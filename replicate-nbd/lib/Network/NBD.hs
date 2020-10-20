{-# LANGUAGE OverloadedStrings, Rank2Types  #-}

module Network.NBD where

import           Conduit
import           Control.Concurrent (forkIO)
import           Control.Concurrent.MVar (newMVar, newEmptyMVar, putMVar, takeMVar)
import           Control.Exception.Base (Exception)
import           Control.Monad (when)
import           Data.Bits
import qualified Data.ByteString as BS
import           Data.Conduit.Cereal
import           Data.Conduit.Network
import           Data.Serialize
import           Abstraction (InitResult(..))
import           NbdAPI
import           Network.NBD.Data
import           Replication.TwoDiskEnvironment
import qualified ReplicatedServer as Server
import           System.Exit (die)
import           Utils.Conversion

-- IANA reserved port 10809
--
-- high-level overview of protocol:
-- on connection:
-- negotiate
--   S: INIT_PASSWD, NEW_MAGIC, NBD_FLAG_FIXED_NEWSTYLE
--   C: flags, should have NBD_FLAG_C_FIXED_NEWSTYLE
--   loop (options)
--     C: NEW_MAGIC, type, length, data (length bytes)
--     until type == NBD_OPT_EXPORT_NAME
--   S: export size, NBD_FLAG_HAS_FLAGS (| read-only | flush), 124 zeroes
-- transmission
--   loop (commands)
--     C: NBD_REQUEST_MAGIC, flags (fua), type, handle, offset, length
--     (for write) C: data (length bytes)
--     S: NBD_REPLY_MAGIC, error, (same) handle
--     (for read) S: data (length bytes)
--
-- see https://sourceforge.net/p/nbd/code/ci/master/tree/doc/proto.md for a
-- detailed protocol description

data ServerOptions = ServerOptions
  { diskPaths :: (FilePath, FilePath)
  , logCommands :: Bool }

type ByteConduit m r = ConduitM BS.ByteString BS.ByteString m r

type ExportName = BS.ByteString

-- get an option, or return an export name
getOption :: MonadThrow m => ByteConduit m (Either ExportName NbdOption)
getOption = do
  magic <- sinkGet getWord64be
  when (magic /= nbd_C_OPT_MAGIC) $
    throwM $ InvalidMagic "client option" magic
  sinkGet $ do
    opt <- toEnum . fromIntegral <$> getWord32be
    len <- fromIntegral <$> getWord32be
    case opt of
      ExportName -> Left <$> getBytes len
      _ -> getBytes len >> return (Right opt)

-- negotiate a set of options with the client
-- options are currently all ignored, so that this process simply returns the
-- export name requested by the client
negotiateNewstyle :: MonadThrow m => ByteConduit m ExportName
negotiateNewstyle = do
  yield newstylePrelude
  clientFlags <- sinkGet getWord32be
  when (clientFlags .&. nbd_FLAG_C_FIXED_NEWSTYLE == 0) $
    throwM $ InvalidClientFlags clientFlags
  handleOptions
  where
    newstylePrelude :: BS.ByteString
    newstylePrelude = runPut $ do
      putWord64be nbd_INIT_PASSWD
      putWord64be nbd_NEW_MAGIC
      putWord16be (0 .|. nbd_FLAG_FIXED_NEWSTYLE)

    handleOptions = do
      opt <- getOption
      case opt of
        Left n -> return n
        Right o -> do
          -- we actually ignore all options
          yield $ runPut $ do
            putWord64be nbd_OPT_REPLY_MAGIC
            putWord32be $ fromIntegral $ fromEnum o
            putWord32be nbd_REP_ERR_UNSUP
            putWord32be 0
          handleOptions

-- start transmission after negotiation by informing the client about the export
sendExportInformation :: Monad m => ByteCount -> ByteConduit m ()
sendExportInformation len = sourcePut $ do
    putWord64be $ fromIntegral len
    putWord16be flags
    putByteString zeroes
  where
    zeroes = BS.replicate 124 0
    flags = nbd_FLAG_HAS_FLAGS .|. nbd_FLAG_SEND_FLUSH

-- parse a command from the client during the transmission phase
getCommand :: (MonadThrow m, MonadIO m) => ByteConduit m Request
getCommand = do
  magic <- sinkGet getWord32be
  when (magic /= nbd_REQUEST_MAGIC) $
    throwM $ InvalidMagic "request" (fromIntegral magic)
  (_, typ, handle, offset, len) <- sinkGet $ label "request header" $ (,,,,) <$>
    getWord16be <*> -- flags (ignored)
    getWord16be <*> -- type
    getWord64be <*> -- handle
    (fromIntegral <$> getWord64be) <*> -- offset
    (fromIntegral <$> getWord32be) -- length
  let command
        | typ == nbd_CMD_READ =
          return $ Read handle (offset `div` blocksize) (len `div` blocksize)
        | typ == nbd_CMD_WRITE = do
            dat <- sinkGet $ getBytes (fromIntegral len)
            return $ Write handle
              (offset `div` blocksize)
              (len `div` blocksize) dat
        | typ == nbd_CMD_FLUSH = return $ NbdAPI.Flush handle
        | typ == nbd_CMD_DISC = return Disconnect
        | otherwise = return $ UnknownOp handle in
    command

-- send an error code reply to the client (data is sent separately afterward,
-- for reads)
sendReply :: Monad m => Handle -> ErrorCode -> ByteConduit m ()
sendReply h err = sourcePut $ do
  putWord32be nbd_REPLY_MAGIC
  putWord32be (errCode err)
  putWord64be h

sendResponse :: MonadIO m => Response -> ByteConduit m ()
sendResponse (Build_Response h e _ dat) = do
  sendReply h e
  sourcePut $ putByteString dat

handleCommands :: (MonadThrow m, MonadIO m) => Bool -> Env -> ByteConduit m ()
handleCommands doLog e = handle
  where
    debug :: (MonadThrow m, MonadIO m) => String -> ByteConduit m ()
    debug = liftIO . when doLog . putStrLn
    handle = do
      cmd <- getCommand
      case cmd of
        Read _ off len -> debug $ "read at " ++ show (off*blocksize) ++ " of length " ++ show (len*blocksize)
        Write _ off len _ -> debug $ "write at " ++ show (off*blocksize) ++ " of length " ++ show (len*blocksize)
        NbdAPI.Flush _ -> debug "flush"
        Disconnect -> debug "disconnect command"
        UnknownOp _ -> debug "unknown command"
      r <- liftIO $ do
        putMVar (requests e) cmd
        takeMVar (responses e)
      sendResponse r
      handle

data SizeMismatchException =
  SizeMismatchException { size0 :: Integer
                        , size1 :: Integer  }
  deriving (Eq, Show)

instance Exception SizeMismatchException

forkNbdServer :: Env -> Bool -> IO ()
forkNbdServer e doLog =
  forkSingleClient $ \ad ->
  -- assemble a conduit using the TCP server as input and output
  runConduit $ appSource ad .| nbdConnection .| appSink ad
  where
    settings = serverSettings 10809 "127.0.0.1"
    forkSingleClient app = do
      -- process a single client; new connections will block on this MVar
      mv <- newMVar ()
      _ <- forkTCPServer settings (\ad -> takeMVar mv >> app ad)
      return ()
    nbdConnection = do
      -- negotiate
      name <- negotiateNewstyle
      liftIO $ when (name /= "") $
        putStrLn $ "ignoring non-default export name " ++ show name
      sz <- liftIO . runTD e $ Server.size
      -- start transmission phase
      sendExportInformation (fromIntegral sz * blocksize)
      liftIO $ putStrLn "negotiated with client"
      -- infinite loop parsing commands and putting them on the queue
      handleCommands doLog e

runServer :: ServerOptions -> IO ()
runServer ServerOptions
  { diskPaths=(fn0, fn1),
    logCommands=doLog} = do
  e <- newEnv fn0 fn1
  putStrLn "serving on localhost:10809"
  mv <- newEmptyMVar
  _ <- liftIO . forkIO $ runTD e Server.serverLoop >> putMVar mv ()
  forkNbdServer e doLog
  takeMVar mv

initServer :: (FilePath, FilePath) -> IO ()
initServer (fn0, fn1) = do
  e <- newEnv fn0 fn1
  r <- runTD e Server.init
  case r of
    Initialized -> return ()
    InitFailed -> die "initialization failed! are disks of different sizes?"
