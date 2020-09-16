{-# LANGUAGE PackageImports #-}
module BadBlockDisk.Ops where

import                   Control.Monad.Reader (reader, liftIO)
import qualified         Data.ByteString as BS
import qualified         Data.Char
import                   BadBlockDisk.Env
import                   Disk
import                   System.IO (SeekMode(..))
import "unix-bytestring" System.Posix.IO.ByteString
import                   Utils.Conversion
import                   Abstraction

init :: Proc InitResult
init = return Initialized

read :: Coq_addr -> Proc BS.ByteString
read a = do
  fd <- reader diskHandle
  bs <- reader badBlock
  if a == bs then
    return $ BS.replicate blocksize $ fromIntegral $ Data.Char.ord 'A'
  else
    liftIO $ fdPread fd blocksize (fromIntegral $ addrToOffset a)

write :: Coq_addr -> BS.ByteString -> Proc ()
write a b = do
  fd <- reader diskHandle
  _ <- liftIO $ fdPwrite fd b (fromIntegral $ addrToOffset a)
  return ()

-- |implementation of bad disk DiskSize operation - note that this size is
-- reported to Coq in blocks
size :: Proc Integer
size = do
  fd <- reader diskHandle
  off <- liftIO $ fdSeek fd SeekFromEnd 0
  return (fromIntegral off `div` blocksize)

getBadBlock :: Proc Integer
getBadBlock = reader badBlock

recover :: Proc ()
recover = return ()
