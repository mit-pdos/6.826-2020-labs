module BadBlockDisk.Env
  (
    Proc
  , Env
  , diskHandle
  , badBlock
  , requests
  , responses
  , newEnv
  , runBS
  , (>>=)
  , return
  ) where

import Control.Concurrent.MVar (MVar, newEmptyMVar)
import Control.Monad.Reader (ReaderT, runReaderT)
import NbdAPI
import System.Posix.IO
import System.Posix.Types

data Env =
  Env { diskHandle :: Fd
      , badBlock :: Integer
      , requests :: MVar Request
      , responses :: MVar Response }

type Proc = ReaderT Env IO

newEnv :: FilePath -> Integer -> IO Env
newEnv fn badBlockArg = pure Env
  <*> openFile fn
  <*> return badBlockArg
  <*> newEmptyMVar <*> newEmptyMVar
  where openFile :: FilePath -> IO Fd
        openFile path = openFd path ReadWrite Nothing defaultFileFlags

runBS :: Env -> Proc a -> IO a
runBS e m = runReaderT m e
