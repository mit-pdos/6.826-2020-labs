module Network.ServerOps where

import NbdAPI
import Control.Monad.Reader (reader, liftIO)
import Control.Concurrent.MVar (takeMVar, putMVar)
import Replication.TwoDiskEnvironment
import Abstraction

init :: Proc InitResult
init = do
  return Initialized

getRequestFromQueue :: Proc Request
getRequestFromQueue = do
  m <- reader requests
  liftIO $ takeMVar m

sendResponseOnQueue :: Response -> Proc ()
sendResponseOnQueue r = do
  m <- reader responses
  liftIO $ putMVar m r

recover :: Proc ()
recover = do
  return ()
