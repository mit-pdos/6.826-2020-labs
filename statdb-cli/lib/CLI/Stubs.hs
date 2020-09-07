module CLI.Stubs (getNewItem, reportMean) where

import Control.Monad.Trans (liftIO)
import Variables.State
import System.IO

getNewItem :: Proc Integer
getNewItem = do
  x <- liftIO $ do
    putStr "Enter a number to add: "
    hFlush stdout
    getLine
  if (read x :: Integer) < 0 then do
    liftIO $ putStrLn "Negative numbers not supported"
    getNewItem
  else
    return $ read x

reportMean :: Maybe Integer -> Proc ()
reportMean m = liftIO $ putStrLn $ "Mean: " ++ show m
