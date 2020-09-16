{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad (when)
import Data.Semigroup ((<>))
import Network.NBD (runServer, initServer, ServerOptions (..))
import Options.Applicative
import System.Directory
import System.IO

data InitOptions = InitOptions
  { defaultSizeKB :: Int
  , initDiskPath :: FilePath
  , initBadBlock :: Integer }

data Options = Start ServerOptions
             | Init InitOptions

parseDiskPath :: Parser FilePath
parseDiskPath = argument str (metavar "FILE0") <|> pure "disk.img"

parseBadBlock :: Parser Integer
parseBadBlock = argument auto (metavar "BADBLOCK") <|> pure 1

serverOptions :: Parser ServerOptions
serverOptions = do
  diskPath <- parseDiskPath
  diskBadBlock <- parseBadBlock
  logCommands <- switch (long "debug"
                        <> short 'd'
                        <> help "log each operation received")
  pure ServerOptions {..}

initOptions :: Parser InitOptions
initOptions = do
  defaultSizeKB <- option auto
    ( long "size"
      <> help "size to initialize disk files to if they do not exist"
      <> showDefault
      <> value (100*1024)
      <> metavar "KB" )
  initDiskPath <- parseDiskPath
  initBadBlock <- parseBadBlock
  pure InitOptions {..}

diskDefaultMessage :: String
diskDefaultMessage = "disk defaults to disk0.img"

options :: Parser Options
options = hsubparser
          ( command "start" (info (Start <$> serverOptions)
                             (progDesc "start server"
                             <> footer diskDefaultMessage))
            <> command "init" (info (Init <$> initOptions)
                               (progDesc "initialize disk"
                               <> footer diskDefaultMessage))
          )

main :: IO ()
main = execParser opts >>= run
  where
    opts = info (options <**> helper)
      (fullDesc
       <> progDesc "an nbd server that remaps a bad block; COMMAND is either init or start"
       <> header "remap-nbd - remapping network block device"
       )

run :: Options -> IO ()
run (Start opts) = runServer opts
run (Init opts) = runInit opts

runInit :: InitOptions -> IO ()
runInit InitOptions
  { defaultSizeKB=size,
    initDiskPath=fn,
    initBadBlock=bs } = do
  exists <- doesFileExist fn
  when (not exists) $
    withFile fn WriteMode $ \h ->
      hSetFileSize h (fromIntegral $ size * 1024)
  initServer fn bs
