{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Main where

import Variables.State
import StatDbCli

main :: IO ()
main = runVars cli
