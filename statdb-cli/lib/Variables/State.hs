module Variables.State
  (
    Proc
  , Vars(..)
  , runVars
  , (>>=)
  , return
  ) where

import Control.Monad.State.Strict (StateT, evalStateT)

data Vars =
  Vars { varX :: Integer
       , varY :: Integer
       , varZ :: Integer }

type Proc = StateT Vars IO

-- the Coq model of Variables assumes nothing about the initial values
initialEnv :: Vars
initialEnv = Vars (-1) (-1) (-1)

runVars :: Proc a -> IO a
runVars m = evalStateT m initialEnv
