module Variables.Ops where

import Control.Monad.State.Strict (gets, modify)
import Variables.State
import VariablesAPI
import Abstraction

init :: Proc InitResult
init = return Initialized

read :: Coq_var -> Proc Integer
read VarX = gets varX
read VarY = gets varY
read VarZ = gets varZ

write :: Coq_var -> Integer -> Proc ()
write VarX x = modify (\s -> s { varX = x })
write VarY x = modify (\s -> s { varY = x })
write VarZ x = modify (\s -> s { varZ = x })
