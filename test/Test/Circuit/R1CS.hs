module Test.Circuit.R1CS where

import Circuit.Solver
import Protolude
import R1CS
import Test.Circuit.Arithmetic

prop_r1csSolver :: ArithCircuitWithInput Fr -> Bool
prop_r1csSolver (ArithCircuitWithInput program inputs) =
  let solution = solve inputs program
   in isValidWitness (Witness solution) (toR1CS program)
