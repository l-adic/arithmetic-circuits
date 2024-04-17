module Test.Circuit.R1CS where

import Circuit (collectCircuitVars)
import Circuit.Solver
import Protolude
import R1CS
import Test.Circuit.Arithmetic

prop_r1csSolver :: ArithCircuitWithInput Fr -> Bool
prop_r1csSolver (ArithCircuitWithInput program inputs) =
  let vars = collectCircuitVars program
      solution = solve inputs vars program
   in isValidWitness (Witness solution) (toR1CS vars program)
