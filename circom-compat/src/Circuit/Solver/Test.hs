{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Circuit.Solver.Test where

{-
import Circuit (ArithCircuit, CircuitVars)
import Circuit.Solver.Circom
import Data.Field.Galois (Prime)
import Data.Propagator (Propagated, PropagatedNum)
import GHC.TypeLits (KnownNat)
import Protolude

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

instance (KnownNat p) => Propagated (Prime p)

instance (KnownNat p) => PropagatedNum (Prime p)

myProgramState :: CircuitVars f
myProgramState = undefined

myProgramEnv :: ArithCircuit f
myProgramEnv = undefined

\$(mkProgram 'myProgramEnv 'myProgramState ''Fr)
-}