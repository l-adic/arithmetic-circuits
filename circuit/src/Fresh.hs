module Fresh
  ( fresh,
    evalFresh,
    Fresh,
    FreshT,
  )
where

import Protolude

type FreshT m a = StateT Int m a

type Fresh a = FreshT Identity a

evalFresh :: Fresh a -> a
evalFresh act = runIdentity $ evalStateT act 1

fresh :: Fresh Int
fresh = do
  v <- get
  modify (+ 1)
  pure v
