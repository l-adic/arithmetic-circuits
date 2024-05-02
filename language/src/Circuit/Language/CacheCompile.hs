{-# LANGUAGE TypeFamilies #-}

module Circuit.Language.CacheCompile where

import Circuit (Wire)
import Data.Array
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Hashable
import Data.Vector (Vector)
import GHC.IO (unsafeDupablePerformIO, unsafePerformIO)
import Protolude

-- tuning parameter
defaultCacheWidth :: Int
defaultCacheWidth = 1024

data CacheState t = CacheState
  { compileOutput :: !(HashMap (Description t) (Vector Wire))
  }

newtype Cache t = Cache {getCache :: Array Int (MVar (CacheState t))}

mkCache :: (Interned t) => Cache t
mkCache = result
  where
    element = CacheState HashMap.empty
    w = cacheWidth result
    result =
      Cache $
        unsafePerformIO $
          traverse newMVar $
            listArray (0, w - 1) $
              replicate w element

type Id = Int

class
  ( Eq (Description t),
    Hashable (Description t)
  ) =>
  Interned t
  where
  data Description t
  type Uninterned t
  describe :: Uninterned t -> Description t
  identify :: Id -> Uninterned t -> t

  cacheWidth :: p t -> Int
  cacheWidth _ = defaultCacheWidth
  cache :: Cache t

class (Interned t) => Uninternable t where
  unintern :: t -> Uninterned t

intern :: forall t. (Interned t) => Uninterned t -> (t -> IO (Vector Wire)) -> t
intern !bt compile = unsafeDupablePerformIO $ modifyMVar slot go
  where
    slot = getCache cache ! r
    !dt = describe @t bt
    !hdt = hash dt
    !wid = cacheWidth dt
    r = hdt `mod` wid
    go st@(CacheState {compileOutput}) = case HashMap.lookup dt compileOutput of
      Nothing -> do
        let t = identify hdt bt
        wires <- compile t
        pure
          ( CacheState
              { compileOutput = HashMap.insert dt wires compileOutput
              },
            t
          )
      Just _ ->
        let t = identify hdt bt
         in pure (st, t)

-- given a description, go hunting for an entry in the cache
recover :: (Interned t) => Description t -> IO (Maybe (Vector Wire))
recover !dt = do
  CacheState {compileOutput} <- readMVar $ getCache cache ! (hash dt `mod` cacheWidth dt)
  return $ HashMap.lookup dt compileOutput
