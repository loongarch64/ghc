{-# LANGUAGE Haskell2010 #-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, AllowAmbiguousTypes #-}

module Bug where

class C a b where
  op :: a -> b -> ()

-- GHC should not infer
-- foo :: (C a b0, Num b0) => a -> ()
-- but instead let b0 default to Integer:
-- foo :: (C a Integer) => a -> ()
foo x = op x 3
