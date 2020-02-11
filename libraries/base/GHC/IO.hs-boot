{-# LANGUAGE Unsafe #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GHC.IO where

import GHC.Types
import GHC.Num.Integer () -- See Note [Depend on GHC.Num.Integer] in GHC.Base
import {-# SOURCE #-} GHC.Exception.Type (SomeException)

mplusIO :: IO a -> IO a -> IO a
mkUserError :: [Char] -> SomeException
