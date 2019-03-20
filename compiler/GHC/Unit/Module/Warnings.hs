{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Warnings for a module
module GHC.Unit.Module.Warnings
   ( Warnings (..)
   , WarningTxt (..)
   , WarningSort (..)
   , warningTxtContents
   , mkIfaceWarnCache
   , emptyIfaceWarnCache
   , plusWarns
   )
where

import GHC.Prelude

import GHC.Types.SourceText
import GHC.Types.Name.Occurrence
import GHC.Types.SrcLoc

import GHC.Utils.Outputable
import GHC.Utils.Binary
import Control.Monad

import Data.Data

-- | Warning Text
--
-- reason/explanation from a WARNING or DEPRECATED pragma
data WarningTxt text = WarningTxt
  { wt_sort :: !(Located (WithSourceText WarningSort))
  , wt_warning :: ![Located (WithSourceText text)]
  } deriving (Eq, Data, Functor, Foldable, Traversable)

-- | Ignores source locations and 'SourceText's.
instance Binary text => Binary (WarningTxt text) where
  put_ bh w = do
    let (sort_, ws) = warningTxtContents w
    put_ bh sort_
    put_ bh ws
  get bh = do
    sort_ <- get bh
    ws <- get bh
    pure $ WarningTxt (noLoc $ noSourceText sort_)
                      (map (noLoc . noSourceText) ws)

-- Yeah, this is a funny instance.
-- It makes Ppr035, Ppr036 and Ppr046 pass though!
instance Outputable text => Outputable (WarningTxt text) where
  ppr (WarningTxt lsort lws) =
    case wst_st (unLoc lsort) of
      NoSourceText -> pp_ws lws
      SourceText src -> text src <+> pp_ws lws <+> text "#-}"
    where
      pp_ws [l] = ppr $ unLoc l
      pp_ws ws = ppr $ map unLoc ws

warningTxtContents :: WarningTxt text -> (WarningSort, [text])
warningTxtContents (WarningTxt srt ws) =
    (unWithSourceText $ unLoc srt, map (unWithSourceText . unLoc) ws)

data WarningSort
  = WsWarning
  | WsDeprecated
  deriving (Data, Eq, Enum)

instance Binary WarningSort where
  put_ bh = putByte bh . fromIntegral . fromEnum
  get  bh = toEnum . fromIntegral <$!> getByte bh

instance Outputable WarningSort where
  ppr WsWarning = text "Warning"
  ppr WsDeprecated = text "Deprecated"

-- | Warning information for a module
data Warnings text
  = NoWarnings                          -- ^ Nothing deprecated
  | WarnAll (WarningTxt text)                  -- ^ Whole module deprecated
  | WarnSome [(OccName,WarningTxt text)]     -- ^ Some specific things deprecated

     -- Only an OccName is needed because
     --    (1) a deprecation always applies to a binding
     --        defined in the module in which the deprecation appears.
     --    (2) deprecations are only reported outside the defining module.
     --        this is important because, otherwise, if we saw something like
     --
     --        {-# DEPRECATED f "" #-}
     --        f = ...
     --        h = f
     --        g = let f = undefined in f
     --
     --        we'd need more information than an OccName to know to say something
     --        about the use of f in h but not the use of the locally bound f in g
     --
     --        however, because we only report about deprecations from the outside,
     --        and a module can only export one value called f,
     --        an OccName suffices.
     --
     --        this is in contrast with fixity declarations, where we need to map
     --        a Name to its fixity declaration.
  deriving( Eq )

instance Binary a => Binary (Warnings a) where
    put_ bh NoWarnings     = putByte bh 0
    put_ bh (WarnAll t) = do
            putByte bh 1
            put_ bh t
    put_ bh (WarnSome ts) = do
            putByte bh 2
            put_ bh ts

    get bh = do
            h <- getByte bh
            case h of
              0 -> return NoWarnings
              1 -> do aa <- get bh
                      return (WarnAll aa)
              _ -> do aa <- get bh
                      return (WarnSome aa)

instance Outputable text => Outputable (Warnings text) where
  ppr NoWarnings     = empty
  ppr (WarnAll txt)  = text "Warn all:" <+> ppr txt
  ppr (WarnSome prs) = text "Warnings:"
                       <+> nest 2 (vcat (map pprWarning prs))
    where
      pprWarning (name, txt) = ppr name <> colon <+> ppr txt

-- | Constructs the cache for the 'mi_warn_fn' field of a 'ModIface'
mkIfaceWarnCache :: Warnings text -> OccName -> Maybe (WarningTxt text)
mkIfaceWarnCache NoWarnings  = \_ -> Nothing
mkIfaceWarnCache (WarnAll t) = \_ -> Just t
mkIfaceWarnCache (WarnSome pairs) = lookupOccEnv (mkOccEnv pairs)

emptyIfaceWarnCache :: OccName -> Maybe (WarningTxt text)
emptyIfaceWarnCache _ = Nothing

plusWarns :: Warnings a -> Warnings a -> Warnings a
plusWarns d NoWarnings = d
plusWarns NoWarnings d = d
plusWarns _ (WarnAll t) = WarnAll t
plusWarns (WarnAll t) _ = WarnAll t
plusWarns (WarnSome v1) (WarnSome v2) = WarnSome (v1 ++ v2)

