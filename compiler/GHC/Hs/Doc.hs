-- | Types and functions for raw and lexed docstrings.
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module GHC.Hs.Doc
  ( HsDoc(..)
  , emptyHsDoc
  , appendHsDoc
  , concatHsDoc
  , concatHDS
  , hsDocIds
  , LHsDoc
  , ppr_mbDoc
  , HsDocString(..)
  , LHsDocString
  , mkHsDocString
  , mkHsDocStringUtf8ByteString
  , isEmptyDocString
  , unpackHDS
  , hsDocStringToByteString
  , appendHDSAsParagraphs

  , ExtractedTHDocs(..)

  , DocStructureItem(..)
  , DocStructure

  , Docs(..)
  , emptyDocs
  ) where

import GHC.Prelude

import GHC.Utils.Binary
import GHC.Utils.Encoding
import GHC.Types.Name
import GHC.Utils.Outputable as Outputable hiding ((<>))
import GHC.Types.SrcLoc
import qualified GHC.Data.EnumSet as EnumSet
import GHC.Data.EnumSet (EnumSet)
import GHC.Types.Avail
import GHC.Types.Name.Set
import GHC.Unit.Module.Name
import GHC.Driver.Flags

import Control.Applicative (liftA2, (<|>))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C8
import Data.Data
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.ByteString.Internal (ByteString(..))
import Data.List.NonEmpty (NonEmpty(..))
import Foreign
import GHC.ForeignPtr
import GHC.LanguageExtensions.Type
import Data.Semigroup
import qualified GHC.Utils.Outputable as O
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import Language.Haskell.Syntax.Extension
import GHC.Hs.Extension

-- | A docstring with the (probable) identifiers found in it.
data HsDoc pass = HsDoc
  { hsDocStrings     :: ![HsDocString] -- List to support concatenating multiple docstrings
  , hsDocIdentifiers :: ![Located (IdP pass)]
  }

deriving instance (Data pass, Data (IdP pass)) => Data (HsDoc pass)
deriving instance (Eq (IdP pass)) => Eq (HsDoc pass)

-- | For compatibility with the existing @-ddump-parsed' output, we only show
-- the docstring.
--
-- Use 'pprHsDoc' to show `HsDoc`'s internals.

-- TODO: It would be nice if we could use 'pprHsDoc' for this instance.
instance Outputable (HsDoc a) where
  ppr (HsDoc s _ids) = ppr s

instance Binary (HsDoc GhcRn) where
  put_ bh (HsDoc s ids) = do
    put_ bh s
    put_ bh ids
  get bh =
    liftA2 HsDoc (get bh) (get bh)

emptyHsDoc :: HsDoc a
emptyHsDoc = HsDoc [] []

-- | Non-empty docstrings are joined with two newlines in between,
-- so haddock will treat two joined docstrings as separate paragraphs.
appendHsDoc :: HsDoc a -> HsDoc a -> HsDoc a
appendHsDoc (HsDoc s_x ids_x) (HsDoc s_y ids_y) =
    HsDoc (s_x   ++ s_y)
          (ids_x ++ ids_y)

-- | Concatenate several 'HsDoc's with 'appendHsDoc'.
--
-- Returns 'Nothing' if all inputs are empty.
concatHsDoc :: [HsDoc pass] -> HsDoc pass
concatHsDoc = foldr appendHsDoc emptyHsDoc

-- | Extract a mapping from the lexed identifiers to the names they may
-- correspond to.
hsDocIds :: HsDoc GhcRn -> NameSet
hsDocIds (HsDoc _ ids) = mkNameSet $ map unLoc ids

pprHsDoc :: Outputable (IdP name) => HsDoc name -> SDoc
pprHsDoc (HsDoc s ids) =
    vcat [ text "text:" $$ nest 2 (ppr s)
         , text "identifiers:" $$ nest 2 (vcat (map ppr ids))
         ]

type LHsDoc pass = Located (HsDoc pass)

ppr_mbDoc :: Maybe (LHsDoc a) -> SDoc
ppr_mbDoc (Just doc) = ppr doc
ppr_mbDoc Nothing    = empty

-- | Haskell Documentation String
--
-- Internally this is a UTF8-Encoded 'ByteString'.
newtype HsDocString = HsDocString ByteString
  -- There are at least two plausible Semigroup instances for this type:
  --
  -- 1. Simple string concatenation.
  -- 2. Concatenation as documentation paragraphs with newlines in between.
  --
  -- To avoid confusion, we pass on defining an instance at all.
  deriving (Eq, Ord, Show, Data)

instance Binary HsDocString where
  put_ bh (HsDocString bs) = put_ bh bs
  get bh = HsDocString <$> get bh

instance Outputable HsDocString where
  ppr = doubleQuotes . text . unpackHDS

isEmptyDocString :: HsDocString -> Bool
isEmptyDocString (HsDocString bs) = BS.null bs

mkHsDocString :: String -> HsDocString
mkHsDocString s = HsDocString (utf8EncodeString s)

-- | Create a 'HsDocString' from a UTF8-encoded 'ByteString'.
mkHsDocStringUtf8ByteString :: ByteString -> HsDocString
mkHsDocStringUtf8ByteString = HsDocString

unpackHDS :: HsDocString -> String
unpackHDS = utf8DecodeByteString . hsDocStringToByteString

-- | Return the contents of a 'HsDocString' as a UTF8-encoded 'ByteString'.
hsDocStringToByteString :: HsDocString -> ByteString
hsDocStringToByteString (HsDocString bs) = bs

nullHDS :: HsDocString -> Bool
nullHDS (HsDocString bs) = BS.null bs

lengthHDS :: HsDocString -> Int
lengthHDS (HsDocString (PS fptr off len)) =
  unsafeDupablePerformIO $
    countUTF8CharsBS (plusPtr (unsafeForeignPtrToPtr fptr) off) len

concatHDS :: [HsDocString] -> HsDocString
concatHDS = HsDocString . BS.concat . map hsDocStringToByteString

-- | Non-empty docstrings are joined with two newlines in between,
-- so haddock will treat two joined docstrings as separate paragraphs.
appendHDSAsParagraphs :: HsDocString -> HsDocString -> HsDocString
appendHDSAsParagraphs a b
  | nullHDS a = b
  | nullHDS b = a
  | otherwise = concatHDS [a, HsDocString (C8.pack "\n\n"), b]

type LHsDocString = Located HsDocString

-- | A simplified version of 'HsImpExp.IE'.
data DocStructureItem
  = DsiSectionHeading Int (HsDoc GhcRn)
  | DsiDocChunk (HsDoc GhcRn)
  | DsiNamedChunkRef String
  | DsiExports Avails
  | DsiModExport
      (NonEmpty ModuleName) -- ^ We might re-export avails from multiple
                            -- modules with a single export declaration. E.g.
                            -- when we have
                            --
                            -- > module M (module X) where
                            -- > import R0 as X
                            -- > import R1 as X
      Avails

instance Binary DocStructureItem where
  put_ bh = \case
    DsiSectionHeading level doc -> do
      putByte bh 0
      put_ bh level
      put_ bh doc
    DsiDocChunk doc -> do
      putByte bh 1
      put_ bh doc
    DsiNamedChunkRef name -> do
      putByte bh 2
      put_ bh name
    DsiExports avails -> do
      putByte bh 3
      put_ bh avails
    DsiModExport mod_names avails -> do
      putByte bh 4
      put_ bh mod_names
      put_ bh avails

  get bh = do
    tag <- getByte bh
    case tag of
      0 -> DsiSectionHeading <$> get bh <*> get bh
      1 -> DsiDocChunk <$> get bh
      2 -> DsiNamedChunkRef <$> get bh
      3 -> DsiExports <$> get bh
      4 -> DsiModExport <$> get bh <*> get bh
      _ -> fail "instance Binary DocStructureItem: Invalid tag"

instance Outputable DocStructureItem where
  ppr = \case
    DsiSectionHeading level doc -> vcat
      [ text "section heading, level" <+> ppr level O.<> colon
      , nest 2 (pprHsDoc doc)
      ]
    DsiDocChunk doc -> vcat
      [ text "documentation chunk:"
      , nest 2 (pprHsDoc doc)
      ]
    DsiNamedChunkRef name ->
      text "reference to named chunk:" <+> text name
    DsiExports avails ->
      text "avails:" $$ nest 2 (ppr avails)
    DsiModExport mod_names avails ->
      text "re-exported module(s):" <+> ppr mod_names $$ nest 2 (ppr avails)

type DocStructure = [DocStructureItem]

-- TODO: Maybe combine the various @(Map Name X)@s to a single map.
data Docs = Docs
  { docs_mod_hdr      :: Maybe (HsDoc GhcRn)
    -- ^ Module header.
  , docs_decls        :: Map Name (HsDoc GhcRn)
    -- ^ Docs for declarations: functions, data types, instances, methods etc.
  , docs_args         :: Map Name (IntMap (HsDoc GhcRn))
    -- ^ Docs for arguments. E.g. function arguments, method arguments.
  , docs_structure    :: DocStructure
  , docs_named_chunks :: Map String (HsDoc GhcRn)
    -- ^ Map from chunk name to content.
    --
    -- This map will be empty unless we have an explicit export list from which
    -- we can reference the chunks.
  , docs_haddock_opts :: Maybe String
    -- ^ Haddock options from @OPTIONS_HADDOCK@ or from @-haddock-opts@.
  , docs_language     :: Maybe Language
    -- ^ The 'Language' used in the module, for example 'Haskell2010'.
  , docs_extensions   :: EnumSet Extension
    -- ^ The full set of language extensions used in the module.
  }

-- | Left biased
instance Semigroup Docs where
  Docs hdr1 decls1 args1 str1 chnk1 opts1 lang1 ext1
   <> Docs hdr2 decls2 args2 str2 chnk2 opts2 lang2 ext2
   = Docs (hdr1 <|> hdr2) (Map.union decls1 decls2) (Map.unionWith IntMap.union args1 args2)
          (str1 <> str2) (Map.union chnk1 chnk2) opts (lang1 <|> lang2) (ext1 <> ext2)
     where
       opts = case (opts1, opts2) of
         (Nothing, Nothing) -> Nothing
         (Just x, Nothing) -> Just x
         (Nothing, Just y) -> Just y
         (Just x, Just y) -> Just $ x <> " " <> y

instance Binary Docs where
  put_ bh docs = do
    put_ bh (docs_mod_hdr docs)
    put_ bh (docs_decls docs)
    put_ bh (docs_args docs)
    put_ bh (docs_structure docs)
    put_ bh (docs_named_chunks docs)
    put_ bh (docs_haddock_opts docs)
    put_ bh (docs_language docs)
    put_ bh (docs_extensions docs)
  get bh = do
    mod_hdr <- get bh
    decls <- get bh
    args <- get bh
    structure <- get bh
    named_chunks <- get bh
    haddock_opts <- get bh
    language <- get bh
    exts <- get bh
    pure Docs { docs_mod_hdr = mod_hdr
              , docs_decls =  decls
              , docs_args = args
              , docs_structure = structure
              , docs_named_chunks = named_chunks
              , docs_haddock_opts = haddock_opts
              , docs_language = language
              , docs_extensions = exts
              }

instance Outputable Docs where
  ppr docs =
      vcat
        [ pprField (pprMaybe pprHsDoc) "module header" docs_mod_hdr
        , pprField (pprMap ppr pprHsDoc) "declaration docs" docs_decls
        , pprField (pprMap ppr (pprIntMap ppr pprHsDoc)) "arg docs" docs_args
        , pprField (vcat . map ppr) "documentation structure" docs_structure
        , pprField (pprMap (doubleQuotes . text) pprHsDoc) "named chunks"
                   docs_named_chunks
        , pprField pprMbString "haddock options" docs_haddock_opts
        , pprField ppr "language" docs_language
        , pprField (vcat . map ppr . EnumSet.toList) "language extensions"
                   docs_extensions
        ]
    where
      pprField :: (a -> SDoc) -> String -> (Docs -> a) -> SDoc
      pprField ppr' heading lbl =
        text heading O.<> colon $$ nest 2 (ppr' (lbl docs))
      pprMap pprKey pprVal m =
        vcat $ flip map (Map.toList m) $ \(k, v) ->
          pprKey k O.<> colon $$ nest 2 (pprVal v)
      pprIntMap pprKey pprVal m =
        vcat $ flip map (IntMap.toList m) $ \(k, v) ->
          pprKey k O.<> colon $$ nest 2 (pprVal v)
      pprMbString Nothing = empty
      pprMbString (Just s) = text s
      pprMaybe ppr' = \case
        Nothing -> text "Nothing"
        Just x -> text "Just" <+> ppr' x

emptyDocs :: Docs
emptyDocs = Docs
  { docs_mod_hdr = Nothing
  , docs_decls = Map.empty
  , docs_args = Map.empty
  , docs_structure = []
  , docs_named_chunks = Map.empty
  , docs_haddock_opts = Nothing
  , docs_language = Nothing
  , docs_extensions = EnumSet.empty
  }

-- | Maps of docs that were added via Template Haskell's @putDoc@.
newtype ExtractedTHDocs = ExtractedTHDocs { getExtractedTHDocs :: Docs }
