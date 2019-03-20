module GHC.Rename.Doc ( rnHsDoc, rnLHsDoc, rnLDocDecl, rnDocDecl ) where

import GHC.Prelude

import GHC.Tc.Types
import GHC.Hs
import GHC.Types.Name.Reader
import GHC.Types.Name
import GHC.Tc.Utils.Monad (getGblEnv)
import GHC.Types.Avail
import GHC.Rename.Env
import GHC.Utils.Outputable (ppr)
import GHC.Utils.Panic (pprPanic)

rnLHsDoc :: LHsDoc RdrName -> RnM (LHsDoc Name)
rnLHsDoc = traverse rnHsDoc

rnLDocDecl :: LDocDecl GhcPs -> RnM (LDocDecl GhcRn)
rnLDocDecl = traverse rnDocDecl

rnDocDecl :: DocDecl GhcPs -> RnM (DocDecl GhcRn)
rnDocDecl (DocCommentNext doc) = do
  doc' <- rnHsDoc doc
  pure $ (DocCommentNext doc')
rnDocDecl (DocCommentPrev doc) = do
  doc' <- rnHsDoc doc
  pure $ (DocCommentPrev doc')
rnDocDecl (DocCommentNamed n doc) = do
  doc' <- rnHsDoc doc
  pure $ (DocCommentNamed n doc')
rnDocDecl (DocGroup i doc) = do
  doc' <- rnHsDoc doc
  pure $ (DocGroup i doc')

rnHsDoc :: HsDoc RdrName -> RnM (HsDoc Name)
rnHsDoc (HsDoc s ids) = do
  gre <- tcg_rdr_env <$> getGblEnv
  pure (HsDoc s (rnHsDocIdentifier gre <$> ids))

rnHsDocIdentifier :: GlobalRdrEnv
                  -> HsDocIdentifier RdrName
                  -> HsDocIdentifier Name
rnHsDocIdentifier gre (HsDocIdentifier span [rdr_name]) =
  HsDocIdentifier span names
  where
    -- Try to look up all the names in the GlobalRdrEnv that match
    -- the names.
    names = concatMap (\c -> map (greNamePrintableName . gre_name) (lookupGRE_RdrName c gre)) choices
    -- Generate the choices for the possible kind of thing this
    -- is.
    choices = dataTcOccs rdr_name
rnHsDocIdentifier _ hsDocId =
  pprPanic "rnHsDocIdentifier" (ppr hsDocId)
