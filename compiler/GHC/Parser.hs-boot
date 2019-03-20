module GHC.Parser where

import GHC.Prelude
import GHC.Hs.Doc (HsDoc)
import GHC.Types.Name.Reader (RdrName)

lexHsDoc' :: String -> HsDoc RdrName
