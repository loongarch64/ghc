{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module GHC.Parser.HaddockLex (lexLHsDoc) where

import GHC.Prelude

import GHC.Data.FastString
import GHC.Hs.Doc
import GHC.Parser.Lexer
import GHC.Parser.Annotation
import GHC.Types.SrcLoc
import GHC.Data.StringBuffer
import GHC.Types.Name.Reader
import GHC.Utils.Outputable
import GHC.Utils.Error
import GHC.Utils.Encoding
import GHC.Hs.Extension

import qualified GHC.Data.EnumSet as EnumSet

import Data.Maybe
import Data.Word

import Data.ByteString ( ByteString )
import qualified Data.ByteString as BS

import qualified GHC.LanguageExtensions as LangExt
}

-- The character sets marked "TODO" are mostly overly inclusive
-- and should be defined more precisely once alex has better
-- support for unicode character sets (see
-- https://github.com/simonmar/alex/issues/126).
$special   = [\(\)\,\;\[\]\{\}\`]
$asciisymbol = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~\:]
$asciidigit = 0-9
$digit = $asciidigit                             -- TODO
$asciilower = [a-z \_]
$asciiupper = A-Z
$asciialpha = [$asciilower $asciiupper]
$interesting = $printable # [$white $special]
$alpha = $interesting # [$digit $asciisymbol \'] -- TODO
$upper = $alpha # $asciilower                    -- TODO
$symbol = $interesting # [$digit $asciialpha \'] -- TODO
$idchar = [$alpha $digit \']

@id = $alpha $idchar* \#* | $symbol+
@modname = $upper $idchar*
@qualid = (@modname \.)* @id

:-
  \' @qualid \' | \` @qualid \` { getIdentifier 1 }
  \'\` @qualid \`\' | \'\( @qualid \)\' | \`\( @qualid \)\` { getIdentifier 2 }
  [. \n] ;

{
data AlexInput = AlexInput
  { alexInput_position     :: !RealSrcLoc
  , alexInput_string       :: !ByteString
  }

-- NB: As long as we don't use a left-context we don't need to track the
-- previous input character.
alexInputPrevChar :: AlexInput -> Word8
alexInputPrevChar = error "Left-context not supported"

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (AlexInput p s) = case utf8UnconsByteString s of
  Nothing -> Nothing
  Just (c,bs) -> Just (adjustChar c, AlexInput (advanceSrcLoc p c) bs)

alexScanTokens :: RealSrcLoc -> ByteString -> [(RealSrcSpan, ByteString)]
alexScanTokens start str0 = go (AlexInput start str0)
  where go inp@(AlexInput pos str) =
          case alexScan inp 0 of
            AlexSkip  inp' _ln          -> go inp'
            AlexToken inp'@(AlexInput _ str') _ act -> act pos (BS.length str - BS.length str') str : go inp'
            AlexEOF                     -> []
            AlexError (AlexInput p _) -> error $ "lexical error at " ++ show p

--------------------------------------------------------------------------------

-- | Extract identifier from Alex state.
getIdentifier :: Int -- ^ adornment length
              -> RealSrcLoc
              -> Int
                 -- ^ Token length
              -> ByteString
                 -- ^ The remaining input beginning with the found token
              -> (RealSrcSpan, ByteString)
getIdentifier !i !loc0 !len0 !s0 =
    (mkRealSrcSpan loc1 loc2, ident)
  where
    (adornment, s1) = BS.splitAt i s0
    ident = BS.take (len0 - 2*i) s1 
    loc1 = advanceSrcLocBS loc0 adornment
    loc2 = advanceSrcLocBS loc1 ident

advanceSrcLocBS :: RealSrcLoc -> ByteString -> RealSrcLoc
advanceSrcLocBS !loc bs = case utf8UnconsByteString bs of
  Nothing -> loc
  Just (c, bs') -> advanceSrcLocBS (advanceSrcLoc loc c) bs' 

-- | Lex identifiers from a docstring.
lexLHsDoc :: P (LocatedN RdrName)      -- ^ A precise identifier parser
         -> LHsDocString -- ^ A docstring
         -> LHsDoc GhcPs
lexLHsDoc identParser (L l doc@(HsDocString s)) =
    L l (HsDoc [doc] (mapMaybe maybeDocIdentifier plausibleIdents))
  where
    maybeDocIdentifier :: (RealSrcSpan, ByteString) -> Maybe (Located RdrName)
    maybeDocIdentifier = uncurry (validateIdentWith identParser)

    plausibleIdents :: [(RealSrcSpan,ByteString)]
    plausibleIdents = alexScanTokens (realSrcSpanStart rl) s

    rl = case l of
      RealSrcSpan s _ -> s
      UnhelpfulSpan _ -> realSrcLocSpan $ mkRealSrcLoc (mkFastString "") 0 0

validateIdentWith :: P (LocatedN RdrName) -> RealSrcSpan -> ByteString -> Maybe (Located RdrName)
validateIdentWith identParser loc str0 =
  let -- These ParserFlags should be as "inclusive" as possible, allowing
      -- identifiers defined with any language extension.
      pflags = mkParserOpts
                 (EnumSet.fromList [LangExt.MagicHash])
                 dopts
                 []
                 False False False False
      dopts = DiagOpts
        { diag_warning_flags = EnumSet.empty
          , diag_fatal_warning_flags = EnumSet.empty
          , diag_warn_is_error = False
          , diag_reverse_errors = False
          , diag_max_errors = Nothing
          , diag_ppr_ctx = defaultSDocContext
        }
      buffer = stringBufferFromByteString str0
      realSrcLc = realSrcSpanStart loc
      pstate = initParserState pflags buffer realSrcLc
  in case unP identParser pstate of
    POk _ name -> Just $ reLoc name
    _ -> Nothing
}
