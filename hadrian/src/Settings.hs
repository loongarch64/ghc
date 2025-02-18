{-# LANGUAGE TupleSections #-}

module Settings (
    getArgs, getLibraryWays, getRtsWays, flavour, knownPackages,
    findPackageByName, unsafeFindPackageByName, unsafeFindPackageByPath,
    isLibrary, stagePackages, getBignumBackend, getBignumCheck, completeSetting
    ) where

import CommandLine
import Expression
import Flavour
import Packages
import Settings.Parser
import UserSettings (userFlavours, userPackages, userDefaultFlavour)

import {-# SOURCE #-} Settings.Default
import Settings.Flavours.Benchmark
import Settings.Flavours.Development
import Settings.Flavours.GhcInGhci
import Settings.Flavours.Performance
import Settings.Flavours.Quick
import Settings.Flavours.Quickest
import Settings.Flavours.QuickCross
import Settings.Flavours.Validate
import Settings.Flavours.Release


getArgs :: Args
getArgs = expr flavour >>= args

getLibraryWays :: Ways
getLibraryWays = expr flavour >>= libraryWays

getRtsWays :: Ways
getRtsWays = expr flavour >>= rtsWays

getBignumBackend :: Expr String
getBignumBackend = expr $ cmdBignum >>= \case
   Nothing -> bignumBackend <$> flavour
   Just b  -> pure b

getBignumCheck :: Expr Bool
getBignumCheck = expr $ cmdBignum >>= \case
   Nothing -> bignumCheck <$> flavour
   Just _  -> cmdBignumCheck

stagePackages :: Stage -> Action [Package]
stagePackages stage = do
    f <- flavour
    packages f stage

hadrianFlavours :: [Flavour]
hadrianFlavours =
    [ benchmarkFlavour, defaultFlavour, developmentFlavour Stage1
    , developmentFlavour Stage2, performanceFlavour
    , releaseFlavour
    , quickFlavour, quickValidateFlavour, quickDebugFlavour
    , quickestFlavour
    , quickCrossFlavour
    , ghcInGhciFlavour, validateFlavour, slowValidateFlavour
    ]

-- | This action looks up a flavour with the name given on the
--   command line with @--flavour@, defaulting to 'userDefaultFlavour'
--   when no explicit @--flavour@ is passed. It then applies any
--   potential setting update specified on the command line or in a
--   <build root>/hadrian.settings file, using @k = v@ or @k += v@ style
--   syntax. See Note [Hadrian settings] at the bottom of this file.
flavour :: Action Flavour
flavour = do
    flavourName <- fromMaybe userDefaultFlavour <$> cmdFlavour
    kvs <- userSetting ([] :: [KeyVal])
    let flavours = hadrianFlavours ++ userFlavours
        (settingErrs, tweak) = applySettings kvs

    when (not $ null settingErrs) $ fail
      $ "failed to apply key-value settings:" ++ unlines (map (" - " ++) settingErrs)

    case parseFlavour flavours flavourTransformers flavourName of
      Left err -> fail err
      Right f -> return $ tweak f

-- TODO: switch to Set Package as the order of packages should not matter?
-- Otherwise we have to keep remembering to sort packages from time to time.
knownPackages :: [Package]
knownPackages = sort $ ghcPackages ++ userPackages

-- TODO: Speed up? Switch to Set?
-- Note: this is slow but we keep it simple as there are just ~50 packages
findPackageByName :: PackageName -> Maybe Package
findPackageByName name = find (\pkg -> pkgName pkg == name) knownPackages

unsafeFindPackageByName :: PackageName -> Package
unsafeFindPackageByName name = fromMaybe (error msg) $ findPackageByName name
  where
    msg = "unsafeFindPackageByName: No package with name " ++ name

unsafeFindPackageByPath :: FilePath -> Package
unsafeFindPackageByPath path = err $ find (\pkg -> pkgPath pkg == path) knownPackages
  where
    err = fromMaybe $ error ("findPackageByPath: No package for path " ++ path)