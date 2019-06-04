{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GHCForeignImportPrim #-}

{- Test 64bit comparisons.
   We simply compare a number of values in different ways
   and print the results. 32bit and 64bit platforms use
   different code paths so if either one breaks this test
   should catch it.

-}

module Main where

import GHC.Types
import GHC.Exts
import GHC.Word
import GHC.Int
import Data.Bits
import Control.Monad
import Unsafe.Coerce


data I64 = I64 Int64#
data W64 = W64 Word64#

foreign import prim "test_lt" lt_s :: Int64# -> Int64# -> Int#
foreign import prim "test_gt" gt_s :: Int64# -> Int64# -> Int#
foreign import prim "test_le" le_s :: Int64# -> Int64# -> Int#
foreign import prim "test_ge" ge_s :: Int64# -> Int64# -> Int#

foreign import prim "test_eq" eq_s :: Int64# -> Int64# -> Int#
foreign import prim "test_ne" ne_s :: Int64# -> Int64# -> Int#

foreign import prim "test_ltu" lt_u :: Word64# -> Word64# -> Int#
foreign import prim "test_gtu" gt_u :: Word64# -> Word64# -> Int#
foreign import prim "test_leu" le_u :: Word64# -> Word64# -> Int#
foreign import prim "test_geu" ge_u :: Word64# -> Word64# -> Int#

wordValues :: [Word64]
wordValues = do
    lowerBits <- interestingValues
    higherBits <- interestingValues
    return $ (fromIntegral higherBits `shiftL` 32) .|. fromIntegral lowerBits

interestingValues :: [Word32]
interestingValues =
    [ 0x00000000
    , 0x00000001
    , 0x00000002

    , 0x7FFFFFFD
    , 0x7FFFFFFE
    , 0x7FFFFFFF

    , 0xFFFFFFFE
    , 0xFFFFFFFD
    , 0xFFFFFFFF

    , 0x80000000
    , 0x80000001
    , 0x80000002
    ]

intValues :: [Int64]
intValues = map fromIntegral wordValues

intOps :: [(Int64# -> Int64# -> Int#, String)]
intOps = [(lt_s, "lt_s")
         ,(gt_s, "gt_s")
         ,(le_s, "le_s")
         ,(ge_s, "ge_s")

         ,(eq_s, "eq_s")
         ,(ne_s, "ne_s")]

testInt :: Int64 -> Int64 -> (Int64# -> Int64# -> Int#) -> String -> IO ()
testInt x y op op_name = do
    (I64 w1,I64 w2) <- getInts x y
    let !res = I# (op w1 w2)
    putStrLn $ "(" ++ (show x) ++ " `" ++ op_name ++ "` " ++ show y ++ ") = " ++ show res
    return ()

testInts = do
    let tests = do
            (op,op_desc) <- intOps
            x <- intValues
            y <- intValues
            return $ testInt x y op op_desc
    sequence tests

wordOps :: [(Word64# -> Word64# -> Int#, String)]
wordOps = [(lt_u, "lt_u")
          ,(gt_u, "gt_u")
          ,(le_u, "le_u")
          ,(ge_u, "ge_u")]

testWord x y op op_name = do
    (W64 w1,W64 w2) <- getWords x y
    let !res = I# (op w1 w2)
    putStrLn $ "(" ++ (show x) ++ " `" ++ op_name ++ "` " ++ show y ++ ") = " ++ show res

testWords = do
    let tests = do
            (op,op_desc) <- wordOps
            x <- wordValues
            y <- wordValues
            return $ testWord x y op op_desc
    sequence tests

main = do
    testInts
    testWords

    print "done"
    print wordValues
    print intValues
    return ()


-- We want to get a I64#/W64# both and 64 and 32bit platforms.
-- We unsafeCoerce on 64bit, on 32bit the unboxed argument already
-- has the right type.

getInts :: Int64 -> Int64 -> IO ( I64, I64 )
getInts (I64# a1) (I64# a2) = return (I64 a1, I64 a2)


getWords :: Word64 -> Word64 -> IO ( W64, W64 )
getWords (W64# a1) (W64# a2) = return (W64 a1, W64 a2)
