{-# OPTIONS -fglasgow-exts #-}

-- !!! Test top-level unboxed types

module ShouldFail where

import PrelGHC

y :: Int#
y = x +# 1#

main =  let 
	  z = x -# y
	in
	if z ># 3# then putStrLn "Yes"
		   else putStrLn "No"

