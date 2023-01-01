module Main where

import Control.Monad
import RE

-- int_of_positive :: Positive -> Int
-- int_of_positive XH = 1
-- int_of_positive (XO p) = 2 * int_of_positive p
-- int_of_positive (XI p) = 2 * int_of_positive p + 1

-- int_of_Z :: Z -> Int
-- int_of_Z Z0 = 0
-- int_of_Z (Zpos p) = int_of_positive p
-- int_of_Z (Zneg p) = - int_of_positive p

-- list_of_colist :: Colist a -> [a]
-- list_of_colist Conil = []
-- list_of_colist (Cocons a l) = a : list_of_colist l

-- instance Show Z where
--   show = show . int_of_Z

test :: [Bool] -> IO ()
test bs = putStrLn $ show (Prelude.map (\b -> if b then 1 else 0) bs)
          ++ ": " ++ show (matches bs)

main :: IO ()
main = do
  test []
  test [False]
  test [True]
  test [False, False]
  test [False, True]
  test [True, False]
  test [True, True]
  test [False, False, False]
  test [False, False, True]
  test [False, True, False]
  test [False, True, True]
  test [True, False, False]
  test [True, False, True]
  test [True, True, False]
  test [True, True, True]
  test [False, False, False, False]
  test [False, False, False, True]
  test [False, False, True, False]
  test [False, False, True, True]
  test [False, True, False, False]
  test [False, True, False, True]
  test [False, True, True, False]
  test [False, True, True, True]
  test [True, False, False, False]
  test [True, False, False, True]
  test [True, False, True, False]
  test [True, False, True, True]
  test [True, True, False, False]
  test [True, True, False, True]
  test [True, True, True, False]
  test [True, True, True, True]
