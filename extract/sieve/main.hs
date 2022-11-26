module Main where

import Control.Monad
import Sieve

int_of_positive :: Positive -> Int
int_of_positive XH = 1
int_of_positive (XO p) = 2 * int_of_positive p
int_of_positive (XI p) = 2 * int_of_positive p + 1

int_of_Z :: Z -> Int
int_of_Z Z0 = 0
int_of_Z (Zpos p) = int_of_positive p
int_of_Z (Zneg p) = - int_of_positive p

list_of_colist :: Colist a -> [a]
list_of_colist Conil = []
list_of_colist (Cocons a l) = a : list_of_colist l

instance Show Z where
  show = show . int_of_Z

main :: IO ()
main = do
  let primes = list_of_colist sieve''
  forM_ primes (\n -> putStrLn (show n))
