module Test.Main where

import Prelude hiding (gcd)
import Effect (Effect)
import Data.Sparse.Polynomial(Polynomial, (^), (:.), (?), roots, liftC, diff, gcd)
import Data.Complex(Cartesian, i, magnitudeSquared)
import Data.Ratio(Ratio, (%))
import Data.Foldable(foldr)

foreign import assert :: String -> Boolean -> Effect Unit

pol1 :: Polynomial Int -- 3x^2-2x+5
pol1 = 3 ^ 2 <> (-2) ^ 1 <> 5 ^ 0

pol2 :: Polynomial Number -- 3x^2+5
pol2 = 3.0 ^ 2 <> 5.0 ^ 0

pol3 :: Polynomial Int -- 4x-1
pol3 = (-1) ^ 0 <> 4 ^ 1

pol4 :: Polynomial (Polynomial Int) -- (4x-1)y + 3x^2-2x+5
pol4 = pol3 ^ 1 <> pol1 ^ 0

pol5 :: Polynomial (Cartesian Int) -- x^2 + ix - 1
pol5 = (-one) ^ 0 <> i ^ 1 <> one ^ 2
 
pol6 :: Polynomial (Ratio Int)
pol6 = (-8%3) ^ 0 <> (1%7) ^ 1 <> (2%1) ^ 2

pol7 :: Polynomial (Ratio Int)
pol7 = (-8%3) ^ 2 <> (1%7) ^ 1 <> (2%1) ^ 0

main :: Effect Unit
main = do
  assert "polynomial Int application" $ pol1 :. 2 == 13
  assert "polynomial Number application" $ pol2 :. 2.0 == 17.0
  assert "polynomial Complex application" $ pol5 :. i == ((_ * (-3)) <$> one)
  assert "polynomial Rational application" $ pol6 :. (1%2) == -44%21
  assert "coefficient extraction" $ pol3 ? 1 == 4
  assert "polynomial sum" $ (pol1 + pol3) :. 3 == 37
  assert "polynomial difference" $ (pol1 - pol3) :. 3 == 15
  assert "polynomial product" $ (pol1 * pol3) :. 3 == 286
  assert "polynomial quotient" $ (pol7 / pol6) :. (0%1) == -4%3
  assert "polynomial rest" $ (pol7 `mod` pol6) :. (0%1) == -14%9
  assert "polynomial gcd" $ gcd pol6 pol7 ==  (-1496 % 27)^0
  assert "differentiation" $ diff pol7 == (-16%3) ^ 1 <> (1%7) ^ 0
  assert "polynomial composition" $ ((:.) pol3 <<< (:.) pol1) 3 == 103
  assert "bivariate polynomial" $ ((pol4 <#> (_ :. 3)) # (_ :. 5)) == 81 
  let x = 1 ^ 1 ^ 0 ^ 0
  let y = 1 ^ 0 ^ 1 ^ 0
  let z = 1 ^ 0 ^ 0 ^ 1
  assert "multivariate polynomial" $ 
    ((((y*y*y - x*x*z) <#> ((<$>) (_ :. 3))) <#> (_ :. 5)) # (_ :. 7)) == 62
  assert "root polynomial nullification" $ 
    (foldr (+) 0.0 $ magnitudeSquared <$> 
      (liftC pol2 :. _) <$> roots pol2) < 1e-6
  pure unit
