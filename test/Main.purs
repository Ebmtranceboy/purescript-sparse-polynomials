module Test.Main where

import Prelude hiding (gcd)
import Effect (Effect)
import Data.Array (all)
import Data.Sparse.Polynomial
  ( Polynomial
  , (^)
  , (:.)
  , (.-)
  , axes
  , bezout
  , diff
  , display
  , down
  , eisenstein
  , factor
  , gcd
  , interpolate
  , liftC
  , pow
  , roots
  , xpose
  , (!)
  )
import Data.Complex (Cartesian, i, magnitudeSquared)
import Data.Ratio (Ratio, (%))
import Data.Tuple.Nested ((/\))
import Data.Foldable (foldr)
import JS.BigInt (BigInt, fromInt)
import Partial.Unsafe (unsafePartial)
import Test.Assert (assert')

pol1 :: Polynomial BigInt -- 3y^2-2y+5
pol1 = fromInt 3 ^ 2 <> (- fromInt 2) ^ 1 <> fromInt 5 ^ 0

pol2 :: Polynomial Number -- 3x^2+5
pol2 = 3.0 ^ 2 <> 5.0 ^ 0

pol3 :: Polynomial BigInt -- 4y-1
pol3 = (-fromInt 1) ^ 0 <> fromInt 4 ^ 1

pol4 :: Polynomial (Polynomial BigInt) -- (4y-1)x + 3y^2-2y+5
pol4 = pol3 ^ 1 <> pol1 ^ 0

pol5 :: Polynomial (Cartesian Int) -- x^2 + ix - 1
pol5 = (-one) ^ 0 <> i ^ 1 <> one ^ 2
 
pol6 :: Polynomial (Ratio Int)
pol6 = (-8%3) ^ 0 <> (1%7) ^ 1 <> (2%1) ^ 2

pol7 :: Polynomial (Ratio Int)
pol7 = (-8%3) ^ 2 <> (1%7) ^ 1 <> (2%1) ^ 0

type P3 = Polynomial (Polynomial (Polynomial (Ratio Int)))

main :: Effect Unit
main = unsafePartial $ do
  
  assert' "polynomial Int application" $ pol1 :. fromInt 2 == fromInt 13
  assert' "polynomial Number application" $ pol2 :. 2.0 == 17.0
  assert' "polynomial Complex application" $ pol5 :. i == ((_ * (-3)) <$> one)
  assert' "polynomial Rational application" $ pol6 :. (1%2) == -44%21
  assert' "coefficient extraction" $ pol3 ! 1 == fromInt 4
  let x :: P3
      x = (1%1) ^ 0 ^ 0 ^ 1
      y :: P3
      y = (1%1) ^ 0 ^ 1 ^ 0
      z :: P3
      z = (1%1) ^ 1 ^ 0 ^ 0
      p :: P3
      p = z*(x*x-y*y)
      q :: P3
      q = z*z*(x+y)

  assert' "bivariate polynomial" $ fromInt 5 `xpose` (fromInt 3 `down xpose` pol4) == fromInt 81 
  assert' "multivariate polynomial" $ 
    (7%1) `xpose` ((5%1) `down xpose` ((3%1) `down $ down xpose` (y*y*y - x*z*z))) == 62%1
  assert' "display multivariate polynomial" $ 
    display ["x","y"] (3 ^ 1 ^ 2 - 1 ^ 2 ^ 3) == "((-1)×y^2)×x^3+((3)×y)×x^2" 
  assert' "polynomial sum" $ (pol1 + pol3) :. fromInt 3 == fromInt 37
  assert' "polynomial difference" $ (pol1 - pol3) :. fromInt 3 ==  fromInt 15
  assert' "polynomial product" $ (pol1 * pol3) :. fromInt 3 == fromInt 286
  assert' "polynomial quotient" $ (pol7 / pol6) :. (0%1) == -4%3
  assert' "multivariate polynomial quotient" $ 
    (z * pow x 2 - z * pow y 2) / (x + y) == z * (x - y)
  assert' "polynomial rest" $ (pol7 `mod` pol6) :. (0%1) == -14%9
  assert' "differentiation" $ diff pol7 == (-16%3) ^ 1 <> (1%7) ^ 0
  assert' "polynomial composition" $ (pol3 .- pol1) :. fromInt 3 == fromInt 103
  assert' "root polynomial nullification" $ 
    (foldr (+) 0.0 $ magnitudeSquared <$> 
      (liftC pol2 :. _) <$> roots pol2) < 1e-6
  assert' "multivariate polynomial gcd" $ degree (gcd p q / (z*(x+y))) == 0
  assert' "univariate polynomial bezout" $ 
    ( pure 
      ( \ { u, v } -> 
        degree ((u * pol6 + v * pol7) / gcd pol6 pol7) 
      ) <*> bezout pol6 pol7
    ) == pure 0
  assert' "Lagrange's identity" $
      let u = (1%1)^0^0^0^0
          _ /\ [a,b,c,d] = axes u
      in (pow a 2 + pow b 2) * (pow c 2 + pow d 2) - pow (a * c + b * d) 2 == pow (a * d - b * c) 2
  assert' "univariate polynomial interpolation" $ 
    interpolate [(1%1)/\(3%1), (2%1)/\(1%1), (3%1)/\(2%1)] == (3%2)^2-(13%2)^1+(8%1)^0
  assert' "univariate polynomial factorization" $
    let pol = (fromInt 32 % fromInt 1)^5-(fromInt 243 % fromInt 1)^0
        fs = factor pol
    in all (\f -> let p' = pol/f in pol == p' * f) fs
  assert' "univariate polynomial irreductibility" $ 
    eisenstein (fromInt 1^5-fromInt 6^1+fromInt 3^0) (fromInt 3)
  
