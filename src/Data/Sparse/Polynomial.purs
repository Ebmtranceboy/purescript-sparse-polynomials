module Data.Sparse.Polynomial(module Data.Sparse.Polynomial) where

import Prelude hiding (gcd)

import Data.Array (catMaybes, sortBy, uncons, (!!), (..))
import Data.Complex (Cartesian(..), magnitudeSquared)
import Data.Complex (pow) as Cartesian
import Data.Foldable (foldr,maximum,product)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Int (toNumber)
import Data.Map (Map, empty, filter, fromFoldable, insert, mapMaybe, singleton
                , toUnfoldable, union, unionWith, lookup)
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Tuple (Tuple(..), uncurry, snd)
import Math (sqrt)
import Partial.Unsafe (unsafePartial)
import Data.Ratio(Ratio, (%))

-- | Represents a polynomial by the discrete list of its non-zero
-- | terms, stored in a map 
-- |
-- | * from `Int` (type of the degree of a term) 
-- | * to `a` (type of the coefficient of a term: 
-- |            integer, real, complex, polynomic ...).
-- | 
-- | ```
-- | > -- Working with Sparse Polynomials
-- | > import Data.Sparse.Polynomial 
-- | > 
-- | > -- Defining univariate polynomial with concatenation by (<>)
-- | > -- of terms (monoms). Each term has the form: coef ^ degree.
-- | > -- For instance
-- | > 2.0 ^ 3 <> (-3.0) ^ 0
-- | {fromTuples (Tuple 3 2.0)(Tuple 0 -3.0)}
-- | 
-- | > -- means x↦2x^3 - 3, so applied to 2:
-- | > (2.0 ^ 3 <> (-3.0) ^ 0) :. 2.0
-- | 13.0
-- | 
-- | > -- as expected :-)
-- | >
-- | > -- Polynomials constitute a ring, so usual mathematical operations can 
-- | > -- be performed:
-- | > a = 1 ^ 2 <> 4 ^ 0 -- working with Int here
-- | > b = 1 ^ 1 <> 1 ^ 0
-- | > a+b
-- | {fromTuples (Tuple 2 1)(Tuple 1 1)(Tuple 0 5)}
-- | 
-- | > a-b
-- | {fromTuples (Tuple 2 1)(Tuple 1 -1)(Tuple 0 3)}
-- | 
-- | > a*b
-- | {fromTuples (Tuple 3 1)(Tuple 2 1)(Tuple 1 4)(Tuple 0 4)}
-- | 
-- | > -- Coefficients can be extracted:
-- | > a ? 0
-- | 4
-- | 
-- | > --
-- | > -- When the embedding structure is a field (Rationals, Reals, 
-- | > -- Complex ...), we can divide too 
-- | > import Data.Ratio
-- | > r = (1%9) ^ 2 <> (2%1) ^ 0 -- meaning x↦(1/9) x^2 + 2
-- | > s = (4%1) ^ 1 -- meaning x↦4x
-- | > r/s
-- | {fromTuples (Tuple 1 1 % 36)}
-- | 
-- | > r `mod` s
-- | {fromTuples (Tuple 0 2 % 1)}
-- | 
-- | > gcd r s
-- | fromTuples (Tuple 0 2 % 1)
-- | >  
-- | > -- No surprise with differentiation:
-- | > diff $ (2%1)^3<>(-3%1)^1
-- | {fromTuples (Tuple 2 6 % 1)(Tuple 0 -3 % 1)}
-- | 
-- | > 
-- | > -- Composition is using the (:.) apply operator:
-- | > bThenA = (:.) b >>> (:.) a
-- | > aThenB = (:.) a >>> (:.) b
-- | >
-- | > -- but this time, the application is the usual function application:
-- | > bThenA  1
-- | 8
-- | 
-- | > aThenB 1
-- | 6
-- | 
-- | > 
-- | > -- There is also a useful tool in case of univariate real polynomials:
-- | > pol = 1.0 ^ 2 <> 7.0 ^ 1 <> 12.0 ^ 0
-- | > roots pol
-- | [-2.9999999996605635-3.769201527786494e-10i,
-- | -4.000000000339432+3.769201528752112e-10i]
-- | 
-- | > -- which gives the approximative values of all the complex roots of the 
-- | > -- polynomial.
-- | > -- Thanks to the sparse nature of the lib, any abuse is permitted :-)
-- | > -- but best results are given when there is no multiple roots
-- | > roots $ 1.0 ^ 16 <> (-1.0) ^ 0
-- | [1.0+0.0i,0.3826834323650897+0.9238795325112867i,
-- | -0.7071067811865476+0.7071067811865476i,
-- | -0.9238795325112871-0.3826834323650901i,
-- | -2.5434386919291434e-12-1.0000000000025875i,
-- | 0.9238795325108287-0.382683432364685i,
-- | 0.7071067811865476+0.7071067811865476i,
-- | -0.9238795325112867+0.3826834323650898i,
-- | -0.707106781186544-0.7071067811865521i,
-- | 0.382683432330398-0.9238795325016941i,
-- | 0.7071067812242033-0.7071067811940133i,
-- | 2.825247823205539e-19+1.0i,-0.3826834323650898+0.9238795325112867i,
-- | -1.0-1.7156434035577625e-17i,-0.3826834323650554-0.9238795325112262i,
-- | 0.9238795325112867+0.3826834323650898i]
-- |  
-- | > -- To Define multivariate polynomials, it's easier with the 
-- | > -- basis 'vectors'.
-- | > -- For instance, with 4 variables x,y,z and t, unity (=1 so 
-- | > -- not a variable!) is
-- | > u = 1 ^ 0 ^ 0 ^ 0 ^ 0
-- | > -- and similarly
-- | > x = 1 ^ 1 ^ 0 ^ 0 ^ 0
-- | > y = 1 ^ 0 ^ 1 ^ 0 ^ 0
-- | > z = 1 ^ 0 ^ 0 ^ 1 ^ 0
-- | > t = 1 ^ 0 ^ 0 ^ 0 ^ 1
-- | > u
-- | {fromTuples (Tuple 0 {fromTuples (Tuple 0 {fromTuples (Tuple 0 
-- |                                             {fromTuples (Tuple 0 1)})})})}
-- | 
-- | > -- Setters are little more difficult.
-- | > -- As t is the most shallow, it is the easiest
-- | > setT val = (_ :. val)
-- | > setZ val = (<$>) (_ :. val)
-- | > setY val = (<$>) (setZ val)
-- | > setX val = (<$>) (setY val)
-- | > -- but the scheme is general
-- | > pXYZT = x + y*y + z*z*z + t*t*t*t -- meaning (x,y,z,t)↦x+y²+z³+t⁴
-- | >
-- | > setT 0 $ setZ 0 $ setY 0 $ setX 1 pXYZT
-- | 1
-- | 
-- | > setT 0 $ setZ 0 $ setY 2 $ setX 0 pXYZT
-- | 4
-- | 
-- | > setT 0 $ setZ 3 $ setY 0 $ setX 0 pXYZT
-- | 27
-- | 
-- | > setT 4 $ setZ 0 $ setY 0 $ setX 0 pXYZT
-- | 256
-- | 
-- | > setT 4 $ setZ 3 $ setY 2 $ setX 1 pXYZT
-- | 288
-- | 
-- | > -- Coefficients can be extracted but [WARNING], in the reversed
-- | > -- order relative to insertion
-- | > pXYZT T ? 0 ? 0 ? 2 ? 0 -- meaning coefficient of y²
-- | 1
-- | 
-- | ```
data Polynomial a = Poly (Map Int a)

-- | Monoterm polynomial
monoPol :: forall a. a -> Int -> Polynomial a
monoPol x n = Poly $ insert n x empty

-- |  Monoterm polynomial infix notation
infixl 8 monoPol as ^ 
      
-- | Coefficient extraction
query :: forall a. Semiring a => Polynomial a -> Int -> a
query (Poly p) n = fromMaybe zero $ lookup n p

-- |  Coefficient extraction infix notation
infixl 8 query as ?

-- | Warning : the 2 appended maps are assumed without common keys
-- | and when they aren't, `<>` is used as the operator of resetting 
-- | the argument to its right by the argument to its left 
instance semigroupPoly :: Semigroup (Polynomial a) where
  append (Poly a) (Poly b) = Poly $ union a b

-- | Integer power
pow :: forall a. Semiring a => a -> Int -> a
pow x 0 = one
pow x i = x * pow x (i-1)

-- | Polynomial application
applyPoly :: forall a. Semiring a => Polynomial a -> a -> a
applyPoly (Poly coeffs) x = 
   foldrWithIndex (\i v acc -> acc + v * pow x i) zero coeffs

-- | Polynomial application infix notation
infixl 5 applyPoly as :.

instance eqPoly :: Eq a => Eq (Polynomial a) where
  eq (Poly p1) (Poly p2) = p1 == p2
  
instance functorPoly :: Functor Polynomial where
  map f (Poly p) = Poly $ mapMaybe (\v -> Just $ f v) p

instance semiringPoly :: (Eq a, Semiring a) => Semiring (Polynomial a) where
  add (Poly p1) (Poly p2) = Poly $ filter (_ /= zero) $ unionWith (+) p1 p2
  mul (Poly p1) (Poly p2) = Poly $ filter (_ /= zero) $ 
    foldr (unionWith (+)) empty $ 
      map (\(Tuple i v) -> 
        foldrWithIndex (\j w acc -> insert (i+j) (v*w) acc) empty p2) $
          (toUnfoldable p1 :: Array (Tuple Int a))
  zero = Poly empty
  one = Poly $ singleton 0 one

instance ringPoly :: (Eq a, Semiring a, Ring a) => Ring (Polynomial a) where
  sub p1 p2 = add p1 $ (_ * (-one)) <$> p2
  
instance commutativeRingPoly :: 
  (Eq a, CommutativeRing a) => CommutativeRing (Polynomial a)

-- | Dispatches the terms in list of tuples (degree,coefficient) and order it
-- | by decreasing degree
sortedMonoms :: forall a. Polynomial a -> Array (Tuple Int a)
sortedMonoms (Poly p) = 
   sortBy (\(Tuple i v) (Tuple j w) -> compare j i) $ toUnfoldable p

-- | Leading term
dominantMonom :: forall a. Eq a => Semiring a => Polynomial a -> Tuple Int a
dominantMonom p =   
  let ordered = sortedMonoms p
  in case (uncons ordered) of
    Just {head, tail} -> head
    _                 -> Tuple 0 zero

-- | Warning : prelude's gcd will not work as the condition degree = 0 is
-- | not sufficient to stop the recursion asking for value = 0
instance euclideanRingPoly :: 
   (Eq a, DivisionRing a, CommutativeRing a) 
      => EuclideanRing (Polynomial a) where
  degree p | Tuple i v <- dominantMonom p = i
  div p q = 
    let Tuple dsor vsor = dominantMonom q
        f dividende acc = 
         let Tuple dnde vnde = dominantMonom dividende
         in 
           if dnde < dsor 
             then acc
             else
               let r = (*) vnde $ recip vsor
                   monom = Poly $ insert (dnde-dsor) r empty
               in if dnde == 0 then acc + monom 
                  else  f (dividende - monom * q) $ acc + monom
    in f p $ Poly empty  
  mod p q = let d = p/q in p - d*q

-- | Greatest common divisor of 2 univariate polynomials
gcd :: forall a. Eq a => DivisionRing a => CommutativeRing a => 
      Polynomial a -> Polynomial a -> Polynomial a
gcd p q = 
  let {u,v} = bezout p q
  in u*p + v*q

-- | Find 2 polynomials u and v such that u p1 + v p2 == gcd (p1,p2)
bezout :: forall a. Eq a => CommutativeRing a => DivisionRing a =>
      Polynomial a -> Polynomial a -> {u :: Polynomial a, v :: Polynomial a}
bezout p1 p2 = res
      where res = f {r_: p1, r:p2, u_: one, v_: zero, u: zero, v: one}
            f {r_:r__, r:r_, u_:u__, v_:v__, u:u_, v:v_} =
              if r_ == zero then {u:u__, v:v__}
               else
                  let q = r__ / r_
                      r = r__ - q * r_
                      u = u__ - q * u_
                      v = v__ - q * v_
                   in f {r_, r, u_, u, v_, v}

instance ordPoly :: 
  (Ord a, Eq a, CommutativeRing a) => Ord (Polynomial a) where
  compare p q = 
    let sp = sortedMonoms p
        sq = sortedMonoms q
        f xs ys = case (uncons xs) of
          Just {head: Tuple ix vx, tail: tx} ->
            case (uncons ys) of
              Just {head: Tuple iy vy, tail: ty} ->
                case unit of
                  unit | ix /= iy -> compare ix iy
                       | vx /= vy -> compare vx vy
                       | otherwise -> f tx ty
              _ -> GT 
          _ -> case (uncons ys) of
            Just _ -> LT
            _      -> EQ
    in f sp sq

-- | Transforms a polynomial with real arguments 
-- | into a polynomial with complex arguments    
liftC :: Polynomial Number -> Polynomial (Cartesian Number)
liftC p = (\v -> (_*v) <$> one) <$> p

-- | Returns the n approximative roots of a polynomial of degree n
roots :: Polynomial Number -> Array (Cartesian Number)
roots pnum = 
  let p = liftC pnum
      Tuple degree lead = dominantMonom p
      unitary = (_ / lead) <$> p
      z0 = Cartesian 1.2 3.4
      indices = 0..(degree-1)
      candidates = (\x -> Cartesian.pow z0 x) <$> (toNumber <$> indices)
      th k xs = unsafePartial $ fromJust $ xs !! k
      f goods error' = 
        if error' < 1e-7
        then goods
        else 
          let betters = map (\i -> 
               let good = i `th` goods
                   prod = 
                     foldr (\j acc -> 
                       if i==j 
                        then acc 
                        else acc * ( good - (j `th` goods))) one indices
                in good - (unitary :. good) / prod) indices
              error = 
                let Poly residue = 
                      unitary - (product $ (\z -> one^1 - z^0) <$> betters)
                in fromMaybe 0.0 $ 
                  maximum $ sqrt <$> magnitudeSquared <$> 
                    snd <$> (toUnfoldable residue :: Array _)
          in f betters error
    in f candidates 1.0

instance showPoly :: Show a => Show (Polynomial a) where
  show p = "{fromTuples " <> (foldr (<>) "" $ show <$> sortedMonoms p) <> "}"
  
derivative :: forall a. Eq a => Semiring a => 
  (Int -> a) -> Polynomial a -> Polynomial a
derivative fromInt (Poly a) = 
  Poly $ fromFoldable $ catMaybes $ 
    map (uncurry deriveMonom) $ toUnfoldable a
      where
        deriveMonom 0 _ = Nothing
        deriveMonom _ coef | coef == zero = Nothing
        deriveMonom exp coef = Just $ Tuple (exp - 1) (coef * fromInt exp)

class IntLiftable a where
    fromInt :: Int -> a

instance intIntLiftable :: IntLiftable Int where
  fromInt = identity

instance numberIntLiftable :: IntLiftable Number where
  fromInt = toNumber

instance complexIntLiftable :: 
  (Semiring a, Ring a, IntLiftable a) => IntLiftable (Cartesian a) where
  fromInt n = (_ * fromInt n) <$> one 

instance ratioIntLiftable :: 
  (Ord a, IntLiftable a, EuclideanRing a) => IntLiftable (Ratio a) where
  fromInt n = fromInt n % one

-- | Univariate polynomial differentiation
diff :: forall a. Eq a => Ord a => 
  Semiring a => EuclideanRing a => IntLiftable a => 
               Polynomial a -> Polynomial a
diff = derivative fromInt

