module Data.Sparse.Polynomial(module Data.Sparse.Polynomial) where

import Prelude

import Data.Array (catMaybes, sortBy, uncons, (!!), (..))
import Data.Complex (Cartesian(..), magnitudeSquared)
import Data.Complex (pow) as Cartesian
import Data.Foldable (foldr)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Int (toNumber)
import Data.Map (Map, empty, filter, fromFoldable, insert, mapMaybe, singleton, toUnfoldable, union, unionWith)
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..), uncurry)
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
-- | > -- Polynomials constitute a ring, so usual mathematical operations can be 
-- | > -- performed:
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
-- | > --
-- | > -- when the embedding structure is a field (Rationals, Reals, Complex ...) 
-- | > -- we can divide too 
-- | > import Data.Ratio
-- | > r = (1%9) ^ 2 <> (2%1) ^ 0 -- meaning x↦(1/9) x^2 + 2
-- | > s = (4%1) ^ 1 -- meaning x↦4x
-- | > r/s
-- | {fromTuples (Tuple 1 1 % 36)}
-- | 
-- | > r `mod` s
-- | {fromTuples (Tuple 0 2 % 1)}
-- | 
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
-- | > -- there is also a useful tool in case of univariate real polynomials:
-- | > pol = 1.0 ^ 2 <> 7.0 ^ 1 <> 12.0 ^ 0
-- | > roots pol
-- | [-3.0000000000000004-2.5587943030169417e-19i,
-- | -3.9999999999999982+2.5588046427745986e-19i]
-- | 
-- | > -- which gives the approximative values of all the complex roots of the 
-- | > -- polynomial.
-- | > -- Thanks to the sparse nature of the library, any abuse is permitted :-)
-- | > -- but best results are given when there is no multiple roots
-- | > roots $ 1.0 ^ 16 <> (-1.0) ^ 0
-- | [1.0+0.0i,0.3826834323650898+0.9238795325112867i,
-- | -0.7071067811865476+0.7071067811865476i,
-- | -0.9238795325112867-0.3826834323650898i,1.4018530340143064e-22-1.0i,
-- | 0.9238795325112867-0.3826834323650898i,
-- | 0.7071067811865476+0.7071067811865476i,
-- | -0.9238795325112867+0.3826834323650898i,
-- | -0.7071067811865475-0.7071067811865475i,
-- | 0.3826834323650898-0.9238795325112867i,
-- | 0.7071067811865475-0.7071067811865475i,
-- | 1.184013581560663e-30+1.0i,-0.3826834323650898+0.9238795325112867i,
-- | -1.0+7.614356628129376e-30i,-0.3826834323650898-0.9238795325112867i,
-- | 0.9238795325112867+0.3826834323650898i]
-- | > 
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
-- | > -- setters are little more difficult.
-- | > -- As t is the more shallow, it is the easiest
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
-- | >
-- | ```
data Polynomial a = Poly (Map Int a)

-- | Monoterm polynomial
monoPol :: forall a. a -> Int -> Polynomial a
monoPol x n = Poly $ insert n x empty

-- |  Monoterm polynomial infix notation
infixl 6 monoPol as ^

-- | Warning : the 2 appended maps are assumed without common keys
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
               in f (dividende - monom * q) $ acc + monom
    in f p $ Poly empty  
  mod p q = let d = p/q in p - d*q

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
              error = (\x -> x / (toNumber degree)) $ foldr (\k acc -> 
                sqrt (magnitudeSquared $ 
                  (k `th` goods) - (k `th` betters)) + acc) 0.0 indices
          in f betters error
    in f candidates 1.0

instance showPoly :: Show a => Show (Polynomial a) where
  show p = "{fromTuples " <> (foldr (<>) "" $ show <$> sortedMonoms p) <> "}"
  
derivative :: forall a. Eq a => Semiring a => (Int -> a) -> Polynomial a -> Polynomial a
derivative fromInt (Poly a) = Poly $ fromFoldable $ catMaybes $ map (uncurry deriveMononom) $ toUnfoldable a
  where
    deriveMononom 0 _ = Nothing
    deriveMononom _ coef | coef == zero = Nothing
    deriveMononom exp coef = Just $ Tuple (exp - 1) (coef * fromInt exp)

class IntLiftable a where
    fromInt :: Int -> a

instance intIntLiftable :: IntLiftable Int where
  fromInt = identity

instance numberIntLiftable :: IntLiftable Number where
  fromInt = toNumber

instance complexIntLiftable :: (Semiring a, Ring a, IntLiftable a) => IntLiftable (Cartesian a) where
  fromInt n = (_ * fromInt n) <$> one 

instance ratioIntLiftable :: (Ord a, IntLiftable a, EuclideanRing a) => IntLiftable (Ratio a) where
  fromInt n = fromInt n % one

diff :: forall a. Eq a => Ord a => Semiring a => EuclideanRing a => IntLiftable a => Polynomial a -> Polynomial a
diff = derivative fromInt

