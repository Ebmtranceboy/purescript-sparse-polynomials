module Data.Sparse.Polynomial
  (module Data.Sparse.Polynomial) 
  where

import Prelude 
  ( class Eq
  , class EuclideanRing
  , class Semiring
  , class Ord
  , class Ring
  , class Functor
  , class Semigroup
  , class CommutativeRing
  , class Show
  , class Monoid
  , one
  , zero
  , identity
  , div
  , (<$>)
  , (==)
  , (*)
  , (+)
  , ($)
  , (-)
  , (/)
  , (<<<)
  , (>>>)
  , (<>)
  , (/=)
  , (<)
  , (>)
  , (>>=)
  , (||)
  , (&&)
  , lcm
  , mod
  , negate
  , add
  , degree
  , compare
  , flip
  , show
  , map
  , otherwise
  
  )

import Data.Array 
  ( catMaybes
  , sortBy
  , uncons
  , (!!)
  , (..)
  , all
  , reverse
  , scanl
  , (:)
  , head
  , zip
  , zipWith)
import Data.Array (filter) as Array
import Data.Complex (Cartesian(..), magnitudeSquared)
import Data.Complex (pow) as Cartesian
import Data.Foldable (lookup) as Array
import Data.Foldable (foldr, foldl, maximum, product)
import Data.FoldableWithIndex (foldrWithIndex)
import Data.Int (toNumber)
import Data.Map (Map, empty, filter, fromFoldable, insert, mapMaybe, singleton
                , toUnfoldable, union, unionWith, lookup, findMax)
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Monoid (power)
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Ord (abs)
import Data.Ordering (Ordering (..)) as DataOrd
import Data.String (joinWith)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), uncurry, fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Number (sqrt)
import Partial.Unsafe (unsafePartial)
import Data.Ratio (Ratio, (%), denominator, numerator)
import JS.BigInt (BigInt)
import JS.BigInt (fromInt) as BigInt
import Prim.Int (class Add, class Compare)
import Prim.Ordering (Ordering, LT, EQ, GT)
import Type.Proxy (Proxy(..))

-- | Represents a non-null polynomial by the discrete list of its non-zero
-- | terms, stored in a map 
-- |
-- | * from `Int` (type of the degree of a term) 
-- | * to `a` (type of the coefficient of a term: 
-- |            integer, real, complex, polynomic ...).
-- | 
-- | and a null polynomial by the empty map.
-- | ```
-- | > -- Working with Sparse Polynomials
-- | > import Data.Sparse.Polynomial 
-- |  
-- | > -- Defining univariate polynomial
-- | > -- ------------------------------
-- | >
-- | > --  * by concatenation / resetting with (<>) [see Semigroup instance note] or
-- | > --  * by summation with (+) and (-)
-- | >
-- | > -- of terms (monoms). Each term has the form: coef ^ degree.
-- | > -- For instance
-- | >
-- | > display ["x"] $ 2.0 ^ 3 <> (-4.0) ^ 0
-- | "(2.0)×x^3+(-4.0)"
-- | >
-- | > 2.0 ^ 3 <> (-4.0) ^ 0
-- | (2.0)×x^3+(-4.0)
-- | >
-- | > display ["z"] $ 2.0 ^ 3 + (-4.0) ^ 0
-- | "(2.0)×z^3+(-4.0)"
-- | >
-- | > -- displays (with variable "x" by default) the polynomial 
-- | > -- that subtract 4 from the double of the cube, 
-- | > -- so evaluated at 5 with the (:.) evaluation operator:
-- | >
-- | > (2.0 ^ 3 <> (-4.0) ^ 0) :. 5.0
-- | 246.0
-- | >
-- | > -- or with `xpose`, its flipped version:
-- | >
-- | > 5.0 `xpose` (2.0 ^ 3 <> (-4.0) ^ 0)
-- | 246.0
-- | >
-- | > -- without having to specify the name of the variable, as expected :-)
-- | 
-- | 
-- | > -- Polynomials constitute a Ring, so usual mathematical operations can 
-- | > -- be performed:
-- | > 
-- | > a = 1 ^ 2 <> 4 ^ 0 -- working with Int as the underlying structure
-- | >                    -- here 
-- | > b = 1 ^ 1 <> 1 ^ 0
-- | > 
-- | > a
-- | (1)×x^2+4
-- | > 
-- | > b
-- | (1)×x+1
-- | > 
-- | > a+b
-- | (1)×x^2+(1)×x+5
-- | >
-- | > a-b
-- | (1)×x^2+(-1)×x+3
-- | >
-- | > a*b
-- | (1)×x^3+(1)×x^2+(4)×x+4
-- | 
-- | > -- Composition is using the (.-) substitution operator:
-- | >
-- | > aAfterB = a .- b
-- | > aAfterB
-- | (1)×x^2+(2)×x+5
-- | >
-- | > b .- a
-- | (1)×x^2+5
-- | >
-- | > -- or `xpand`, its flipped version:
-- | >
-- | > bThenA = b `xpand` a
-- | > bThenA
-- | (1)×x^2+(2)×x+5
-- | >
-- | > a `xpand` b
-- | (1)×x^2+5
-- |
-- | 
-- | > -- Coefficients can be extracted with the (?) query operator :
-- | > a ? 0
-- | 4
-- | 
-- |
-- | > -- When the underlying structure is a Division ring (Rationals, Reals, 
-- | > -- Complex, or any other field), we can divide too. (Technically, when
-- | > -- the underlying structure is only a Euclidean ring -- like  Int --,
-- | > -- the algorithm works when the rest is null and occasionnally loops
-- | > -- forever if not.)
-- | >
-- | > import Data.Ratio
-- | > r = (1%9) ^ 2 <> (2%1) ^ 0 -- meaning x↦(1/9) x^2 + 2
-- | > s = (4%1) ^ 1 -- meaning x↦4x
-- | >
-- | > r / s
-- | (1 % 36)×x
-- | >
-- | > r `mod` s
-- | 2 % 1
-- | >
-- | > gcd r s
-- | 32 % 1
-- | >
-- | > -- [WARNING] the implemented gcd is designed to be useful 
-- | > -- for non-constant polynomials modulo some scaling factor.
-- | > -- This has 2 major consequences :
-- | >
-- | > -- 1) `Prelude.gcd a b` is generally _different_ from 
-- | > --    `Data.Sparse.Polynomial.gcd (a^0) (b^0)`
-- | > --    because the scaling factor is left unchanged 
-- | > --    at the end of the algorithm (see gcd's comment)
-- | > -- 2) Little Bézout's theorem doesn't hold : for any two multivariate
-- | > --    polynomials P and Q, it's _not_ always possible to find two
-- | > --    polynomials U and V, and a ring element r such that
-- | > --    U×P + V×Q = r GCD(P,Q).
-- | > --    [Consider P(X,Y)=X, Q(X,Y)=Y then no (U,V) possible
-- | > --    since GCD(P,Q)=1]
-- |
-- | 
-- | > -- No surprise with differentiation:
-- | > diff $ (2%1)^3<>(-4%1)^1
-- | (6 % 1)×x^2+(-4 % 1)
-- | 
-- |
-- | > -- There is also a useful tool in case of univariate real polynomials:
-- | >
-- | > pol = 1.0 ^ 2 <> 7.0 ^ 1 <> 12.0 ^ 0
-- | > roots pol
-- | [-2.9999999996605635-3.769201527786494e-10i,
-- | -4.000000000339432+3.769201528752112e-10i]
-- | >
-- | > -- which gives the approximative values of all the complex roots of the 
-- | > -- polynomial.
-- | > -- Thanks to the sparse nature of the lib, any abuse is permitted :-)
-- | > -- but best results are given when there is no multiple roots
-- | > 
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
-- | 
-- | > ------------------------------------
-- | > --                                --
-- | > -- ABOUT MULTIVARIATE POLYNOMIALS --
-- | > --                                --
-- | > --           -------              --
-- | > --          |  API  |             --
-- | > --           -------              --
-- | > ------------------------------------
-- |
-- | > --    This set of notes shows several uses of the functions
-- | > --    performing  multivariate polynomial manipulation provided 
-- | > --    by this library, along with (^) and (?) : 
-- | > --
-- | > --     * `set`,  for evaluation and arity decrease, more efficient 
-- | > --               but demanding than
-- | > --     * `fill`, for substitution (or `full` for full evaluation)
-- | > --               where arity is conserved.
-- | > --
-- | > --    Then, two functions are provided to increase arity :
-- | > --     * `pad`,  rather coarse, useful in particular
-- | > --               with numerical constants, and
-- | > --     * `nest`, for more specific uses.
-- | > --
-- | > --    The inverse of `pad`  :
-- | > --     * `unpad`, carelessly decreases arity.
-- | > --
-- | > --    Finally, one function makes variable changes :
-- | > --     * the `swap` function,
-- | > --
-- | > --    and one function extracts the constant coefficient
-- | > --    of any polynomial :
-- | > --     * the `peel` function.
-- | > --
-- | > --    See documentation of each function for more specifications. 
-- |
-- |
-- | > -- 1) DEFINITION : There are (at least) three possible 
-- | > --    ----------   and equivalent ways to define multivariate
-- | > --                 polynomials with this library:
-- |
-- | > --    a) By using a sum of terms where each term is defined with 
-- | > --       the enumerative representation "n ^ ... ^ e_Z ^ e_Y ^ e_X",
-- | > --       generalizing the construction seen with univariate polynomials
-- | > --       where n is an element of the underlying structure and the e_i 
-- | > --       are of type Int and correspond to respective variable's degrees.
-- | >
-- | > 3^0^2
-- | (3)×x^2
-- | >
-- | > 4^1^1^0
-- | ((4)×z)×y
-- | >
-- | > 3^0^0^0^2 + 4^0^1^1^0 + 5^1^0^0^0
-- | (3)×x^2+((4)×z)×y+(5)×t
-- |
-- | > --    b) By using
-- | > --       * the basis axes where each axis (aka term that embodies
-- | > --         a variable) is defined with the enumerative representation,
-- | > --         and
-- | > --       * a wrapping function that lifts the constant numeric values
-- | > --         (refered as n in a))  to the required (multivariate) 
-- | > --         polynomial type (see the `axes`  function).
-- | > --        
-- | >
-- | > -- For instance, with arity = 4 and Int as the underlying structure :
-- | >
-- | > x = 1^0^0^0^1
-- | > y = 1^0^0^1^0
-- | > z = 1^0^1^0^0
-- | > t = 1^1^0^0^0
-- | > kst v = v^0^0^0^0 
-- | >
-- | > kst 3*x*x + kst 4*y*z + kst 5*t 
-- | (3)×x^2+((4)×z)×y+(5)×t
-- |
-- | > --    Note that, in the enumerative representation of a term, the 
-- | > --    positions of the exponents listed from left to right were designed 
-- | > --    to be of decreasing proximity (i.e of decreasing technical 
-- | > --    accessibility) so that the righter the position of a 1,
-- | > --    the more remote and more difficult to access.
-- | > --    In other words, if an integer is associated with the proximity of
-- | > --    a term, and if `proxi` is the function returning that integer,
-- | > --    
-- | > --    proxi(x) < proxi(y) < ... < proxi(nearest) < proxi(kst one).
-- | > --
-- | > --    In addition, this library has been built, for any arity,
-- | > --    following these four principles : 
-- | > --
-- | > --     * the proximity of two consecutive axes defer by 1,
-- | > --     * the proximity of the most remote axis ("x") is set to 0,
-- | > --     * the proximity of the most accessible (aka nearest) axis
-- | > --       is set to arity-1, and
-- | > --     * the term `kst one` is more accessible than any other axis.
-- |
-- | > --    This leads to the preferred third option:
-- |
-- | > --    c) By using 
-- | > --     * proximity of axes (denoted with <"'">), 
-- | > --     * `one^1`, the _univariate_ axis, and
-- | > --     * `pad` and `swap` functions : 
-- | >
-- | > --============ DEFINING SCHEME FOR ANY ARITY (4 here) ===================
-- | >                -----------------------------                                                   
-- | >
-- | > x' = Proxy :: _ 0   -- *) Sequentially, give each proximity an identifier 
-- | > y' = Proxy :: _ 1
-- | > z' = Proxy :: _ 2
-- | > t' = Proxy :: _ 3   -- *) Check that <arity> = <proxi(nearest axis)+1>
-- | >
-- | > kst = pad t'        -- *) Wrapping function = pad <arity-1>
-- | >
-- | >                     -- *) Choose a underlying structure to define `one`
-- | >                     --    then :
-- | > t = pad z' (1^1)    --    Nearest axis = pad <arity-2> (one^1)
-- | >
-- | >                     -- *) Other axis =
-- | > x = swap x' t' t    --      swap <proxi(self)> <arity-1> (nearest axis)
-- | > y = swap y' t' t    --    ...
-- | > z = swap z' t' t    --    ...
-- | > ...                 --    ...
-- | > --=======================================================================
-- | >
-- | > kst 3*x*x + kst 4*y*z + kst 5*t          
-- | (3)×x^2+((4)×z)×y+(5)×t
-- |
-- | > --     ------------------------------
-- | > --    | Using `pad` increases arity. |
-- | > --     ------------------------------
-- | 
-- | 
-- | > -- 2) DISPLAY : By defaut, the first four variables are printed with the 
-- | > --    -------
-- | > --    "x","y","z" and "t" strings in that order, but, for five
-- | > --    or more variables, the variables names are proximity-indexed
-- | > --    versions of "x".
-- | > --    So,
-- | >
-- | > display ["a","b","c"] $ 2^0^0^0 + 4^0^1^0
-- | > --    returns
-- | "(4)×b+2"
-- | > --    whereas
-- | > 2^0^0^0 + 4^0^1^0
-- | > --    displays
-- | (4)×y+2
-- | > --    and
-- | > 2^0^0^0^0^0 + 4^0^0^0^1^0
-- | > --    displays
-- | (4)×x1+2
-- |
-- |
-- | > -- 3) EVALUATION : A multivariate polynomial, say with arity = 4 
-- | > --    ----------   for instance, like
-- | >
-- | > p = kst 2 * x - y * y + z * z * t - z * t * t 
-- | > p
-- | (2)×x+((-1))×y^2+((1)×t)×z^2+((-1)×t^2)×z
-- | >
-- | > --    has been modeled in this library as
-- | > --    a polynomial in x whose coefficients are
-- | > --    polynomials in y whose coefficients are
-- | > --    polynomials in z whose coefficients are
-- | > --    polynomials in t whose coefficients are numbers
-- | > --    (in other words, polynomials in the most accessible variable
-- | > --    are univariate polynomials).
-- | 
-- | > --    As a consequence, if we evaluate (`set`) the t-component of p
-- | > --    at a constant value,
-- | > 
-- | > 4 `set t'` p
-- | (2)×x+((-1))×y^2+(4)×z^2+(-16)×z
-- | >
-- | > :t 4 `set t'` p
-- | Polynomial (Polynomial (Polynomial Int))
-- | >
-- | > --    we get the same 3-variate polynomial as if we substitute (`fill`) t
-- | > --    with the corresponding constant polynomial :
-- | > 
-- | > kst 4 `fill t'` p
-- | (2)×x+((-1))×y^2+(4)×z^2+((-16))×z
-- | >
-- | > --    However, with `fill`, the result is in the same scope 
-- | > --    as p (where arity = 4).
-- | >
-- | > :t kst 4 `fill t'` p
-- | Polynomial (Polynomial (Polynomial (Polynomial Int)))
-- |
-- | > --     -------------------------------------
-- | > --    | Using `set` _does_ decrement arity, |
-- | > --    | using `fill` does not change arity. |
-- | > --     -------------------------------------
-- |
-- | > --    This is the desired behavior because `set` consumes all occurrences 
-- | > --    of a variable so the loss of one unit of arity only reflects
-- | > --    the saved space. On the other hand, with `fill`, all occurrences 
-- | > --    of the replaced variable are consumed as well but replacements 
-- | > --    variables  may include the replaced variable itself (which is
-- | > --    not possible with `set`), so arity is not expected to be 
-- | > --    decreased mecanically in this case.
-- |
-- | > --    Here are all the ways to define
-- | > --
-- | > --             q(x,y) = p(x,y,3,4) = (2)×x+(-1)×y^2+(-12)
-- | > --
-- | > --    from p(x,y,z,t) :
-- | >
-- | > --    (xtend = pad x' : convert a number
-- | > --    to the corresponding univariate constant polynomial)
-- | >
-- | > 3 `set z'` (4 `set t'` p)                -- output arity = 2
-- | > 4 `set z'` (xtend 3 `set z'` p)          -- output arity = 2
-- | > xtend 3 `set z'` (kst 4 `fill t'` p)     -- output arity = 3
-- | > 4 `set t'` (kst 3 `fill z'` p)           -- output arity = 3
-- | > pad z' 3 `fill z'` (4 `set t'` p)        -- output arity = 3
-- | > pad z' 4 `fill z'` (xtend 3 `set z'` p)  -- output arity = 3
-- | > kst 3 `fill z'` (kst 4 `fill t'` p)      -- output arity = 4
-- | > kst 4 `fill t'` (kst 3 `fill z'` p)      -- output arity = 4
-- |
-- |
-- | > --    Notice that using `set` requires to be careful about the types of 
-- | > --    the provided arguments. This is the first reason `set` is
-- | > --    more demanding to use than `fill`.
-- |
-- | > --    Ultimately, the easiest ways to fully evaluate a polynomial 
-- | > --    (numerical result of q(1,2) with arity 0 after all partial 
-- | > --    partial evaluations performed), are either with `set`,
-- | > --    providing the values _in_order_
-- |
-- | > set x' 1 $ set y' 2 $ set z' 3 $ set t' 4 p
-- | -14
-- |
-- | > --    or with `fill`, providing constant polynomials (notice 
-- | > --    the arbitrary order) and, eventually, extracting the constant :
-- |
-- | > peel$ fill t'(kst 4) $ fill x'(kst 1) $ fill z'(kst 3) $ fill y'(kst 2) p
-- | -14
-- |
-- | > --    or with `full`, a 'saturated' version of `fill` where values have
-- | > --    to be provided in order, this time :
-- | 
-- | > peel $ map kst [1,2,3,4] `full` p 
-- | -14
-- |
-- |
-- | > --    Similarly, when evaluating the z-component of p at a non-constant
-- | > --    univariate polynomial, it is implicitely expressed in t, 
-- | > --    in respect of the type of the coefficients of the z-component :
-- | >
-- | > pz = (2^1-5^0) `set z'` p
-- | > pz
-- | (2)×x+((-1))×y^2+(2)×z^3+(-15)×z^2+(25)×z
-- | >
-- | > --    Even if any t doesn't seem to be introduced, this expression is 
-- | > --    expected because of the way `set` works : after having been 
-- | > --    replaced with a t expression, each occurrence of z in p has 
-- | > --    vanished. The empty z-slot is vacant, and since t follows z 
-- | > --    by order of proximity, t-content earns an order
-- | > --    of remoteness and everything looks like t has been renamed z. 
-- | > --    As a check, the fact that the same polynomial is obtained when  
-- | > --    filling z with the corresponding polynomial in t should
-- | > --    convince that the expression of pz is right :
-- | > --    
-- | > 
-- | > pt = (kst 2 * t - kst 5) `fill z'` p
-- | > pt
-- | (2)×x+((-1))×y^2+(2)×t^3+(-15)×t^2+(25)×t
-- | 
-- | > --    This odd process is the second reason `set` is more demanding
-- | > --    than `fill`. In addition, note that, with `fill`, the replacement 
-- | > --    polynomial can include any variable, unlike with `set` where
-- | > --    replacement variables are always stricly more accessible 
-- | > --    than the replaced one :
-- | > 
-- | > (kst 2 * z - kst 5 * y ) `fill z'` p
-- | (2)×x+((25)×t+(-1))×y^2+(((-20)×t)×z+(5)×t^2)×y+((4)×t)×z^2+((-2)×t^2)×z
-- | 
-- | 
-- | > --    When needed, it is possible to change pt to pz by evaluating 
-- | > --    the z-component of pt at any polynomial with right arity (say  
-- | > --    zero). Indeed, the empty content associated with z gets removed
-- | > --    since `set` decrements arity and the content associated with t
-- | > --    is shifted one step more remote and gets associated with z,
-- | > --    as already stated.
-- | > 
-- | > zero `set z'` pt
-- | (2)×x+((-1))×y^2+(2)×z^3+(-15)×z^2+(25)×z
-- | 
-- | > --    It is conceptually easier to change pz to pt, by substituting z 
-- | > --    with t, as long as we use a version of pz with arity at least 4 
-- | > --    because the use of `fill` requires its two arguments of the same
-- | > --    arity :
-- | > --    Note that the `pad` function can't be used to change arity here
-- | > --    since it shifts all the axes several times, unlike the `nest` 
-- | > --    function which shifts several chosen axes once  : 
-- | > --    
-- | > 
-- | > t `fill z'` (nest t' pz)
-- | (2)×x+((-1))×y^2+(2)×t^3+(-15)×t^2+(25)×t
-- | >
-- | > --     --------------------------------
-- | > --    | Using `nest` increments arity. |
-- | > --     --------------------------------
-- | 
-- | > --    This method can be used to change pt to pz as well
-- | > --    (arity won't match though, `set t' zero` would fix that)
-- |
-- | > z `fill t'` pt
-- | (2)×x+((-1))×y^2+(2)×z^3+((-15))×z^2+(25)×z
-- |
-- |
-- | > --    There is another way to change pt to pz using 
-- | > --    a function that unconditionnally swaps two axes
-- | > --    (and keeps scope).
-- | >
-- | > swap z' t' pt
-- | (2)×x+((-1))×y^2+(2)×z^3+((-15))×z^2+(25)×z
-- | 
-- | > --     --------------------------------------
-- | > --    | Using `swap` does not change arity. |
-- | > --     --------------------------------------
-- |
-- | > --    Finally, it is possible to `swap` pz to pt too, but
-- | > --    pz's arity is only 3, so swaping z and t requires to `nest`
-- | > --    a t-slot beforehand just like in one of the preceeding examples
-- | >
-- | > swap z' t' $ nest t' pz
-- | (2)×x+((-1))×y^2+(2)×t^3+(-15)×t^2+(25)×t
-- | >
-- | > --    and a simpler way is to just `nest` a z-slot, thanks to the fact
-- | > --    that `nest` shifts all previous z content on step nearer, to t:
-- | >
-- | > nest z' pz
-- | (2)×x+((-1))×y^2+(2)×t^3+(-15)×t^2+(25)×t
-- |
-- |
-- | > --    Notation used in the documentation of the manipulation functions
-- | > --    ----------------------------------------------------------------
-- | > --    P : natural number reflecting the arity of the polynomial
-- | > --    P = 0 for the elements of the underlying structure
-- | > --    P = 1 for univariate polynomials
-- | > --    P = 2 for bivariate polynomials and more generally,
-- | > --          multivariate polynomials are P-variate.
-- |
-- |
-- | > -- 4) COEFFICIENT EXTRACTION :
-- | > --    ----------------------
-- | > --
-- | > -- coefficient of zt², beware, orders ...
-- | > let p = 10^0^0^1^2 + 20^1^2^0^0 + 42^2^1^0^0 in p ? 0 ? 0 ? 1 ? 2
-- | 42
-- | 
-- | ```
newtype Polynomial a = Poly (Map Int a)

-- | Monoterm polynomial
monoPol :: forall a. a -> Int -> Polynomial a
monoPol x n = Poly $ insert n x empty

-- |  Monoterm polynomial infix notation
infixl 8 monoPol as ^ 

class NextAxis :: Int -> Int -> Constraint
class NextAxis a n | a -> n, n -> a where
  nextAxis :: Proxy a -> Proxy n
  prevAxis :: Proxy n -> Proxy a
  
instance
  ( Add a 1 n
  ) => NextAxis a n where
  nextAxis _ = Proxy :: Proxy n
  prevAxis _ = Proxy :: Proxy a

-- | ```
-- | > --     ---------------------------------------------------
-- | > --    | PAD : the lifting function that introduces        |
-- | > --    | ---                                               |
-- | > --    | in a polynomial as many new variables as 1 + the  |
-- | > --    | provided arity, shifting the content of each      |
-- | > --    | of the initial variables as many orders nearer.   |
-- | > --     ---------------------------------------------------
-- | > --    | input : polynomial |
-- | > --     ----------------------------------------------------
-- | > --    |                            |    arity  |  arity    |
-- | > --    |          usage             |    input  | output    |
-- | > --    |                            |           |           |
-- | > --     ====================================================
-- | > --    |  pad (Proxy :: _ <arity>)  |    P>=0   | P+arity+1 |
-- | > --     ----------------------------------------------------
-- |
-- | > pad (Proxy :: _ 0) 5
-- | 5
-- |
-- | > pad (Proxy :: _ 0) (5^0)
-- | 5
-- |
-- | > pad (Proxy :: _ 0) (5^1)
-- | (5)×y
-- |
-- | > pad (Proxy :: _ 1) (5^0)
-- | 5
-- |
-- | > pad (Proxy :: _ 1) (5^1)
-- | (5)×z
-- |
-- | > pad (Proxy :: _ 1) (5^1^1)
-- | ((5)×t)×z
-- |
-- | ```
class Pad :: Int -> Type -> Type -> Constraint
class Pad n a b | n a -> b where
  pad :: Proxy n -> a -> b

instance Pad 0 a (Polynomial a) where
  pad _ p = p ^ 0
else instance
  ( Pad n1 a b
  , Add n1 1 n
  ) => Pad n a (Polynomial b) where
  pad _ p = pad (Proxy :: Proxy n1) p ^ 0

-- | ```
-- | > --     -----------------------------------------------------
-- | > --    | UNPAD : the inverse of `pad` that decreases the     |
-- | > --    | -----                                               |
-- | > --    | arity of a polynomial of 1 + the                    |
-- | > --    | provided arity, shifting the content of each        |
-- | > --    | of the initial variables to a more remote position. |
-- | > --     -----------------------------------------------------
-- | > --    | input : polynomial |
-- | > --     ----------------------------------------------------
-- | > --    |                            |    arity  |  arity    |
-- | > --    |          usage             |    input  | output    |
-- | > --    |                            |           |           |
-- | > --     ====================================================
-- | > --    | unpad (Proxy :: _ <arity>) |P>= 2+arity| P-arity-1 |
-- | > --     ----------------------------------------------------
-- |
-- | > unpad (Proxy :: _ 0) (5^1^1 + 6^1^0)
-- | (6)×x
-- |
-- | > unpad (Proxy :: _ 1) (5^1^1^0 + 6^1^0^0 + 7^0^0^0)
-- | (6)×x+7
-- |
-- | ```
class Unpad :: Int -> Type -> Type -> Constraint
class Unpad n a b | n b -> a where
  unpad :: Proxy n -> b -> a

instance
  ( Semiring a
  ) => Unpad (-1) a a where
  unpad _ p = p
else instance
  ( Unpad n (Polynomial (Polynomial a)) b
  , Add n 1 n1
  , Semiring a
  , Eq a
  ) => Unpad n1 (Polynomial a) b where
  unpad _ p = (_ ? 0) $ unpad (Proxy :: Proxy n) p

-- | Coefficient extraction
query :: forall a. Semiring a => Polynomial a -> Int -> a
query (Poly p) n = fromMaybe zero $ lookup n p

-- |  Coefficient extraction infix notation
infixl 8 query as ?

-- | Warning : the 2 appended maps are assumed without common keys
-- | and when they aren't, `<>` is used as the operator of resetting 
-- | the argument to its right by the argument to its left 
instance
  ( Eq a
  , Semiring a
  ) => Semigroup (Polynomial a) where
  append pa@(Poly a) pb@(Poly b) 
    | pa == zero && pb == zero = Poly empty
    | pa == zero = pb
    | otherwise = Poly $ union a b

instance 
  ( Eq a
  , Semiring a
  ) => Monoid (Polynomial a) where
  mempty = Poly empty

-- | Integer power
pow :: forall a. Semiring a => a -> Int -> a
pow _ 0 = one
pow x i 
  | i `mod` 2 == 0 = 
    let y = x `pow` (i `div` 2)
    in y * y
  | otherwise = 
    let y = x `pow` ((i-1) `div` 2)
    in x * y * y

-- | Univariate polynomial evaluation
evaluate :: forall a. Semiring a => Polynomial a -> a -> a
evaluate (Poly coeffs) x = 
   foldrWithIndex (\i v acc -> acc + v * x `pow` i) zero coeffs

-- | Univariate polynomial evaluation infix notation
infixl 5 evaluate as :.

-- | ```
-- | > --     ---------------------------------------------------------
-- | > --    | SET : the evaluating function that removes the variable |
-- | > --    | ---                                                     |
-- | > --    | at focus in a polynomial by setting it to the provided  |
-- | > --    | value, and shifts the content of each of the other      |      
-- | > --    | nearer variables and associates it to the variable      |
-- | > --    | one order more remote.                                  |
-- | > --     ---------------------------------------------------------
-- | > --    | input1 : value || input2 : polynomial |
-- | > --     ---------------------------------------------------------------
-- | > --    |    arity  |                             |    arity   |  arity |
-- | > --    |   input1  |           `usage`           |   input2   = output |
-- | > --    |           |                             |            |        |
-- | > --     ================================================================
-- | > --    |P-(focus+1)|  `set (Proxy :: _ <focus>)` |   P>focus  =   P-1  |
-- | > --     ---------------------------------------------------------------
-- | 
-- | > 1^0^0^1 + 2^1^3^0
-- | (1)×x+((2)×z)×y^3
-- | 
-- | > (5^0^0) `set (Proxy :: _ 0)` (1^0^0^1 + 2^1^3^0)
-- | ((2)×y)×x^3+5
-- | 
-- | > (5^1^3) `set (Proxy :: _ 0)` (1^0^0^1 + 2^1^3^0)
-- | ((7)×y)×x^3
-- | 
-- | > (5^0) `set (Proxy :: _ 1)` (1^0^0^1 + 2^1^3^0) 
-- | (1)×x+(250)×y
-- | 
-- | > (5) `set (Proxy :: _ 2)` (1^0^0^1 + 2^1^3^0) 
-- | (1)×x+(10)×y^3
-- | 
-- | ```
class Set :: Int -> Type -> Type -> Constraint
class Set n a b | n b -> a where
  set :: Proxy n -> a -> Polynomial b -> b 

instance
  ( Semiring a
  ) => Set 0 a a where
  set _ = xpose

else instance
  ( Set n1 a b
  , Add n1 1 n
  , Semiring a
  ) => Set n a (Polynomial b) where
  set _ = down $ set (Proxy :: Proxy n1)

down :: forall f a c d. 
  Functor f => 
  Semiring a =>
  (a -> c -> d) -> a -> f c -> f d
down f = (<$>) <<< f

xpose :: forall a. Semiring a => a -> Polynomial a -> a
xpose = flip evaluate

-- | Multivariate polynomial substitution
flipXpand :: forall a. 
  Eq a => 
  Semiring a => 
  Polynomial a -> Polynomial a -> Polynomial a
flipXpand (Poly coeffs) xp = 
   foldrWithIndex (\i v acc -> acc + ((v * _ ) <$> xp `pow` i)) zero coeffs

-- | Multivariate polynomial substitution infix notation
infixl 5 flipXpand as .-

class FillValid :: Int -> Type -> Constraint
class FillValid n a where
  fillValid :: Proxy n -> (Polynomial a -> Polynomial a -> Polynomial a) 

instance
  ( Eq a
  , Semiring a
  ) => FillValid 0 a where
    fillValid _ = xpand
else instance
  ( FillValid n1 a
  , Eq a
  , Semiring a
  , Add n1 1 n
  ) => FillValid n (Polynomial a) where
  fillValid _ = deep $ fillValid (Proxy :: Proxy n1)

deep :: forall f a c d. 
  Functor f => 
  Semiring a =>
  (a -> c -> d) -> Polynomial a -> f c -> f d
deep f = (<$>) <<< f <<< (_ ? 0)

xpand :: forall a. 
  Eq a => 
  Semiring a => 
  Polynomial a -> Polynomial a -> Polynomial a
xpand = flip flipXpand

-- | ```
-- | > --     ------------------------------------------------
-- | > --    | FILL : the substitution function that replaces |
-- | > --    | ----                                           |
-- | > --    | each occurrence of the focus in a polynomial   |
-- | > --    | by the provided value.                         |
-- | > --     ------------------------------------------------
-- | > --    | input1 : value || input2 : polynomial |
-- | > --     -----------------------------------------------------------------
-- | > --    |    arity  |                                |    arity  |  arity |
-- | > --    |   input1  |            `usage`             |   input2  = output |
-- | > --    |           |                                |           |        |
-- | > --     =================================================================
-- | > --    |      P    |  `fill (Proxy :: _ <focus>)`   |  P>focus  =    P   |
-- | > --     -----------------------------------------------------------------
-- | 
-- | > 1^0^0^1 + 2^1^3^0
-- | (1)×x+((2)×z)×y^3
-- | 
-- | > 1^0^0^1 + 1^0^1^0
-- | (1)×x+(1)×y
-- | 
-- | > (1^0^0^1 + 1^0^1^0) `fill (Proxy :: _ 0)` (1^0^0^1 + 2^1^3^0)
-- | (1)×x+((2)×z)×y^3+(1)×y
-- | 
-- | > (1^0^0^1 + 1^0^1^0) `fill (Proxy :: _ 1)` (1^0^0^1 + 2^1^3^0)
-- | ((2)×z)×x^3+(((6)×z)×y)×x^2+(((6)×z)×y^2+1)×x+((2)×z)×y^3
-- |
-- | > (1^0^0^1 + 1^0^1^0) `fill (Proxy :: _ 2)` (1^0^0^1 + 2^1^3^0) 
-- | ((2)×y^3+1)×x+(2)×y^4
-- |
-- | ```
fill :: forall a v w.
  Eq a =>
  Semiring a =>
  NextAxis v w =>
  GoSwap 0 w a =>
  Proxy v -> Polynomial a -> Polynomial a -> Polynomial a
fill _ r p =
  let x' = Proxy :: Proxy 0
  in zero `set x'` 
    (pad x' r `fillValid x'` 
      (goSwap x' (Proxy :: Proxy w) $ pad x' p)
    )
  
class Full :: Int -> Type -> Constraint
class Full n a where
  fullImpl :: Proxy n -> Array (Polynomial a -> Polynomial a -> Polynomial a)

instance
  ( Eq a
  , Semiring a
  ) => Full 0 a where
  fullImpl _ = [fill (Proxy :: Proxy 0)]
else instance 
  ( Full n1 a
  , Add n1 1 n
  , NextAxis n w
  , GoSwap 0 w a
  , Eq a
  , Semiring a
  ) => Full n a where
  fullImpl _ = fullImpl (Proxy :: Proxy n1) <> [fill (Proxy :: Proxy n)]

-- | Saturated version of `fill` where array values have
-- | to be provided in order of proximity : value at index i 
-- | is set to axis of proximity <i>.
full :: forall a n m. 
  Full n a => 
  Add n 1 m => 
  Arity (Polynomial a) m => 
  Array (Polynomial a) -> Polynomial a -> Polynomial a
full arr p = 
  foldr identity p $ zipWith ($) (fullImpl (prevAxis $ arity' p)) arr

instance Eq a => Eq (Polynomial a) where
  eq (Poly p1) (Poly p2) = p1 == p2
  
instance Functor Polynomial where
  map f (Poly p) = Poly $ mapMaybe (\v -> Just $ f v) p

instance (Eq a, Semiring a) => Semiring (Polynomial a) where
  add (Poly p1) (Poly p2) = Poly $ filter (_ /= zero) $ unionWith (+) p1 p2
  mul (Poly p1) (Poly p2) = Poly $ filter (_ /= zero) $ 
    foldr (unionWith (+)) empty $ 
      map (\(Tuple i v) -> 
        foldrWithIndex (\j w acc -> insert (i+j) (v*w) acc) empty p2) $
          (toUnfoldable p1 :: Array (Tuple Int a))
  zero = Poly empty
  one = Poly $ singleton 0 one

instance (Eq a, Ring a) => Ring (Polynomial a) where
  sub p1 p2 = add p1 $ (_ * (-one)) <$> p2
  
instance 
  ( Eq a
  , Ring a
  ) => CommutativeRing (Polynomial a)

-- | Dispatches the terms of a polynomial with respect to its first variable
-- | in list of tuples (degree, coefficient) and order it by decreasing degree
sortedMonoms :: forall a. Polynomial a -> Array (Tuple Int a)
sortedMonoms (Poly p) = 
   sortBy (\(Tuple i _) (Tuple j _) -> compare j i) $ toUnfoldable p

-- | Terms of a polynomial with respect to its first variable
-- | in list of tuples (degree, coefficient)
monoms :: forall a. Polynomial a -> Array (Tuple Int a)
monoms (Poly p) = toUnfoldable p

-- | Leading term of a polynomial with respect to its first variable
dominantMonom :: forall a. 
  Eq a => 
  Semiring a => 
  Polynomial a -> Tuple Int a
dominantMonom p =   
  let ordered = sortedMonoms p
  in case (uncons ordered) of
    Just { head, tail: _ } -> head
    _                -> Tuple 0 zero

-- | Leading term of an expanded multivariate polynomial 
class Semiring a <= Leadable a where
  leader :: Polynomial a -> Polynomial a
  
instance 
  ( Eq a
  , Leadable a
  , Semiring a
  ) => Leadable (Polynomial a) where
  leader p =
    let d /\ c = dominantMonom p
    in leader c ^ d
else instance 
  ( Eq a
  , Semiring a
  ) => Leadable a where
  leader p = 
    let d /\ c = dominantMonom p
    in c ^ d

-- | Divisibility between two leaders
class Divisible a where
  divides :: a -> a -> Maybe a

instance (Semiring a, Divisible a) => Divisible (Polynomial a) where
  divides (Poly d) (Poly n) =
    let dummy = { key: -1, value: zero }
        { key: kd, value: vd } = fromMaybe dummy $ findMax d
        { key: kn, value: vn } = fromMaybe dummy $ findMax n
    in if kd > kn 
      then Nothing
      else (vd `divides` vn) >>= (\q -> Just $ q ^ (kn - kd))
else instance (EuclideanRing a) => Divisible a where
  divides a b = Just $ b / a

-- | Euclidean division between two multivariate polynomials
-- | over an Euclidean ring
division :: forall a.
  Ring a =>
  Eq a =>
  Divisible a =>
  Leadable a => 
  Polynomial a -> Polynomial a -> { div :: Polynomial a, mod :: Polynomial a }
division num den =
  let ld = leader den
      loop n q r =
        if n == zero 
          then { div: q, mod: r }
          else 
            let ln = leader n
            in case ld `divides` ln of
              Just ratio -> loop (n - ratio * den) (q + ratio) r
              _ -> loop (n - ln) q (r + ln)
    in loop num zero zero

-- | Degree
degreeAccordingToFirstVariable :: forall a. 
  Eq a => 
  Semiring a =>
  Polynomial a -> Int
degreeAccordingToFirstVariable p | Tuple i _ <- dominantMonom p = i

-- | Warning : prelude's gcd will not work as the condition degree = 0 is
-- | not sufficient to stop the recursion asking for value = 0
instance euclideanRingPoly :: 
   ( Eq a
   , Divisible a
   , Ring a
   , Leadable a
   , CommutativeRing a
   ) => EuclideanRing (Polynomial a) where
  degree = degreeAccordingToFirstVariable
  div p q = (p `division` q).div
  mod p q = (p `division` q).mod

class Primitivable a where
  primitivePart :: Polynomial a -> Polynomial a
  globalFactor :: Polynomial a -> Polynomial a -> Polynomial a
  
instance 
  ( Ord a
  , Divisible a
  , Leadable a
  , CommutativeRing a
  , EuclideanRing a
  , Primitivable a
  ) => Primitivable (Polynomial a) where
  primitivePart p = p / (cont p ^ 0)
  globalFactor f g = gcd (cont f) (cont g) ^ 0
else instance (Eq a, Semiring a) => Primitivable a where
  primitivePart p = p
  globalFactor _ _  = one

gcds :: forall a. 
  Ord a =>
  Divisible a =>
  Leadable a =>
  EuclideanRing a => 
  Primitivable a =>
  Array (Polynomial a) -> Polynomial a
gcds arr = 
  case uncons arr of
       Just { head, tail } -> 
        case uncons tail of
             Just _ -> gcd head (gcds tail)
             _ -> head
       Nothing -> one

-- | Greatest common divisor of 2 multvariate polynomials
-- | The final constant scaling factor is nothing but arbitrary
-- | For instance gcd (2xyz) (3yz) gives 2yz
gcd :: forall a. 
  Ord a =>
  Divisible a =>
  CommutativeRing a =>
  Leadable a =>
  Primitivable a =>
  Polynomial a -> Polynomial a  -> Polynomial a
gcd pa' pb' =  
  let highestCoefficient p | Tuple _ v <- dominantMonom p = v ^ 0
      rprs p1 p2 = 
        let p3 = 
              ( p1 * 
                  pow (highestCoefficient p2) 
                      (degree p1 - degree p2 + 1 )
              ) `mod` p2
        in 
          if p3 == zero 
            then [] 
            else p3 : rprs p2 p3

      pa = primitivePart pa'
      pb = primitivePart pb'            
      arr = 
        if pa' > pb' 
          then reverse $ pb : rprs pa pb
          else reverse $ pa : rprs pb pa
      lastNotNull = fromMaybe one $ head arr
                    
    in globalFactor pa' pb' * primitivePart lastNotNull

cont :: forall a. 
  Ord a =>
  EuclideanRing a =>
  Divisible a =>
  Leadable a =>
  Primitivable a =>
  Polynomial (Polynomial a) -> Polynomial a
cont p = 
  gcds $ snd <$> monoms p

-- | Find 2 univariate polynomials u and v 
-- | such that u(x) p1(x) + v(x) p2(x) == g(x) 
-- | where g = gcd (p1,p2)
bezout :: forall a. 
  Eq a => 
  Ord a =>
  CommutativeRing a => 
  Divisible a =>
  Leadable a =>
  Univariate (Polynomial a) =>
  Polynomial a -> Polynomial a -> 
       Maybe 
        { u :: Polynomial a
        , v :: Polynomial a 
        }
bezout p1 p2 =
  if isMultivariate p1 || isMultivariate p2
    then Nothing
    else
      if p1 < p2
        then
          bezout p2 p1 >>= (\ { u, v } -> Just { u: v, v: u })
        else res
  where res = f { r_: p1, r:p2, u_: one, v_: zero, u: zero, v: one }
        f { r_:r__, r:r_, u_:u__, v_:v__, u:u_, v:v_ } =
          if r_ == zero 
            then Just { u:u__, v:v__ }
            else
              let q = r__ / r_
                  r = r__ - q * r_
                  u = u__ - q * u_
                  v = v__ - q * v_
              in f { r_, r, u_, u, v_, v }


instance ordPoly :: 
  ( Ord a
  , Eq a
  , CommutativeRing a
  ) => Ord (Polynomial a) where
  compare p q = 
    let sp = sortedMonoms p
        sq = sortedMonoms q
        f xs ys = case (uncons xs) of
          Just {head: Tuple ix vx, tail: tx} ->
            case (uncons ys) of
              Just {head: Tuple iy vy, tail: ty} ->
                  next
                    where 
                    next
                      | ix /= iy = compare ix iy
                      | vx /= vy = compare vx vy
                      | otherwise = f tx ty
              _ -> DataOrd.GT 
          _ -> case (uncons ys) of
            Just _ -> DataOrd.LT
            _      -> DataOrd.EQ
    in f sp sq

-- | Gets the right representation of unity in the context 
-- | of the provided multivariate polynomial
unity :: forall a. 
  Eq a => 
  Semiring a =>
  Polynomial a -> Polynomial a
unity _ = one

class Univariate a where
  isMultivariate :: a -> Boolean
  
instance Univariate (Polynomial (Polynomial a)) where 
  isMultivariate _ = true
else instance Univariate a where
  isMultivariate _ = false

class Arity :: Type -> Int -> Constraint
class Arity a n | a -> n where
  arity' :: a -> Proxy n

instance
  ( Arity (Polynomial a) n1
  , Add n1 1 n
  ) => Arity (Polynomial (Polynomial a)) n where 
  arity' _ = Proxy
else instance Arity (Polynomial a) 1 where
  arity' _ = Proxy
else instance Arity a 0 where
  arity' _ = Proxy

-- | ```
-- | > --     -------------------------------------------------
-- | > --    | PEEL : the extracting function that returns     |
-- | > --    | ----                                            |
-- | > --    | the constant term (in the underlying structure) |
-- | > --    | of a polynomial.                                |
-- | > --     -------------------------------------------------
-- | > --    | input : polynomial |
-- | > --     ----------------------------------
-- | > --    |            |    arity  |  arity  |
-- | > --    |     usage  |    input  = output  |
-- | > --    |            |           |         |
-- | > --     ==================================
-- | > --    |     peel   |    P>0    =   0     |
-- | > --     ----------------------------------
-- |
-- | > peel $ (1^1+3^0) * (1^1-3^0)
-- | -9
-- |
-- | > peel $ (4^2^2 - 12^1^1) / 2^1^1
-- | -6
-- |
-- | ```
class Peel a b | a -> b where
  peel :: Polynomial a -> b
  
instance 
  ( Peel a b
  , Eq a
  , Semiring a
  ) => Peel (Polynomial a) b where
  peel p = peel (p ? 0)
else instance
  ( Semiring a
  ) => Peel a a where
  peel p = p ? 0

-- | Gets the right representation of each of the variables in the context 
-- | of the provided multivariate unity
class Axed a r where
  axes :: a -> (r -> a) /\ Array a

instance
  ( Axed a r
  , Semiring a
  , Peel a r
  ) => Axed (Polynomial a) r where
  axes arg = 
    let kst /\ zs = axes (arg ? 0)
        a = kst $ peel arg
    in ((_ ^ 0) <<< kst) /\ ((a ^ 1) : ((_ ^ 0) <$> zs))
else instance (Semiring a, Eq a) => Axed a a where
  axes _ = identity /\ []

-- | ```
-- | > --     -------------------------------------------------
-- | > --    | NEST : the extension function that introduces a |
-- | > --    | ----                                            |
-- | > --    | new variable before the focus of a polynomial   |
-- | > --    | and shifts each of the other nearer variables   |
-- | > --    | (focus included) one order nearer.              |
-- | > --     -------------------------------------------------
-- | > --    | input : polynomial |
-- | > --     ------------------------------------------------
-- | > --    |                           |    arity  |  arity |
-- | > --    |          usage            |    input  = output |
-- | > --    |                           |           |        |
-- | > --     ================================================
-- | > --    | nest (Proxy :: _ <focus>) |  P>=focus =   P+1  |
-- | > --     ------------------------------------------------
-- |
-- | > nest (Proxy :: _ 0) $ 5^0
-- | 5
-- |
-- | > nest (Proxy :: _ 0) $ 8^0^1
-- | (8)×y
-- |
-- | > nest (Proxy :: _ 0) $ 21^1^1
-- | ((21)×z)×y
-- |
-- | > nest (Proxy :: _ 1) $ 5^0^0
-- | 5
-- |
-- | > nest (Proxy :: _ 1) $ 8^0^0^1
-- | (8)×x
-- |
-- | > nest (Proxy :: _ 1) $ 13^0^1^0
-- | (13)×z
-- |
-- | > nest (Proxy :: _ 1) $ 34^1^1^1
-- | (((34)×t)×z)×x
-- |
-- | > nest (Proxy :: _ 2) $ 5^0^0
-- | 5
-- |
-- | > nest (Proxy :: _ 2) $ 34^1^1^1
-- | (((34)×t)×y)×x
-- |
-- | ```
class Nest :: Int -> Type -> Constraint
class Nest n a where
  nest :: Proxy n -> a -> Polynomial a 

instance Nest 0 a where
  nest _ = xtend
else instance
  ( Nest n1 a
  , Add n1 1 n
  ) => Nest n (Polynomial a) where
  nest _ = map $ nest (Proxy :: Proxy n1)

xtend :: forall a. a -> Polynomial a
xtend a = a ^ 0

-- | ```
-- | > --     --------------------------------------------
-- | > --    | SWAP : the swapping function that permutes |
-- | > --    | ----                                       |
-- | > --    | two axes in a polynomial.                  |
-- | > --     --------------------------------------------
-- | > --    | input : polynomial |
-- | > --     -----------------------------------------------------------------
-- | > --    |                                            |    arity  |  arity |
-- | > --    |                 usage                      |    input  = output |
-- | > --    |                                            |           |        |
-- | > --     =================================================================
-- | > --    |swap (Proxy :: _ <ax1>) (Proxy :: _ <ax2>)  |    P>=2   =     P  |
-- | > --     -----------------------------------------------------------------
-- |
-- | > f = 3^0^0^0^2 + 4^0^1^3^0 + 5^1^0^0^0
-- | > f
-- | (3)×x^2+((4)×z)×y^3+(5)×t
-- | >
-- | > swap (Proxy :: _ 0) (Proxy :: _ 1) f
-- | ((4)×z)×x^3+(3)×y^2+(5)×t
-- |
-- | > swap (Proxy :: _ 3) (Proxy :: _ 1) f
-- | (3)×x^2+(5)×y+((4)×t^3)×z
-- |
-- | ```
class SwapAdjacent :: Int -> Type -> Constraint
class SwapAdjacent n a where
  swapAdjacent :: 
    Proxy n -> (Polynomial (Polynomial a) -> Polynomial (Polynomial a))

instance
  ( Eq a
  , Semiring a
  ) => SwapAdjacent 0 a where
    swapAdjacent _ = xchng
else instance
  ( SwapAdjacent n1 a
  , Semiring a
  , Add n1 1 n
  ) => SwapAdjacent n (Polynomial a) where
  swapAdjacent _ = map $ swapAdjacent (Proxy :: Proxy n1)

xchng :: forall a. 
  Eq a => 
  Semiring a =>
  Polynomial (Polynomial a) ->  Polynomial (Polynomial a) 
xchng p = 
  let y = one ^ 1 ^ 0
  in zero `xpose` (xtend y `xpand` ((map $ map xtend) p))  

class Swap :: Int -> Int -> Type -> Constraint
class Swap m n a where
  swap :: 
    Proxy m -> 
    Proxy n -> 
    (Polynomial (Polynomial a) -> Polynomial (Polynomial a))

instance
  ( Compare m n o
  , SwapSort o m n a
  ) => Swap m n a where
  swap = swapSort (Proxy :: Proxy o)

class SwapSort :: Ordering -> Int -> Int -> Type -> Constraint
class SwapSort o m n a where
  swapSort :: 
    Proxy o -> Proxy m -> Proxy n -> 
    (Polynomial (Polynomial a) -> Polynomial (Polynomial a))

instance
  ( SwapInOrder m n a
  ) => SwapSort LT m n a where
  swapSort _ _ _ = swapInOrder (Proxy :: Proxy m) (Proxy :: Proxy n)
else instance
  ( SwapInOrder n m a
  ) => SwapSort GT m n a where
  swapSort _ _ _ = swapInOrder (Proxy :: Proxy n) (Proxy :: Proxy m)
else instance SwapSort EQ m n a where
  swapSort _ _ _ = identity
  
class SwapInOrder :: Int -> Int -> Type -> Constraint
class SwapInOrder m n a where
  swapInOrder ::  Proxy m -> Proxy n -> (Polynomial (Polynomial a) -> Polynomial (Polynomial a))
  
instance
  ( GoSwap m delta a
  , Add m delta n
  ) => SwapInOrder m n a where
  swapInOrder _ _ = goSwap (Proxy :: Proxy m) (Proxy :: Proxy delta)

class GoSwap :: Int -> Int -> Type -> Constraint
class GoSwap from delta a where
  goSwap :: Proxy from -> Proxy delta -> (Polynomial (Polynomial a) -> Polynomial (Polynomial a))
  
instance GoSwap from 0 a where
  goSwap _ _ = identity
else instance
  ( SwapAdjacent from a
  ) => GoSwap from 1 a where
  goSwap _ _ = swapAdjacent (Proxy :: Proxy from)
else instance
  ( GoSwap next delta1 a
  , Add from 1 next
  , Add delta1 1 delta
  , SwapAdjacent from a
  ) => GoSwap from delta a where
  goSwap _ _ = 
    swapAdjacent (Proxy :: Proxy from) >>> goSwap (Proxy :: Proxy next) (Proxy :: Proxy delta1) 
      >>> swapAdjacent (Proxy :: Proxy from)

  
-- | Transforms a univariate polynomial with real arguments 
-- | into a univariate polynomial with complex arguments    
liftC :: Polynomial Number -> Polynomial (Cartesian Number)
liftC p = (\v -> (_*v) <$> one) <$> p

-- | Returns the n approximative roots of a univariate polynomial of degree n
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

-- | Displays a multivariate polynomial
-- | with respect to the provided list of names.
-- | What ever the arity, the zero polynomial is displayed as the empty string. 
class Display a where
  arity :: a -> Int
  display :: Array String -> a -> String
  
instance 
  ( Display a
  , Ord a
  , Semiring a
  ) => Display (Polynomial a) where
  arity p = 1 + (fromMaybe 0 $ maximum $ (arity <<< snd) <$> monoms p)
  display arr p =
    case uncons arr of
      Nothing -> ""
      Just { head, tail } -> 
          joinWith "+" $ (\ (n /\ a) ->
            let  
              coef = display tail a
              parens x = "(" <> x <> ")"
              next 
                  | n == 0 = if a < zero then parens coef else coef
                  | n == 1 = parens coef <> "×" <> head
                  | otherwise = parens coef <> "×" <> head <> "^" <> show n
            in next
            ) <$> sortedMonoms p  
else instance 
  ( Show a
  , Arity a 0
  ) => Display a where
  arity _ = 0
  display _ x = show x

instance 
  ( Display a
  , Ord a
  , Semiring a
  ) => Show (Polynomial a) where
  show x = flip display x $
    case arity x of
         0 -> [""]
         1 -> ["x"]
         2 -> ["x","y"]
         3 -> ["x","y","z"]
         4 -> ["x","y","z","t"]
         a -> ("x" <> _) <<< show <$> (0..(a-1)) 

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

instance integerLiftable :: IntLiftable BigInt where
  fromInt = BigInt.fromInt

instance complexIntLiftable :: 
  (Semiring a, Ring a, IntLiftable a) => IntLiftable (Cartesian a) where
  fromInt n = (_ * fromInt n) <$> one 

instance ratioIntLiftable :: 
  (Ord a, IntLiftable a, EuclideanRing a) => IntLiftable (Ratio a) where
  fromInt n = fromInt n % one

instance
  ( Eq a, IntLiftable a, Semiring a) => IntLiftable (Polynomial a) where
  fromInt n = (_ * fromInt n) <$> one


-- | Univariate polynomial differentiation
diff :: forall a. Eq a => Ord a => 
  Semiring a => EuclideanRing a => IntLiftable a => 
               Polynomial a -> Polynomial a
diff = derivative fromInt

-- | Polynomial such that the second element of each tuple is 
-- | the image of the first element.
interpolate :: forall a.
  Eq a =>
  Semiring a =>
  EuclideanRing a =>
  Array (a /\ a) -> Polynomial a

interpolate arr =
  let go n build_ current_ prod_ arr_ =
        case uncons arr_ of
          Just { head: x /\ y, tail }
            -> 
              let 
                build = 
                  foldl
                    (\ acc j -> 
                      let i = n+1 - j
                      in acc+((acc?(j-1)?(i+1) - acc?(j-1)? i) / (acc? 0? n - acc? 0? i))^i^j
                    )
                    (build_ + x ^ n ^ 0 + y ^ n ^ 1)
                    (2..(n+1))
              in go (n+1)
                    build
                    (current_ + (build?(n+1)? 0)^0 * prod_)
                    (prod_ * (one ^ 1 - x ^ 0))
                    tail
          _ -> current_
  in 
    case uncons arr of
      Just { head: x0 /\ y0, tail }
        -> go 1 
              (x0 ^ 0 ^ 0 + y0 ^ 0 ^ 1) 
              (y0 ^ 0)
              (one ^ 1 - x0 ^0)
              tail
      _ -> zero

-- | True if n is < 2 or prime
isPrime :: forall a. 
  Ord a => 
  Semiring a => 
  EuclideanRing a => 
  a -> Boolean
isPrime n =
  let go i = 
        if (i*i) > n
          then true
          else n `mod` i /= zero && go (i + one)
  in go (one + one)

-- | Ad infinitum
nextPrime :: forall a. 
  Ord a => 
  Semiring a => 
  EuclideanRing a => 
  a -> a
nextPrime n = 
  if isPrime (n + one)
    then n + one
    else nextPrime (n + one)

-- | If n is prime, returns true /\ n,
-- | otherwise, false /\ d if d | n with d > 1
primeFactor :: forall a. 
  Ord a => 
  Eq a => 
  EuclideanRing a => 
  a -> Boolean /\ a
primeFactor n =
  let ldpf p =
        if n `mod` p == zero 
          then p /\ p
          else if n < (p*p) 
            then n /\ n
            else ldpf (nextPrime p)
  in 
    if n == one 
      then false /\ one
      else 
        let ldpn = ldpf (one + one)
          in (fst ldpn == n) /\ snd ldpn

-- | Factorizes a number > 1  in an array (divider /\ multiplicity)
primeFactorization :: forall base exp. 
  Ord base => 
  Eq base => 
  Semiring base =>
  EuclideanRing base =>
  Semiring exp =>
  base -> Array (base /\ exp)
primeFactorization m =
    let go acc n current cpt =
         if n == one 
          then acc
          else 
            let bool = primeFactor n
                nogarbage = 
                  if current == zero 
                    then acc 
                    else (current /\ cpt) : acc
            in 
              let p = snd bool
              in 
                if fst bool 
                  then
                    if p == current
                      then (p /\ (cpt + one)) : acc
                      else (p /\ one) : nogarbage
                  else
                    if p == current
                      then go acc (n/p) current (cpt + one)
                      else go nogarbage (n/p) p one
      in go [] m zero zero

-- | All the divisors of a positive integer
divisors :: forall a.
  Semiring a =>
  EuclideanRing a =>
  Eq a =>
  Ord a =>
  a -> Array a
divisors n =
  let power' m i = p where 
        Multiplicative p = power (Multiplicative m) i 
      pos = 
        product <$> 
          ( sequence $ 
            (\(d /\ m) -> power' d <$> 0..m) 
            <$> primeFactorization n
          )
  in pos <> (negate <$> pos)

-- | At least one non-constant polynomial factor 
-- | if the univariate input, with rational coefficients,
-- | is not irreductible, empty array if it is.
factor :: forall a. 
  Eq a => 
  Ord a => 
  EuclideanRing a => 
  IntLiftable a => 
  Divisible a => 
  Leadable a => 
  Polynomial (Ratio a) -> Array (Polynomial (Ratio a))

factor pol =
  let zfier q_ n_ l_
        | q_ == zero = l_
        | otherwise = 
            let q = diff q_ * (((one % n_) * _) <$> one)
                n = n_ + one
                l = lcm (denominator $ q_ :. zero) l_
            in zfier q n l
      d = zfier pol one one
  in ((_ % one) <$> _ ) <$> factorOnZ (numerator <$> (((d % one) * _) <$> pol))

-- | At least one non-constant polynomial factor 
-- | if the univariate input, with integer coefficients,
-- | is not irreductible, empty array if it is.
factorOnZ :: forall a. 
  Ord a => 
  Ring a => 
  EuclideanRing a => 
  Divisible a => 
  IntLiftable a =>
  Leadable a => 
  Polynomial a -> Array (Polynomial a)

factorOnZ pol =
  let n = degree pol
      search d = -- a factor of degree d 
        let sample = 
              scanl (\acc _ -> acc + one) (zero - (fromInt $ d/2)) $ 0..d
            probe = (abs <<< (pol :. _)) <$> sample
        in case Array.lookup zero (zip probe sample) of
              Just x -> [one ^ 1 - x ^ 0]
              _ ->
                let
                  candidates = interpolate <$> (zip sample <$> (sequence $ divisors <$> probe))
                  fr = (_ % one)
                in 
                  Array.filter 
                    ( \candidate -> (fr <$> pol) `mod` (fr <$> candidate) == zero) 
                  candidates
    in Array.filter ((_ /= 0) <<< degree) $ foldr (<>) [] $ search <$> 1..(n/2) 

 
-- | Eisenstein criterium of irreductibility of f:
-- |                            _
-- | Exists prime p,             |
-- | p   not | an                | => f = anx^n + ... + a1x + a0 irreductible over Q
-- | p       | ai for i=0..n-1   | 
-- | p^2 not | a0               -
-- |
eisenstein :: forall a.
  Eq a =>
  Divisible a =>
  Leadable a =>
  CommutativeRing a =>
  EuclideanRing a =>
  Polynomial a -> a -> Boolean
eisenstein f p = 
  let n = degree f
      ds = all (\i -> (f ? i) `mod` p == zero) $ 0..(n-1)
  in (f ? n) `mod` p /= zero && ds && (f ? 0) `mod` (p*p) /= zero

