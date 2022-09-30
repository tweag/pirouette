-- This was copied from SimpleSMT
module PureSMT.SExpr where

import Data.Bits (testBit)
import Data.Char (isDigit, isSpace)
import Data.List (intersperse)
import Data.Ratio (denominator, numerator, (%))
import qualified Data.Text
import Numeric (readHex, showFFloat, showHex)
import System.IO
import Text.Read (readMaybe)
import Prelude hiding (abs, and, concat, const, div, mod, not, or)
import qualified Prelude as P

-- | Results of checking for satisfiability.
data Result
  = -- | The assertions are satisfiable
    Sat
  | -- | The assertions are unsatisfiable
    Unsat
  | -- | The result is inconclusive
    Unknown
  deriving (Eq, Show)

-- | Common values returned by SMT solvers.
data Value
  = -- | Boolean value
    Bool !Bool
  | -- | Integral value
    Int !Integer
  | -- | Rational value
    Real !Rational
  | -- | Bit vector: width, value
    Bits !Int !Integer
  | -- | Some other value
    Other !SExpr
  deriving (Eq, Show)

-- | S-expressions. These are the basic format for SmtLib-2.
data SExpr
  = Atom String
  | List [SExpr]
  deriving (Eq, Ord, Show)

-- | Apply a function over all atom in a Value.
overAtomV :: (String -> String) -> Value -> Value
overAtomV f (Other s) = Other (overAtomS f s)
overAtomV _ rest = rest

-- | Apply a function over all atoms in a S-expression.
overAtomS :: (String -> String) -> SExpr -> SExpr
overAtomS f (Atom s) = Atom (f s)
overAtomS f (List ss) = List [overAtomS f s | s <- ss]

-- | Show an s-expression.
showsSExpr :: SExpr -> ShowS
showsSExpr ex =
  case ex of
    Atom x -> showString x
    List es ->
      showChar '('
        . foldr (\e m -> showsSExpr e . showChar ' ' . m) (showChar ')') es

-- | Show an s-expression without intermediate 'as'.
showsSExprWithoutAs :: SExpr -> ShowS
showsSExprWithoutAs (List [Atom "as", x, _]) =
  showsSExprWithoutAs x
showsSExprWithoutAs (List (List [Atom "as", x, _] : args)) =
  showsSExprWithoutAs $ List (x : args)
showsSExprWithoutAs ex =
  case ex of
    Atom x -> showString x
    List es ->
      showChar '('
        . drop 1 -- remove the initial space
        . foldr
          (\e m -> showChar ' ' . showsSExprWithoutAs e . m)
          (showChar ')')
          es

-- | Show an s-expression in a Haskell fashion.
showsSExprHaskellish :: SExpr -> ShowS
showsSExprHaskellish = fst . go
  where
    go :: SExpr -> (ShowS, Bool)
    go (List [Atom "as", x, _]) = go x
    go (List (List [Atom "as", x, _] : args)) = go $ List (x : args)
    go ex =
      case ex of
        Atom x -> (showString x, False)
        List [] -> (showString "()", False)
        List [cstr] -> go cstr
        t@(List (Atom ":" : _))
          | Just lst <- list t ->
            ( showChar '['
                . drop 2
                . foldr
                  (\e m -> showString ", " . fst (go e) . m)
                  (showChar ']')
                  lst,
              False
            )
        List (cstr : args) ->
          let (showCstr, _) = go cstr
           in ( showCstr
                  . foldr
                    ( \e m ->
                        let (showArg, spaceArg) = go e
                         in if spaceArg
                              then showString " (" . showArg . showChar ')' . m
                              else showChar ' ' . showArg . m
                    )
                    id
                    args,
                True
              )

    list :: SExpr -> Maybe [SExpr]
    list (Atom "[]") = Just []
    list (List [Atom "as", Atom "[]", _]) = Just []
    list (List [Atom ":", oneArg, restArgs]) =
      (oneArg :) <$> list restArgs
    list (List [List [Atom "as", Atom ":", _], oneArg, restArgs]) =
      (oneArg :) <$> list restArgs
    list _ = Nothing

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> Value
sexprToVal expr =
  case expr of
    Atom "true" -> Bool True
    Atom "false" -> Bool False
    Atom ('#' : 'b' : ds)
      | Just n <- binLit ds -> Bits (length ds) n
    Atom ('#' : 'x' : ds)
      | [(n, [])] <- readHex ds -> Bits (4 * length ds) n
    Atom txt
      | Just n <- readMaybe txt -> Int n
    List [Atom "-", x]
      | Int a <- sexprToVal x -> Int (negate a)
    List [Atom "/", x, y]
      | Int a <- sexprToVal x,
        Int b <- sexprToVal y ->
        Real (a % b)
    _ -> Other expr
  where
    binLit cs = do
      ds <- mapM binDigit cs
      return $ sum $ zipWith (*) (reverse ds) powers2
    powers2 = 1 : map (2 *) powers2
    binDigit '0' = Just 0
    binDigit '1' = Just 1
    binDigit _ = Nothing

-- | Show an S-expression in a somewhat readbale fashion.
ppSExpr :: SExpr -> ShowS
ppSExpr = go 0
  where
    tab n = showString (replicate n ' ')
    many = foldr (.) id

    new n e = showChar '\n' . tab n . go n e

    small :: Int -> [SExpr] -> Maybe [ShowS]
    small n es =
      case es of
        [] -> Just []
        e : more
          | n <= 0 -> Nothing
          | otherwise -> case e of
            Atom x -> (showString x :) <$> small (n - 1) more
            _ -> Nothing

    go :: Int -> SExpr -> ShowS
    go n ex =
      case ex of
        Atom x -> showString x
        List es
          | Just fs <- small 5 es ->
            showChar '(' . many (intersperse (showChar ' ') fs) . showChar ')'
        List (Atom x : es) ->
          showString "(" . showString x
            . many (map (new (n + 3)) es)
            . showString ")"
        List es -> showString "(" . many (map (new (n + 2)) es) . showString ")"

delta :: Maybe (IO a) -> IO (Maybe a)
delta Nothing = return Nothing
delta (Just something) = do
  thing <- something
  return (Just thing)

bindIOMaybe :: IO (Maybe a) -> (a -> IO (Maybe b)) -> IO (Maybe b)
bindIOMaybe x f = do
  y <- x
  z <- delta $ f <$> y
  return $ do
    z' <- z
    z'

mapIOMaybe :: (a -> b) -> IO (Maybe a) -> IO (Maybe b)
mapIOMaybe f x = fmap (fmap f) x

-- | Parse an s-expression.
readSExpr :: Handle -> String -> IO (Maybe (SExpr, String))
readSExpr h (c : more) | isSpace c = readSExpr h more
readSExpr h (';' : more) = readSExpr h $ drop 1 $ dropWhile (/= '\n') more
readSExpr _ ('|' : more) = return $ do
  (sym, '|' : rest) <- pure (span ('|' /=) more)
  Just (Atom ('|' : sym ++ ['|']), rest)
readSExpr h ('(' : more) =
  mapIOMaybe (\(xs, more1) -> (List xs, more1)) (list h more)
  where
    list h (c : txt) | isSpace c = list h txt
    list _ (')' : txt) = return $ return ([], txt)
    list h txt =
      bindIOMaybe
        (readSExpr h txt)
        ( \(v, txt1) ->
            mapIOMaybe
              (\(vs, txt2) -> (v : vs, txt2))
              (list h txt1)
        )
readSExpr h "" = do
  more <- hGetLine h
  readSExpr h more
readSExpr _ txt = return $ case break end txt of
  (atom, rest) | P.not (null atom) -> Just (Atom atom, rest)
  _ -> Nothing
  where
    end x = x == ')' || isSpace x

-- * Constructing 'SExpr'

-- | A constant, corresponding to a family indexed by some integers.
fam :: String -> [Integer] -> SExpr
fam f is = List (Atom "_" : Atom f : map (Atom . show) is)

-- | An SMT function.
fun :: String -> [SExpr] -> SExpr
fun f [] = Atom f
fun f args = List (Atom f : args)

-- | An SMT constant.  A special case of 'fun'.
const :: String -> SExpr
const f = fun f []

app :: SExpr -> [SExpr] -> SExpr
app f [] = f -- Tweag: fix problematic parenthesis in generated smtlib sexpr
app f xs = List (f : xs)

match :: SExpr -> [(SExpr, SExpr)] -> SExpr
match t cases =
  List
    [ Atom "match",
      t,
      List $ map (\(a, b) -> List [a, b]) cases
    ]

forall :: [(String, SExpr)] -> SExpr -> SExpr
forall vars prop =
  List
    [ Atom "forall",
      List (map (\(s, e) -> List [symbol s, e]) vars),
      prop
    ]

-- Identifiers -----------------------------------------------------------------------

-- | Symbols are either simple or quoted (c.f. SMTLIB v2.6 S3.1).
-- This predicate indicates whether a character is allowed in a simple
-- symbol.  Note that only ASCII letters are allowed.
allowedSimpleChar :: Char -> Bool
allowedSimpleChar c =
  isDigit c || c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ "~!@$%^&*_-+=<>.?/")

isSimpleSymbol :: String -> Bool
isSimpleSymbol s@(c : _) = P.not (isDigit c) && all allowedSimpleChar s
isSimpleSymbol _ = False

quoteSymbol :: String -> String
quoteSymbol s
  | isSimpleSymbol s = s
  | otherwise = '|' : s ++ "|"

symbol :: String -> SExpr
symbol = Atom . quoteSymbol

keyword :: String -> SExpr
keyword s = Atom (':' : s)

-- | Generate a type annotation for a symbol
as :: SExpr -> SExpr -> SExpr
as s t = fun "as" [s, t]

-- Types -----------------------------------------------------------------------

-- | The type of integers.
tInt :: SExpr
tInt = const "Int"

-- | The type of booleans.
tBool :: SExpr
tBool = const "Bool"

-- | The type of reals.
tReal :: SExpr
tReal = const "Real"

-- | The type of tuples
-- Tweag
tTuple :: [SExpr] -> SExpr
tTuple = fun "Tuple"

-- | The unit type (tuple of arity 0)
-- Tweag
tUnit :: SExpr
tUnit = const "Tuple"

-- | The type of strings
-- Tweag
tString :: SExpr
tString = const "String"

-- | The type of arrays.
tArray ::
  -- | Type of indexes
  SExpr ->
  -- | Type of elements
  SExpr ->
  SExpr
tArray x y = fun "Array" [x, y]

-- | The type of bit vectors.
tBits ::
  -- | Number of bits
  Integer ->
  SExpr
tBits w = fam "BitVec" [w]

-- Literals --------------------------------------------------------------------

-- | Boolean literals.
bool :: Bool -> SExpr
bool b = const (if b then "true" else "false")

-- | Integer literals.
int :: Integer -> SExpr
int x
  | x < 0 = neg (int (negate x))
  | otherwise = Atom (show x)

-- | Real (well, rational) literals.
real :: Rational -> SExpr
real x
  | toRational y == x = Atom (showFFloat Nothing y "")
  | otherwise = realDiv (int (numerator x)) (int (denominator x))
  where
    y = fromRational x :: Double

-- | String literals
-- Tweag
string :: String -> SExpr
string str = Atom ("\"" <> str <> "\"")

-- | String literals, from Text
text :: Data.Text.Text -> SExpr
text str = Atom ("\"" <> Data.Text.unpack str <> "\"")

-- | The unit value: a tuple of arity 0
-- Tweag
unit :: SExpr
unit = const "mkTuple"

-- | Create a new tuple
tuple :: [SExpr] -> SExpr
tuple = fun "mkTuple"

tupleSel :: Integer -> SExpr -> SExpr
tupleSel n t = List [fun "_" [Atom "tupSel", int n], t]

-- | A bit vector represented in binary.
--
--     * If the value does not fit in the bits, then the bits will be increased.
--     * The width should be strictly positive.
bvBin ::
  -- | Width, in bits
  Int ->
  -- | Value
  Integer ->
  SExpr
bvBin w v = const ("#b" ++ bits)
  where
    bits = reverse [if testBit v n then '1' else '0' | n <- [0 .. w - 1]]

-- | A bit vector represented in hex.
--
--    * If the value does not fit in the bits, the bits will be increased to
--      the next multiple of 4 that will fit the value.
--    * If the width is not a multiple of 4, it will be rounded
--      up so that it is.
--    * The width should be strictly positive.
bvHex ::
  -- | Width, in bits
  Int ->
  -- | Value
  Integer ->
  SExpr
bvHex w v
  | v >= 0 = const ("#x" ++ padding ++ hex)
  | otherwise = bvHex w (2 ^ w + v)
  where
    hex = showHex v ""
    padding = replicate (P.div (w + 3) 4 - length hex) '0'

-- | Render a value as an expression.  Bit-vectors are rendered in hex,
-- if their width is a multiple of 4, and in binary otherwise.
value :: Value -> SExpr
value val =
  case val of
    Bool b -> bool b
    Int n -> int n
    Real r -> real r
    Bits w v
      | P.mod w 4 == 0 -> bvHex w v
      | otherwise -> bvBin w v
    Other o -> o

-- Connectives -----------------------------------------------------------------

-- | Logical negation.
not :: SExpr -> SExpr
not p = fun "not" [p]

-- | Conjunction.
and :: SExpr -> SExpr -> SExpr
and p q = fun "and" [p, q]

andMany :: [SExpr] -> SExpr
andMany [] = bool True
andMany [x] = x
andMany xs = fun "and" xs

-- | Disjunction.
or :: SExpr -> SExpr -> SExpr
or p q = fun "or" [p, q]

orMany :: [SExpr] -> SExpr
orMany xs = if null xs then bool False else fun "or" xs

-- | Exclusive-or.
xor :: SExpr -> SExpr -> SExpr
xor p q = fun "xor" [p, q]

-- | Implication.
implies :: SExpr -> SExpr -> SExpr
implies p q = fun "=>" [p, q]

-- If-then-else ----------------------------------------------------------------

-- | If-then-else.  This is polymorphic and can be used to construct any term.
ite :: SExpr -> SExpr -> SExpr -> SExpr
ite x y z = fun "ite" [x, y, z]

-- Relations -------------------------------------------------------------------

-- | Equality.
eq :: SExpr -> SExpr -> SExpr
eq x y = fun "=" [x, y]

distinct :: [SExpr] -> SExpr
distinct xs = if null xs then bool True else fun "distinct" xs

-- | Greater-then
gt :: SExpr -> SExpr -> SExpr
gt x y = fun ">" [x, y]

-- | Less-then.
lt :: SExpr -> SExpr -> SExpr
lt x y = fun "<" [x, y]

-- | Greater-than-or-equal-to.
geq :: SExpr -> SExpr -> SExpr
geq x y = fun ">=" [x, y]

-- | Less-than-or-equal-to.
leq :: SExpr -> SExpr -> SExpr
leq x y = fun "<=" [x, y]

-- | Unsigned less-than on bit-vectors.
bvULt :: SExpr -> SExpr -> SExpr
bvULt x y = fun "bvult" [x, y]

-- | Unsigned less-than-or-equal on bit-vectors.
bvULeq :: SExpr -> SExpr -> SExpr
bvULeq x y = fun "bvule" [x, y]

-- | Signed less-than on bit-vectors.
bvSLt :: SExpr -> SExpr -> SExpr
bvSLt x y = fun "bvslt" [x, y]

-- | Signed less-than-or-equal on bit-vectors.
bvSLeq :: SExpr -> SExpr -> SExpr
bvSLeq x y = fun "bvsle" [x, y]

-- | Addition.
-- See also 'bvAdd'
add :: SExpr -> SExpr -> SExpr
add x y = fun "+" [x, y]

addMany :: [SExpr] -> SExpr
addMany xs = if null xs then int 0 else fun "+" xs

-- | Subtraction.
sub :: SExpr -> SExpr -> SExpr
sub x y = fun "-" [x, y]

-- | Arithmetic negation for integers and reals.
-- See also 'bvNeg'.
neg :: SExpr -> SExpr
neg x = fun "-" [x]

-- | Multiplication.
mul :: SExpr -> SExpr -> SExpr
mul x y = fun "*" [x, y]

-- | Absolute value.
abs :: SExpr -> SExpr
abs x = fun "abs" [x]

-- | Integer division.
div :: SExpr -> SExpr -> SExpr
div x y = fun "div" [x, y]

-- | Modulus.
mod :: SExpr -> SExpr -> SExpr
mod x y = fun "mod" [x, y]

-- | Is the number divisible by the given constant.
divisible :: SExpr -> Integer -> SExpr
divisible x n = List [fam "divisible" [n], x]

-- | Division of real numbers.
realDiv :: SExpr -> SExpr -> SExpr
realDiv x y = fun "/" [x, y]

-- | Bit vector concatenation.
concat :: SExpr -> SExpr -> SExpr
concat x y = fun "concat" [x, y]

-- | Extend to the signed equivalent bitvector by @i@ bits
signExtend :: Integer -> SExpr -> SExpr
signExtend i x = List [fam "sign_extend" [i], x]

-- | Extend with zeros to the unsigned equivalent bitvector
-- by @i@ bits
zeroExtend :: Integer -> SExpr -> SExpr
zeroExtend i x = List [fam "zero_extend" [i], x]

-- | Satisfies @toInt x <= x@ (i.e., this is like Haskell's 'floor')
toInt :: SExpr -> SExpr
toInt e = fun "to_int" [e]

-- | Promote an integer to a real
toReal :: SExpr -> SExpr
toReal e = fun "to_real" [e]

-- | Extract a sub-sequence of a bit vector.
extract :: SExpr -> Integer -> Integer -> SExpr
extract x y z = List [fam "extract" [y, z], x]

-- | Bitwise negation.
bvNot :: SExpr -> SExpr
bvNot x = fun "bvnot" [x]

-- | Bitwise conjuction.
bvAnd :: SExpr -> SExpr -> SExpr
bvAnd x y = fun "bvand" [x, y]

-- | Bitwise disjunction.
bvOr :: SExpr -> SExpr -> SExpr
bvOr x y = fun "bvor" [x, y]

-- | Bitwise exclusive or.
bvXOr :: SExpr -> SExpr -> SExpr
bvXOr x y = fun "bvxor" [x, y]

-- | Bit vector arithmetic negation.
bvNeg :: SExpr -> SExpr
bvNeg x = fun "bvneg" [x]

-- | Addition of bit vectors.
bvAdd :: SExpr -> SExpr -> SExpr
bvAdd x y = fun "bvadd" [x, y]

-- | Subtraction of bit vectors.
bvSub :: SExpr -> SExpr -> SExpr
bvSub x y = fun "bvsub" [x, y]

-- | Multiplication of bit vectors.
bvMul :: SExpr -> SExpr -> SExpr
bvMul x y = fun "bvmul" [x, y]

-- | Bit vector unsigned division.
bvUDiv :: SExpr -> SExpr -> SExpr
bvUDiv x y = fun "bvudiv" [x, y]

-- | Bit vector unsigned reminder.
bvURem :: SExpr -> SExpr -> SExpr
bvURem x y = fun "bvurem" [x, y]

-- | Bit vector signed division.
bvSDiv :: SExpr -> SExpr -> SExpr
bvSDiv x y = fun "bvsdiv" [x, y]

-- | Bit vector signed reminder.
bvSRem :: SExpr -> SExpr -> SExpr
bvSRem x y = fun "bvsrem" [x, y]

-- | Shift left.
bvShl ::
  -- | value
  SExpr ->
  -- | shift amount
  SExpr ->
  SExpr
bvShl x y = fun "bvshl" [x, y]

-- | Logical shift right.
bvLShr ::
  -- | value
  SExpr ->
  -- | shift amount
  SExpr ->
  SExpr
bvLShr x y = fun "bvlshr" [x, y]

-- | Arithemti shift right (copies most significant bit).
bvAShr ::
  -- | value
  SExpr ->
  -- | shift amount
  SExpr ->
  SExpr
bvAShr x y = fun "bvashr" [x, y]

-- | Get an elemeent of an array.
select ::
  -- | array
  SExpr ->
  -- | index
  SExpr ->
  SExpr
select x y = fun "select" [x, y]

-- | Update an array
store ::
  -- | array
  SExpr ->
  -- | index
  SExpr ->
  -- | new value
  SExpr ->
  SExpr
store x y z = fun "store" [x, y, z]

--------------------------------------------------------------------------------
-- Attributes

named :: String -> SExpr -> SExpr
named x e = fun "!" [e, Atom ":named", Atom x]
