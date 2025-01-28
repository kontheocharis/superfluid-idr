module Surface.Parsing

import Surface.Presyntax
import Common
import Context

import Control.Monad.Trans
import Data.List
import Data.String
import Data.DPair

-- Setup:

public export
data ParseError : Type where
  TrailingChars : ParseError
  Empty : ParseError
  EndOfInput : ParseError
  UnexpectedChar : Char -> ParseError

public export
Show ParseError where
  show TrailingChars = "Trailing characters"
  show Empty = "Empty input"
  show EndOfInput = "Unexpected end of input"
  show (UnexpectedChar c) = "Unexpected character: " ++ show c

public export
record Parser (a : Type) where
  constructor MkParser
  runParser : List Char -> Either ParseError (a, List Char)

public export
parse : Parser a -> String -> Either ParseError a
parse p s = case runParser p (unpack s) of
  Left s => Left s
  Right (a, []) => Right a
  Right (_, _) => Left TrailingChars

Functor Parser where
  map f p = MkParser $ \ts => case runParser p ts of
    Left s => Left s
    Right (a, ts') => Right (f a, ts')

Applicative Parser where
  pure a = MkParser $ \ts => Right (a, ts)
  (<*>) f x = MkParser $ \ts => case runParser f ts of
    Left s => Left s
    Right (f', ts') => case runParser x ts' of
      Left s => Left s
      Right (x', ts'') => Right (f' x', ts'')

Monad Parser where
  (>>=) f p = MkParser $ \ts => case runParser f ts of
    Left s => Left s
    Right (a, ts') => runParser (p a) ts'

Alternative Parser where
  empty = MkParser $ \ts => Left Empty
  (<|>) p q = MkParser $ \ts => case runParser p ts of
    Left _ => runParser q ts
    Right (a, ts') => Right (a, ts')

fail : ParseError -> Parser a
fail s = MkParser $ \ts => Left s

optional : Parser a -> Parser (Maybe a)
optional p = MkParser $ \ts => case runParser p ts of
  Left _ => Right (Nothing, ts)
  Right (a, ts') => Right (Just a, ts')

peek : Parser (Maybe Char)
peek = MkParser $ \ts => case ts of
  [] => Right (Nothing, ts)
  (c :: _) => Right (Just c, ts)

satisfy : (Char -> Bool) -> Parser Char
satisfy p = MkParser $ \ts => case ts of
  [] => Left EndOfInput
  (c :: cs) => if p c
    then Right (c, cs)
    else Left $ UnexpectedChar c

char : Char -> Parser ()
char c = satisfy (== c) *> pure ()

many : Parser a -> Parser (List a)
many p = MkParser $ \ts => case runParser p ts of
  Left _ => Right ([], ts)
  Right (a, ts') => case runParser (many p) ts' of
      Left _ => Right ([a], ts')
      Right (as, ts'') => Right (a :: as, ts'')

many1 : Parser a -> Parser (DPair (List a) NonEmpty)
many1 p = do
  a <- p
  as <- many p
  pure ((a :: as) ** IsNonEmpty)

between : Parser a -> Parser b -> Parser c -> Parser c
between l r p = do
  _ <- l
  a <- p
  _ <- r
  pure a

sepBy : Parser a -> Parser b -> Parser (List b)
sepBy sep p = do
  a <- p
  as <- many $ do
    _ <- sep
    p
  pure (a :: as)

whitespace : Parser ()
whitespace = many (satisfy isSpace) *> pure ()

atom : Parser a -> Parser a
atom p = p <* whitespace

string : String -> Parser ()
string s = traverse_ char (unpack s)

symbol : String -> Parser ()
symbol s = atom $ string s

parens : Parser a -> Parser a
parens p = between (symbol "(") (symbol ")") p

-- Actual language:

ident : Parser String
ident = do
  c <- satisfy isAlpha
  cs <- many $ satisfy (\c => isAlphaNum c || c == '-' || c == '_')
  pure $ pack (c :: cs)

public export
tm : Parser PTm

singleTm : Parser PTm

name : Parser Name
name = atom $ MkName <$> ident

param : Parser (Name, PTy)
param = atom . parens $ do
  n <- name
  symbol ":"
  t <- tm
  pure (n, t)

tel : Parser (DPair (List (Name, PTy)) NonEmpty)
tel = many1 param

lam : Parser PTm
lam = atom $ do
  symbol "\\"
  ns <- (Left <$> tel) <|> (Right <$> many1 name)
  symbol "=>"
  t <- tm
  case ns of
    Left ns => pure $ foldr (\(n, ty) => \t => PLam n (Just ty) t) t ns.fst
    Right ns => pure $ foldr (\n => \t => PLam n Nothing t) t ns.fst

app : Parser PTm
app = atom $ do
  f <- singleTm
  xs <- many1 singleTm
  pure $ pApps f (cast xs.fst)

pi : Parser PTm
pi = atom $ do
  ns <- tel
  symbol "->"
  t <- tm
  pure $ foldr (\(n, ty) => \t => PPi n ty t) t ns.fst

u : Parser PTm
u = atom $ symbol "U" *> pure PU

letIn : Parser PTm
letIn = atom $ do
  symbol "let"
  n <- name
  ty <- optional $ do
    symbol ":"
    tm
  symbol "="
  a <- tm
  symbol ";"
  b <- tm
  pure $ PLet n ty a b

tm = lam <|> pi <|> letIn <|> app <|> singleTm

singleTm = u <|> (PName <$> name) <|> parens tm
