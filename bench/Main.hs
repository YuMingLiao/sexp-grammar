{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}

import Criterion.Main

import Prelude hiding ((.), id)

import Control.Arrow
import Control.Category
import Control.DeepSeq
import Control.Exception

import qualified Data.Map as M
import Data.Data (Data, Typeable)
import qualified Data.Text as TS
import qualified Data.Text.Lazy as TL
import GHC.Generics (Generic)

import Language.Sexp (Sexp, Atom, Kw, Position, dummyPos)
import Language.SexpGrammar
import Language.SexpGrammar.TH

newtype Ident = Ident String
  deriving (Show, Eq, Generic)

data Expr
  = Var Ident
  | Lit Int
  | Add Expr Expr
  | Mul Expr Expr
  | Inv Expr
  | IfZero Expr Expr (Maybe Expr)
  | Apply [Expr] String Prim -- inconvenient ordering: arguments, useless annotation, identifier
    deriving (Show, Eq, Generic)

data Prim
  = SquareRoot
  | Factorial
  | Fibonacci
    deriving (Show, Eq, Enum, Bounded, Data, Typeable, Generic)

instance NFData Ident
instance NFData Prim
instance NFData Expr

instance NFData Atom
instance NFData Kw
instance NFData Position
instance NFData Sexp

return []

type SexpG a = forall t. Grammar Position (Sexp :- t) (a :- t)

instance SexpIso Prim where
  sexpIso = enum

instance SexpIso Ident where
  sexpIso = $(match ''Ident)
    (\_Ident -> _Ident . symbol')

exprGrammarTH :: SexpG Expr
exprGrammarTH = go
  where
    go :: SexpG Expr
    go = $(match ''Expr)
      (\_Var -> _Var . sexpIso)
      (\_Lit -> _Lit . int)
      (\_Add -> _Add . list (el (sym "+") >>> el go >>> el go))
      (\_Mul -> _Mul . list (el (sym "*") >>> el go >>> el go))
      (\_Inv -> _Inv . list (el (sym "invert") >>> el go))
      (\_IfZero -> _IfZero . list (el (sym "cond") >>> props ( Kw "pred"  .:  go
                                                           >>> Kw "true"  .:  go
                                                           >>> Kw "false" .:? go )))
      (\_Apply -> _Apply .              -- Convert prim :- "dummy" :- args :- () to Apply node
          list
           (el (sexpIso :: SexpG Prim) >>>       -- Push prim:       prim :- ()
            el (kw (Kw "args")) >>>              -- Recognize :args, push nothing
            rest (go :: SexpG Expr) >>>     -- Push args:       args :- prim :- ()
            Traverse (
               swap >>>                             -- Swap:            prim :- args :- ()
               push "dummy" >>>                     -- Push "dummy":    "dummy" :- prim :- args :- ()
               swap)                                -- Swap:            prim :- "dummy" :- args :- ()
           ))

data SexpTag a
  = ListStartsWithSym TS.Text
  | SomeAtom
  | Other
  deriving (Eq, Ord)

tagSexp :: [TS.Text] -> Sexp -> SexpTag Sexp
tagSexp specials sexp = case sexp of
  List _ (Atom _ (AtomSymbol s) : _) | s `elem` specials -> ListStartsWithSym s
  Atom _ _ -> SomeAtom
  _ -> Other

exprGrammarOctopus:: SexpG Expr
exprGrammarOctopus = go
  where
    go :: SexpG Expr
    go = octopus (tagSexp ["+", "*", "invert", "cond"]) tag
      [ ( SomeAtom
        , tag (Var undefined)
        , $(grammarFor 'Var) . sexpIso
        )
      , ( SomeAtom
        , tag (Lit undefined)
        , $(grammarFor 'Lit) . int
        )
      , ( ListStartsWithSym "+"
        , tag (Add undefined undefined)
        , $(grammarFor 'Add) . list (el (sym "+") >>> el go >>> el go)
        )
      , ( ListStartsWithSym "*"
        , tag (Mul undefined undefined)
        , $(grammarFor 'Mul) . list (el (sym "*") >>> el go >>> el go)
        )
      , ( ListStartsWithSym "invert"
        , tag (Inv undefined)
        , $(grammarFor 'Inv) . list (el (sym "invert") >>> el go)
        )
      , ( ListStartsWithSym "cond"
        , tag (IfZero undefined undefined undefined)
        , $(grammarFor 'IfZero) . list (
              el (sym "cond") >>>
              props ( Kw "pred"  .:  go >>>
                      Kw "true"  .:  go >>>
                      Kw "false" .:? go))
        )
      , ( Other
        , tag (Apply undefined undefined undefined)
        , $(grammarFor 'Apply) .
          list (
            el (sexpIso :: SexpG Prim) >>>
            el (kw (Kw "args")) >>>
            rest go >>>
            Traverse (swap >>> push "dummy" >>> swap))
        )
      ]

parseExpr :: Sexp -> Either String Expr
parseExpr = parseSexp exprGrammarTH

genExpr :: Expr -> Either String Sexp
genExpr = genSexp exprGrammarTH

parseExprO :: Sexp -> Either String Expr
parseExprO = parseSexp exprGrammarOctopus

genExprO :: Expr -> Either String Sexp
genExprO = genSexp exprGrammarOctopus


expr :: TL.Text -> Expr
expr = either error id . decodeWith exprGrammarTH

ellipsis :: Int -> String -> String
ellipsis n str =
  if length str - 3 > n then take (n - 3) str ++ "..." else str

benchCases :: [(String, TL.Text)]
benchCases = map (\a -> ("expression, size " ++ show (TL.length a), a))
  [ "(+ 1 20)"
  , "(+ (* 2 20) 0)"
  , "(+ (* 3 20) (+ 10 20))"
  , "(+ (* (+ 4 20) (* 10 20)) 0)"
  , "(+ (* (+ 5 20) (* 10 20)) (+ 10 20))"
  , "(+ (* (+ 6 20) (* 10 20)) (+ (+ 10 20) 0))"
  , "(+ (* (+ 7 20) (* 10 20)) (+ (+ 10 20) (+ 10 20)))"
  , "(cond :pred (+ 42 x) :false (fibonacci :args 3) :true (factorial :args (* 10 (+ 1 2))))"
  , "(invert (* (+ (cond :pred (+ 42 314) :false (fibonacci :args 3) :true (factorial :args (* 10 (+ 1 2)))) (cond :pred (+ 42 28) :false (fibonacci :args 3) :true (factorial :args (* 10 (+ 1 2))))) (+ (cond :pred (+ 42 314) :false (fibonacci :args 3) :true (factorial :args (* 10 (+ foo bar)))) (cond :pred (+ 42 314) :false (fibonacci :args 3) :true (factorial :args (* 10 (+ 1 2)))))))"
  ]

mkBenchmark :: String -> TL.Text -> IO Benchmark
mkBenchmark name str = do
  expr <- evaluate $ force $ expr str
  sexp <- evaluate $ force $ either error id (genExpr expr)
  return $ bgroup name
    [ bench "gen"    $ nf genExpr expr
    , bench "genO"   $ nf genExprO expr
    , bench "parse"  $ nf parseExpr sexp
    , bench "parseO" $ nf parseExprO sexp
    ]

main :: IO ()
main = do
  cases <- mapM (uncurry mkBenchmark) benchCases
  defaultMain cases
