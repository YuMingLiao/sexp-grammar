{
{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing     #-}
{-# OPTIONS_GHC -fno-warn-tabs               #-}
{-# OPTIONS_GHC -fno-warn-unused-binds       #-}
{-# OPTIONS_GHC -fno-warn-unused-imports     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches     #-}

module Language.Sexp.Lexer
  ( lexSexp
  ) where

import Data.Bifunctor
import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Text.Lazy.Encoding (decodeUtf8)
import Data.Text.Read
import Data.Scientific (Scientific)

import Language.Sexp.LexerInterface
import Language.Sexp.Token
import Language.Sexp.Types (Position (..), LocatedBy (..))

}

$hspace     = [\ \t]
$whitespace = [$hspace\n\r\f\v]

$allgraphic = . # [\x00-\x20 \x7F-\xA0]

$digit      = 0-9
$hex        = [0-9 A-F a-f]
$alpha      = [a-z A-Z]

@number     = [\-\+]? $digit+ ([\.]$digit+)? ([eE] [\-\+]? $digit+)?

@escape     = \\ [nrt\\\"]
@string     = $allgraphic # [\"\\] | $whitespace | @escape

$unicode    = $allgraphic # [\x20-\x80]

$syminitial = [$alpha \:\@\!\$\%\&\*\/\<\=\>\?\~\_\^\.\|\+\- $unicode]
$symsubseq  = [$syminitial $digit \#\'\`\,]
@symescape  = \\ [$alpha $digit \(\)\[\]\{\}\\\|\;\'\`\"\#\.\,]
@symbol     = ($syminitial | @symescape) ($symsubseq | @symescape)*

:-

$whitespace+       ;
";" .*             ;

"("                { just TokLParen   }
")"                { just TokRParen   }
"["                { just TokLBracket }
"]"                { just TokRBracket }
"{"                { just TokLBrace   }
"}"                { just TokRBrace   }

"'" / $allgraphic  { just (TokPrefix Quote)    }
"`" / $allgraphic  { just (TokPrefix Backtick) }
",@" / $allgraphic { just (TokPrefix CommaAt)  }
"," / $allgraphic  { just (TokPrefix Comma)    }
"#" / $allgraphic  { just (TokPrefix Hash)     }

@number            { TokNumber  `via` readNum    }
@symbol            { TokSymbol  `via` decode     }
\" @string* \"     { TokString  `via` readString }

.                  { TokUnknown `via` BL.head    }

{

type AlexAction = LineCol -> ByteString -> LocatedBy LineCol Token

readString :: ByteString -> T.Text
readString = TL.toStrict . unescape . TL.tail . TL.init . decodeUtf8

readNum :: ByteString -> Scientific
readNum = read . TL.unpack . decodeUtf8

decode :: ByteString -> T.Text
decode = TL.toStrict . decodeUtf8

just :: Token -> AlexAction
just tok pos _ =
  pos :< tok

via :: (a -> Token) -> (ByteString -> a) -> AlexAction
via ftok f pos str =
  (pos :<) . ftok . f $ str

alexScanTokens :: AlexInput -> [LocatedBy LineCol Token]
alexScanTokens input =
  case alexScan input defaultCode of
    AlexEOF -> []
    AlexError (AlexInput {aiInput, aiLineCol = LineCol line col}) ->
      error $ "Lexical error at line " ++ show line ++ " column " ++ show col ++
        ". Remaining input: " ++ show (UTF8.take 200 aiInput)
    AlexSkip input _ -> alexScanTokens input
    AlexToken input' tokLen action ->
      action inputPosn inputText : alexScanTokens input'
      where
        inputPosn = aiLineCol input
        inputText = UTF8.take (fromIntegral tokLen) (aiInput input)
  where
    defaultCode :: Int
    defaultCode = 0

lexSexp :: Position -> ByteString -> [LocatedBy Position Token]
lexSexp (Position fn line1 col1) =
  map (bimap fixPos id) . alexScanTokens . mkAlexInput (LineCol line1 col1)
  where
    fixPos (LineCol l c) = Position fn l c
}
