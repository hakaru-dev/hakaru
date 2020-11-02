{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Text.Parsec.Indentation.Char where

import Text.Parsec.Prim (ParsecT, mkPT, runParsecT,
                         Stream(..),
                         Consumed(..), Reply(..),
                         State(..))
import Text.Parsec.Pos (sourceColumn)
import Text.Parser.Indentation.Implementation (Indentation)

----------------
-- Unicode char
-- newtype UnicodeIndentStream

----------------
-- Based on Char
{-# INLINE mkCharIndentStream #-}
mkCharIndentStream :: s -> CharIndentStream s
mkCharIndentStream s = CharIndentStream 1 s
data CharIndentStream s = CharIndentStream { charIndentStreamColumn :: {-# UNPACK #-} !Indentation,
                                             charIndentStreamStream :: !s } deriving (Show)

instance (Stream s m Char) => Stream (CharIndentStream s) m (Char, Indentation) where
  uncons (CharIndentStream i s) = do
    x <- uncons s
    case x of
      Nothing -> return Nothing
      Just (c, cs) -> return (Just ((c, i), CharIndentStream (updateColumn i c) cs))

{-# INLINE updateColumn #-}
updateColumn :: Integral a => a -> Char -> a
updateColumn _ '\n' = 1
updateColumn i '\t' = i + 8 - ((i-1) `mod` 8)
updateColumn i _    = i + 1

{-# INLINE charIndentStreamParser #-}
charIndentStreamParser :: (Monad m) => ParsecT s u m t -> ParsecT (CharIndentStream s) u m (t, Indentation)
charIndentStreamParser p = mkPT $ \state ->
  let go (Ok a state' e) = return (Ok (a, sourceColumn $ statePos state) (state' { stateInput = CharIndentStream (sourceColumn $ statePos state') (stateInput state') }) e)
      go (Error e) = return (Error e)
  in runParsecT p (state { stateInput = charIndentStreamStream (stateInput state) })
         >>= consumed (return . Consumed . go) (return . Empty . go)

{-# INLINE consumed #-}
consumed :: (Monad m) => (a -> m b) -> (a -> m b) -> Consumed (m a) -> m b
consumed c _ (Consumed m) = m >>= c
consumed _ e (Empty m)    = m >>= e
