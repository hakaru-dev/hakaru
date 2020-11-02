module Text.Parser.Indentation.Implementation where

-- Implements common code for "Indentation Senstivie Parising: Landin Revisited"
--
-- Primary functions are:
--  - TODO
-- Primary driver functions are:
--  - TODO

-- TODO:
--   Grace style indentation stream
--   Haskell style indentation stream

--import Control.Monad

------------------------
-- Indentations
------------------------

-- We use indent 1 for the first column.  Not only is this consistent
-- with how Parsec counts columns, but it also allows 'Gt' to refer to
-- the first column by setting the indent to 0.
--data Indentation = Indentation# Int# deriving (Eq, Ord)
type Indentation = Int
data IndentationRel = Eq | Any | Const Indentation | Ge | Gt deriving (Show, Eq)

{-# INLINE infIndentation #-}
infIndentation :: Indentation
infIndentation = maxBound

{-
instance Num Indentation where

instance Show Indentation where
  show i@(Indentation# i') | i' == maxBound = "Infinity"
                           | otherwise = show (Int# i')
-}

------------------------
-- Indentable Stream
------------------------

-- We store state information about the current indentation in the
-- Stream.  Encoding the indentation state in the Stream is weird, but
-- the other two places where we could put it don't work.  The monad
-- isn't rolledback when backtracking happens (which we need the
-- indentation state to do), and the user state isn't available when
-- we do an 'uncons'.

{-# INLINE mkIndentationState #-}
mkIndentationState :: Indentation -> Indentation -> Bool -> IndentationRel -> IndentationState
mkIndentationState lo hi mode rel
  | lo == infIndentation = error "mkIndentationState: minimum indentation 'infIndentation' is out of bounds"
  | lo > hi = error "mkIndentationState: minimum indentation is greater than maximum indent"
  | otherwise = IndentationState lo hi mode rel

-- THEOREM: indent sets are all describable by upper and lower bounds (maxBound is infinity)
-- GLOBAL INVARIANT: minIndentation /= infIndentation
-- GLOBAL INVARIANT: minIndentation <= maxIndentation
-- GLOBAL INVARIENT: lo <= lo' where lo and lo' are minIndentation respectively before and after a monadic action
-- GLOBAL INVARIENT: hi' <= hi where hi and hi' are maxIndentation respectively before and after a monadic action

data IndentationState = IndentationState {
  minIndentation :: {-# UNPACK #-} !Indentation, -- inclusive, must not equal infIndentation
  maxIndentation :: {-# UNPACK #-} !Indentation, -- inclusive, infIndentation (i.e., maxBound) means infinity
  absMode :: !Bool, -- true if we are in 'absolute' mode
  tokenRel :: !IndentationRel
  } deriving (Show)
  -- Our representation of maxIndentation will get us in trouble if things
  -- overflow.  In future we may want to use a type representing
  -- Integer+Infinity However, this bug triggers *only* when there are
  -- a large number of nested 'Gt' indentations which shouldn't be all
  -- that common and 'local'

{-# INLINE indentationStateAbsMode #-}
indentationStateAbsMode :: IndentationState -> Bool
indentationStateAbsMode x = absMode x

{-# INLINE updateIndentation #-}
-- PRIVATE: Use assertIndentation instead
updateIndentation :: IndentationState -> Indentation -> (IndentationState -> a) -> (String -> a) -> a
updateIndentation (IndentationState lo hi mode rel) i ok err = updateIndentation' lo hi (if mode then Eq else rel) i ok' err' where
  ok' lo' hi' = ok (IndentationState lo' hi' False rel)
  err' = err

{-# INLINE updateIndentation' #-}
updateIndentation' :: Indentation -> Indentation -> IndentationRel -> Indentation -> (Indentation -> Indentation -> a) -> (String -> a) -> a
updateIndentation' lo hi rel i ok err =
  case rel of
    Any                          -> ok lo hi
    Const c | c  == i            -> ok lo hi
            | otherwise          -> err' $ "indentation "++show c
    Eq      | lo <= i && i <= hi -> ok i i
            | otherwise          -> err' $ "an indentation between "++show lo++" and "++show hi
    Gt      | lo <  i            -> ok lo (min (i-1) hi)
            | otherwise          -> err' $ "an indentation greater than "++show lo
    Ge      | lo <= i            -> ok lo (min i hi)
            | otherwise          -> err' $ "an indentation greater than or equal to "++show lo
  where err' place = err $ "Found a token at indentation "++show i++".  Expecting a token at "++place++"."

-- TODO: error when hi is maxIndentation

-- There is no way to query the current indentation because multiple
-- indentations are tried in parallel and later parsing may disqualify
-- one of these indentations.  However, we can assert that the current
-- indentation must have a particular relation, 'r', to a given
-- indentation, 'i'.  The call 'assertIndent r i' does this.  Calling
-- 'assertIndent r i' is equivalent to consuming a pseudo-token that has
-- been annotated with the relation 'r' at indentation 'i'.
--
-- Note that the absolute indentation mode may override 'r'.
{-
assertIndent :: (Monad m, Stream (IndentStream s) m t) => IndentRel -> Indent -> ParsecT (IndentStream s) u m ()
assertIndent r i = do
  IndentStream lo hi mode rel s <- getInput
  let ok s' = setInput (s' { absMode = mode }) -- Update input sets mode to False by default
      --ok lo' hi' = setInput (IndentStream lo' hi' mode rel s)
      err msg = unexpected $ "Indentation assertion '"++show r++" "++show i++"' failed.  "++msg
  updateIndent lo hi mode r i s ok err
  --updateIndent lo hi (if mode then Eq else r) i ok err
-}

{-
{-# INLINE askTokenMode #-}
askTokenMode :: (Monad m) => ParsecT (IndentStream s) u m IndentRel
askTokenMode = liftM tokenRel getInput
-}

------------------------
-- Token Modes
------------------------

-- Token modes determine how the current indentation must relate to
-- the indentation of a token.  Because several languages have special
-- rules for the first token of the production, we split the token
-- mode into two parts.  The first part is the mode for the first
-- token in a grammatical form while the second part is the mode for
-- the other tokens in a grammatical form.
--
-- Because of this split, while token modes generally follow a reader
-- monad pattern, there is one important exception.  Namely the
-- first-token mode may follow a state monad pattern.  (Thus we have
-- the divergent names for the first-token and other-token query
-- operators.)

-- THEOREM: tokenMode == tokenMode'
-- THEOREM: firstTokenMode' == firstTokenMode \/ firstTokenMode' == otherTokenMode

type LocalState a = (IndentationState -> IndentationState) -- pre
                  -> (IndentationState {-old-} -> IndentationState {-new-} -> IndentationState) -- post
                  -> a -> a

{-# INLINE localTokenMode #-}
localTokenMode :: (LocalState a)
               -> (IndentationRel -> IndentationRel)
               -> a -> a
localTokenMode localState f_rel = localState pre post where
  pre  i1    = i1 { tokenRel = f_rel (tokenRel i1) }
  post i1 i2 = i2 { tokenRel =        tokenRel i1  }

{-# INLINE absoluteIndentation #-}
absoluteIndentation :: LocalState a -> a -> a
absoluteIndentation localState = localState pre post where
  pre  i1    = i1 { absMode = True }
  post i1 i2 = i2 { absMode = absMode i1 && absMode i2 }

{-# INLINE ignoreAbsoluteIndentation #-}
ignoreAbsoluteIndentation :: LocalState a -> a -> a
ignoreAbsoluteIndentation localState = localState pre post where
  pre  i1    = i1 { absMode = False }
  post i1 i2 = i2 { absMode = absMode i1 }

{-# INLINE localAbsoluteIndentation #-}
localAbsoluteIndentation :: LocalState a -> a -> a
localAbsoluteIndentation localState = localState pre post where
  pre  i1    = i1 { absMode = True }
  post i1 i2 = i2 { absMode = absMode i1 }

--{-# INLINE askTokenMode #-}
--askTokenMode :: (Monad m) => ParsecT (IndentationStream s) u m IndentationRel
--askTokenMode = liftM tokenRel getInput
-- TODO: assertNotAbsMod/askAbsMode
-- when (absMode i2) (fail "absoluteIndentation: no tokens consumed") >>

------------------------
-- Local Indentations
------------------------

{-# INLINE localIndentation' #-}
-- PRIVATE: locally violates global invariants but used in a way that does not
localIndentation' :: LocalState a -> (Indentation -> Indentation) -> (Indentation -> Indentation) -> (Indentation -> Indentation -> Indentation) -> a -> a
localIndentation' localState f_lo f_hi f_hi' m = localState pre post m
  where pre (IndentationState lo hi mode rel) = IndentationState (f_lo lo) (f_hi hi) mode rel
        post (IndentationState lo hi _ _) i2 = i2 { minIndentation = lo, maxIndentation = f_hi' hi (maxIndentation i2) }
--        post (IndentationStream lo hi mode rel s) i2 = IndentationStream lo (f_hi' hi (maxIndentation i2)) mode rel s

-- 'localIndentation r p' specifies that the current indentation for 'p' must have relation 'r'
-- relative to the current indentation of the context in which 'localIndentation r p' is called.
{-# INLINE localIndentation #-}
-- NOTE: it is the responsibility of 'localState' to *not* use it's arguments if we are in absMode
localIndentation :: LocalState a -> IndentationRel -> a -> a
localIndentation _localState Eq m = m
localIndentation localState Any m = localIndentation' localState (const 0) (const infIndentation) (const) m
localIndentation localState (Const c) m
    | c == infIndentation = error "localIndentation: Const indentation 'infIndentation' is out of bounds"
    | otherwise = localIndentation' localState (const c) (const c) (const) m
localIndentation localState Ge m = localIndentation' localState (id) (const infIndentation) (flip const) m
localIndentation localState Gt m = localIndentation' localState (+1) (const infIndentation) (f) ({-TODO: checkOverflow >>-} m) where
  f hi hi' | hi' == infIndentation || hi < hi' = hi
           | hi' > 0 = hi' - 1 -- Safe only b/c hi' > 0
           | otherwise = error "localIndentation: assertion failed: hi' > 0"
{-
  checkOverflow = do
    IndentationStream { minIndentation = lo } <- getState
    when (lo == infIndentation) $ fail "localIndentation: Overflow in indentation lower bound."
-}

----------------
-- SourcePos

{-
mkSourcePosIndentStream s = SourcePosIndentStream s
newtype SourcePosIndentStream s = SourcePosIndentStream s
instance (Stream s m t) => Stream (SourcePosIndentStream s) m (Indent, t) where
  uncons (SourcePosIndentStream s) = do
    col <- liftM sourceColumn $ getPosition
    x <- uncons s
    case x of
      Nothing -> return Nothing
      Just x -> return (Just ((col, x), SourcePosIndentStream s))
-}

----------------
-- Unicode char
-- newtype UnicodeIndentStream

{-
----------------
-- Based on Char
mkCharIndentStream :: s -> CharIndentStream s
mkCharIndentStream s = CharIndentStream 1 s
data CharIndentStream s = CharIndentStream { charIndentStreamColumn :: !Indent,
                                             charIndentStreamStream :: s } deriving (Show)

instance (Stream s m Char) => Stream (CharIndentStream s) m (Indent, Char) where
  uncons (CharIndentStream i s) = do
    x <- uncons s
    case x of
      Nothing -> return Nothing
      Just (c, cs) -> return (Just ((i, c), CharIndentStream (f c) cs)) where
        f '\n' = 1
        f '\t' = i + 8 - ((i-1) `mod` 8)
        f _    = i + 1

charIndentStreamParser :: (Monad m) => ParsecT s u m t -> ParsecT (CharIndentStream s) u m (Indent, t)
charIndentStreamParser p = mkPT $ \state ->
  let go (Ok a state' e) = return (Ok (sourceColumn $ statePos state, a) (state' { stateInput = CharIndentStream (sourceColumn $ statePos state') (stateInput state') }) e)
      go (Error e) = return (Error e)
  in runParsecT p (state { stateInput = charIndentStreamStream (stateInput state) })
         >>= consumed (return . Consumed . go) (return . Empty . go)

----------------
-- TODO: parser based on first non-whitespace char

----------------
-- First token of line indents

----------------
-- Based on Indents

-- Note that if 'p' consumes input but is at the wrong indentation, then
-- 'indentStreamParser p' signals an error but does *not* consume input.
-- This allows Parsec primitives like 'string' to be properly backtracked.
indentStreamParser :: (Monad m) => ParsecT s u m (Indent, t) -> ParsecT (IndentStream s) u m t
indentStreamParser p = mkPT $ \state ->
  let IndentStream lo hi mode rel _ = stateInput state
      go f (Ok (i, a) state' e) = updateIndent lo hi (if mode then Eq else rel) i ok err where
        ok lo' hi' = return $ f $ return (Ok a (state' {stateInput = IndentStream lo' hi' False rel (stateInput state') }) e)
        err msg = return $ Empty $ return $ Error (Message ("Invalid indentation.  "++msg++show ((stateInput state) { tokenStream = ""})) `addErrorMessage` e)
      go f (Error e) = return $ f $ return (Error e)
  in runParsecT p (state { stateInput = tokenStream (stateInput state) }) >>= consumed (go Consumed) (go Empty)

-- lifting operator
-- token, tokens, tokenPrim, tokenPrimEx ???
-- whiteSpace
-- ByteString
-- ByteString.Lazy
-- Text

delimitedLayout :: Stream (IndentStream s) m t =>
  ParsecT (IndentStream s) u m open -> Bool ->
  ParsecT (IndentStream s) u m close -> Bool ->
  ParsecT (IndentStream s) u m a -> ParsecT (IndentStream s) u m a
delimitedLayout open openAny close closeAny body = between open' close' (localIndent (Const 0) body) where
  open'  | openAny = localIndent (Const 0) open
         | otherwise = open
  close' | closeAny = localIndent (Const 0) close
         | otherwise = close

indentedLayout :: Stream (IndentStream s) m t =>
  (Maybe (ParsecT (IndentStream s) u m sep)) ->
  ParsecT (IndentStream s) u m a -> ParsecT (IndentStream s) u m [a]
indentedLayout (Nothing ) clause = localIndent Gt $ many $ absoluteIndent $ clause
indentedLayout (Just sep) clause = liftM concat $ localIndent Gt $ many $ absoluteIndent $ sepBy1 clause sep

{-
layout p = delimitedLayout (symbol "{") False (symbol "}") True (semiSep p)
       <|> indentedLayout (Just semi) p

identifier pred = liftM fromString $ try $ identifier >>= \x -> guard (pred x) >> return x
operator pred = liftM fromString $ try $ operator >>= \x -> guard (pred x) >> return x

reserved name = (if name `elem` middleKeywords then localFirstTokenMode (const Ge) else id) $ reserved name

Numbers, Integers and Naturals are custom

dotSep
dotSep1

-}

{-
test :: String
test = foo where
          foo = "abc \
\def" ++ ""

test2 :: Int
test2 = foo where
          foo = let { x = 1;
 } in x


--- All code indented?
  foo = 3
  bar = 4
-}
-}
