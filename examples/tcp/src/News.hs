{-# LANGUAGE OverloadedStrings #-}

module News where

import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as S

import Control.Monad.State.Strict 
import Data.Hashable (Hashable)

import qualified Data.ByteString.Char8 as B
import Data.Char (toLower, isLower)
import System.Directory
import System.FilePath

import qualified Data.Vector.Unboxed as V
import Data.Vector.Unboxed (Vector)
import Control.Monad.Identity (runIdentity)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List (foldl')

-- import Filesystem.Path.Internal.FilePath (FilePath)

-- | An 'Encoding a' is a bijection from some set of values from 'a' to 'Int's '[0..(n-1)]'. 
-- 'Encoding n xs h' has the following invariants:
-- * length xs == H.size h == n
-- * n>0 => H.lookup (head xs) h == Just (n-1)
-- * n>0 => H.lookup (last xs) h == Just 0
data Encoding a = Encoding 
  Int              -- The number of entries
  [a]              -- The decoded values
  (HashMap a Int)  -- The integer encoding
    deriving Show

type EncodeState k a = StateT (Encoding k) IO a

empty :: Encoding a
empty = Encoding 0 [] H.empty

run :: Monad m => StateT (Encoding k) m a -> m a
run x = evalStateT x empty

encode :: (Eq k, Hashable k, Monad m) => k -> StateT (Encoding k) m Int
encode x = do
  Encoding n xs h <- get
  case H.lookup x h of
    -- If 'x' has already been seen, just return the code
    Just k -> return k

    -- If not, update the encoding and return the code
    Nothing -> do
      put $ Encoding (n+1) (x:xs) (H.insert x n h)
      return n

dropHeader :: B.ByteString -> B.ByteString
dropHeader = B.unlines . dropWhile (/= "") . B.lines

tokenize :: B.ByteString -> [B.ByteString]
tokenize = filter (not . isStopword) . B.splitWith (not . isLower) . B.map toLower


encodeFile :: FilePath -> EncodeState B.ByteString [Int]
encodeFile fname = do
  ws <- liftIO 
    . fmap (tokenize . dropHeader) 
    . B.readFile $ fname 
  traverse encode ws

encodeDir :: FilePath -> EncodeState B.ByteString [[Int]]
encodeDir path = do
  fnames <- liftIO $ do
    names <- listDirectory path
    filterM doesFileExist $ map (path </>) names
  traverse encodeFile fnames

encodeDirs :: FilePath -> EncodeState B.ByteString [[[Int]]]
encodeDirs path = do
  dnames <- liftIO $ do
    names <- listDirectory path
    filterM doesDirectoryExist $ map (path </>) names
  traverse encodeDir dnames

-- path = "/home/chad/git/iu/hakaru/examples/naive_bayes/20_newsgroups"
path = "20_newsgroups/"

-- | Map 'Int's to a new set of contiguous values (remove the holes) 
recode :: [[[Int]]] -> [[[Int]]]
recode = runIdentity . run . (traverse . traverse . traverse $ encode)

removeSingletons :: [[[Int]]] -> [[[Int]]]
removeSingletons xs = recode . map (map $ filter notSingle) $ xs
  where
  notSingle x = IntSet.notMember x singletons
  singletons = IntMap.keysSet . IntMap.filter (== 1) $ counts
  counts = foldl' f IntMap.empty . concat . concat $ xs
    where f m x = let  m' = IntMap.insertWith (+) x 1 m
                       Just v = IntMap.lookup x m'
                  in v `seq` m'

asArrays :: [[[Int]]] -> (Vector Int, Vector Int, Vector Int)
asArrays groupList = (wordIndices, docIndices, topicIndices)
  where
  docList = concat groupList
  docIndices = V.fromList . concat $ zipWith replicate (map length docList) [0..]
  wordIndices = V.fromList . concat $ docList
  topicIndices = V.fromList . map (sum . map length) $ groupList

-- | 'xs !!! ks == [xs !! k | k <- ks]', but avoids multiple traversals
-- 'ks' is assumed to be increasing
(!!!) :: [a] -> [Int] -> [a]
(!!!) = go 0
  where
  go n (x:xs) kss@(k:ks)
    | n == k    = x : go (n+1) xs ks
    | otherwise = go (n+1) xs kss
  go _ _ _ = []

-- To retrieve everything, 'getNews Nothing [0..]'
getNews :: Maybe Int -> [Int] -> IO (Vector Int, Vector Int, Vector Int)
getNews maxDocs topics = fmap (asArrays . removeSingletons) $ run enc
  where
  enc = case maxDocs of
    Nothing -> fmap (!!! topics) $ encodeDirs path
    Just d  -> fmap (map (take d) . (!!! topics)) $ encodeDirs path

isStopword :: B.ByteString -> Bool
isStopword b = S.member b stopwords

-- | stopwords copied from <https://github.com/brendano/bow/blob/master/stopwords.c>
stopwords :: S.HashSet B.ByteString
stopwords = S.fromList
  [ ""
  , "a"
  , "able"
  , "about"
  , "above"
  , "according"
  , "accordingly"
  , "across"
  , "actually"
  , "after"
  , "afterwards"
  , "again"
  , "against"
  , "all"
  , "allow"
  , "allows"
  , "almost"
  , "alone"
  , "along"
  , "already"
  , "also"
  , "although"
  , "always"
  , "am"
  , "among"
  , "amongst"
  , "an"
  , "and"
  , "another"
  , "any"
  , "anybody"
  , "anyhow"
  , "anyone"
  , "anything"
  , "anyway"
  , "anyways"
  , "anywhere"
  , "apart"
  , "appear"
  , "appreciate"
  , "appropriate"
  , "are"
  , "around"
  , "as"
  , "aside"
  , "ask"
  , "asking"
  , "associated"
  , "at"
  , "available"
  , "away"
  , "awfully"
  , "b"
  , "be"
  , "became"
  , "because"
  , "become"
  , "becomes"
  , "becoming"
  , "been"
  , "before"
  , "beforehand"
  , "behind"
  , "being"
  , "believe"
  , "below"
  , "beside"
  , "besides"
  , "best"
  , "better"
  , "between"
  , "beyond"
  , "both"
  , "brief"
  , "but"
  , "by"
  , "c"
  , "came"
  , "can"
  , "cannot"
  , "cant"
  , "cause"
  , "causes"
  , "certain"
  , "certainly"
  , "changes"
  , "clearly"
  , "co"
  , "com"
  , "come"
  , "comes"
  , "concerning"
  , "consequently"
  , "consider"
  , "considering"
  , "contain"
  , "containing"
  , "contains"
  , "corresponding"
  , "could"
  , "course"
  , "currently"
  , "d"
  , "definitely"
  , "described"
  , "despite"
  , "did"
  , "different"
  , "do"
  , "does"
  , "doing"
  , "done"
  , "down"
  , "downwards"
  , "during"
  , "e"
  , "each"
  , "edu"
  , "eg"
  , "eight"
  , "either"
  , "else"
  , "elsewhere"
  , "enough"
  , "entirely"
  , "especially"
  , "et"
  , "etc"
  , "even"
  , "ever"
  , "every"
  , "everybody"
  , "everyone"
  , "everything"
  , "everywhere"
  , "ex"
  , "exactly"
  , "example"
  , "except"
  , "f"
  , "far"
  , "few"
  , "fifth"
  , "first"
  , "five"
  , "followed"
  , "following"
  , "follows"
  , "for"
  , "former"
  , "formerly"
  , "forth"
  , "four"
  , "from"
  , "further"
  , "furthermore"
  , "g"
  , "get"
  , "gets"
  , "getting"
  , "given"
  , "gives"
  , "go"
  , "goes"
  , "going"
  , "gone"
  , "got"
  , "gotten"
  , "greetings"
  , "h"
  , "had"
  , "happens"
  , "hardly"
  , "has"
  , "have"
  , "having"
  , "he"
  , "hello"
  , "help"
  , "hence"
  , "her"
  , "here"
  , "hereafter"
  , "hereby"
  , "herein"
  , "hereupon"
  , "hers"
  , "herself"
  , "hi"
  , "him"
  , "himself"
  , "his"
  , "hither"
  , "hopefully"
  , "how"
  , "howbeit"
  , "however"
  , "i"
  , "ie"
  , "if"
  , "ignored"
  , "immediate"
  , "in"
  , "inasmuch"
  , "inc"
  , "indeed"
  , "indicate"
  , "indicated"
  , "indicates"
  , "inner"
  , "insofar"
  , "instead"
  , "into"
  , "inward"
  , "is"
  , "it"
  , "its"
  , "itself"
  , "j"
  , "just"
  , "k"
  , "keep"
  , "keeps"
  , "kept"
  , "know"
  , "knows"
  , "known"
  , "l"
  , "last"
  , "lately"
  , "later"
  , "latter"
  , "latterly"
  , "least"
  , "less"
  , "lest"
  , "let"
  , "like"
  , "liked"
  , "likely"
  , "little"
  , "look"
  , "looking"
  , "looks"
  , "ltd"
  , "m"
  , "mainly"
  , "many"
  , "may"
  , "maybe"
  , "me"
  , "mean"
  , "meanwhile"
  , "merely"
  , "might"
  , "more"
  , "moreover"
  , "most"
  , "mostly"
  , "much"
  , "must"
  , "my"
  , "myself"
  , "n"
  , "name"
  , "namely"
  , "nd"
  , "near"
  , "nearly"
  , "necessary"
  , "need"
  , "needs"
  , "neither"
  , "never"
  , "nevertheless"
  , "new"
  , "next"
  , "nine"
  , "no"
  , "nobody"
  , "non"
  , "none"
  , "noone"
  , "nor"
  , "normally"
  , "not"
  , "nothing"
  , "novel"
  , "now"
  , "nowhere"
  , "o"
  , "obviously"
  , "of"
  , "off"
  , "often"
  , "oh"
  , "ok"
  , "okay"
  , "old"
  , "on"
  , "once"
  , "one"
  , "ones"
  , "only"
  , "onto"
  , "or"
  , "other"
  , "others"
  , "otherwise"
  , "ought"
  , "our"
  , "ours"
  , "ourselves"
  , "out"
  , "outside"
  , "over"
  , "overall"
  , "own"
  , "p"
  , "particular"
  , "particularly"
  , "per"
  , "perhaps"
  , "placed"
  , "please"
  , "plus"
  , "possible"
  , "presumably"
  , "probably"
  , "provides"
  , "q"
  , "que"
  , "quite"
  , "qv"
  , "r"
  , "rather"
  , "rd"
  , "re"
  , "really"
  , "reasonably"
  , "regarding"
  , "regardless"
  , "regards"
  , "relatively"
  , "respectively"
  , "right"
  , "s"
  , "said"
  , "same"
  , "saw"
  , "say"
  , "saying"
  , "says"
  , "second"
  , "secondly"
  , "see"
  , "seeing"
  , "seem"
  , "seemed"
  , "seeming"
  , "seems"
  , "seen"
  , "self"
  , "selves"
  , "sensible"
  , "sent"
  , "serious"
  , "seriously"
  , "seven"
  , "several"
  , "shall"
  , "she"
  , "should"
  , "since"
  , "six"
  , "so"
  , "some"
  , "somebody"
  , "somehow"
  , "someone"
  , "something"
  , "sometime"
  , "sometimes"
  , "somewhat"
  , "somewhere"
  , "soon"
  , "sorry"
  , "specified"
  , "specify"
  , "specifying"
  , "still"
  , "sub"
  , "such"
  , "sup"
  , "sure"
  , "t"
  , "take"
  , "taken"
  , "tell"
  , "tends"
  , "th"
  , "than"
  , "thank"
  , "thanks"
  , "thanx"
  , "that"
  , "thats"
  , "the"
  , "their"
  , "theirs"
  , "them"
  , "themselves"
  , "then"
  , "thence"
  , "there"
  , "thereafter"
  , "thereby"
  , "therefore"
  , "therein"
  , "theres"
  , "thereupon"
  , "these"
  , "they"
  , "think"
  , "third"
  , "this"
  , "thorough"
  , "thoroughly"
  , "those"
  , "though"
  , "three"
  , "through"
  , "throughout"
  , "thru"
  , "thus"
  , "to"
  , "together"
  , "too"
  , "took"
  , "toward"
  , "towards"
  , "tried"
  , "tries"
  , "truly"
  , "try"
  , "trying"
  , "twice"
  , "two"
  , "u"
  , "un"
  , "under"
  , "unfortunately"
  , "unless"
  , "unlikely"
  , "until"
  , "unto"
  , "up"
  , "upon"
  , "us"
  , "use"
  , "used"
  , "useful"
  , "uses"
  , "using"
  , "usually"
  , "uucp"
  , "v"
  , "value"
  , "various"
  , "very"
  , "via"
  , "viz"
  , "vs"
  , "w"
  , "want"
  , "wants"
  , "was"
  , "way"
  , "we"
  , "welcome"
  , "well"
  , "went"
  , "were"
  , "what"
  , "whatever"
  , "when"
  , "whence"
  , "whenever"
  , "where"
  , "whereafter"
  , "whereas"
  , "whereby"
  , "wherein"
  , "whereupon"
  , "wherever"
  , "whether"
  , "which"
  , "while"
  , "whither"
  , "who"
  , "whoever"
  , "whole"
  , "whom"
  , "whose"
  , "why"
  , "will"
  , "willing"
  , "wish"
  , "with"
  , "within"
  , "without"
  , "wonder"
  , "would"
  , "would"
  , "x"
  , "y"
  , "yes"
  , "yet"
  , "you"
  , "your"
  , "yours"
  , "yourself"
  , "yourselves"
  , "z"
  , "zero"
  ]