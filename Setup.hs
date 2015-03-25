import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import System.Directory

extractSandboxes x = case foldr f [] x of 
                       [] -> Nothing 
                       r  -> Just r 
 where f (SpecificPackageDB fp) = (fp :)
       f _ = id 

fileTemplate :: Maybe [String] -> String -> String 
fileTemplate sandbox dir = unlines 
  [ "module Language.Hakaru.Paths where"
  , "sandboxPackageDB :: Maybe [String]"
  , "sandboxPackageDB = " ++ show sandbox 
  , "hakaruRoot :: String" 
  , "hakaruRoot = " ++ show dir 
  ]

main = defaultMainWithHooks $ simpleUserHooks 
  { postConf = \a b c d -> do 
      let sb = extractSandboxes (withPackageDB d) 
      cd <- getCurrentDirectory 
      writeFile "Language/Hakaru/Paths.hs" (fileTemplate sb cd)
      postConf simpleUserHooks a b c d 
  }
                         
                       
