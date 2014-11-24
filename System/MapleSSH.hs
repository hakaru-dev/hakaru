module System.MapleSSH (maple) where

import Control.Monad
import Control.Concurrent
import Data.List
import Data.Maybe(fromMaybe)
import Data.Char(isSpace)
import System.IO
import System.Process
import System.Environment
import System.Exit

-- Default values for environment variables
defSSH    = "/usr/bin/ssh"
defUser   = "ppaml"
defServer = "quarry.uits.indiana.edu"
defModule = "maple/18"


envVars :: IO (String, String, String, String)
envVars = do ssh    <- get "MAPLE_SSH"    defSSH
             user   <- get "MAPLE_USER"   defUser
             server <- get "MAPLE_SERVER" defServer
             mod    <- get "MAPLE_MODULE" defModule
             return (ssh, user, server, mod)
             where env = getEnvironment
                   get name def = fmap (fromMaybe def . lookup name) env


maple :: String -> IO String
maple x = do
    (ssh, user, server, mod) <- envVars
    let commands = "module load -s " ++ mod ++ "; maple -q -t" -- quiet mode
    (Just inH, Just outH, Nothing, p) <- createProcess (proc ssh ["-l" ++ user, server, commands])
                                         { std_in = CreatePipe, std_out = CreatePipe, close_fds = True }
    hPutStrLn inH $ x ++ ";"
    hClose inH
    c <- hGetContents outH
    length c `seq` hClose outH
    exit <- waitForProcess p
    case exit of ExitSuccess -> return $ trim c
                 _ -> error ("maple:" ++ show exit)


trim :: String -> String
trim = dropWhile isSpace


test :: IO ()
test = do x <- maple "eval(SLO)"
          print x
