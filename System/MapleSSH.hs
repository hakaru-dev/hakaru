module System.MapleSSH (maple) where

import Data.Maybe(fromMaybe)
import Data.Char(isSpace)
import System.IO
import System.Process
import System.Environment
import System.Exit

-- Default values for SSH environment variables
defSSH, defUser, defServer, defModule :: String
defSSH    = "/usr/bin/ssh"
defUser   = "ppaml"
defServer = "quarry.uits.indiana.edu"
defModule = "maple/18"


envVarsSSH :: IO (String, String, String, String)
envVarsSSH = do
    ssh     <- get "MAPLE_SSH"    defSSH
    user    <- get "MAPLE_USER"   defUser
    server  <- get "MAPLE_SERVER" defServer
    mpl_mod <- get "MAPLE_MODULE" defModule
    return (ssh, user, server, mpl_mod)
    where get name def = fmap (fromMaybe def) (lookupEnv name)

process :: IO CreateProcess
process = do
    bin <- lookupEnv "MAPLE"
    case bin of
        Just b  -> return $ proc b ["-q", "-t"]
        Nothing -> 
          do (ssh, user, server, mpl_mod) <- envVarsSSH
             let commands = "module load -s " ++ mpl_mod ++ "; maple -q -t" -- quiet mode
             return $ proc ssh ["-l" ++ user, server, commands]


maple :: String -> IO String
maple cmd = do
    p <- process
    (Just inH, Just outH, Nothing, p') <- createProcess p { std_in = CreatePipe, std_out = CreatePipe, close_fds = True }
    hPutStrLn inH $ cmd ++ ";"
    hClose inH
    c <- hGetContents outH
    length c `seq` hClose outH
    exit <- waitForProcess p'
    case exit of ExitSuccess -> return $ trim c
                 _ -> error ("maple:" ++ show exit)

trim :: String -> String
trim = dropWhile isSpace

test :: IO ()
test = do x <- maple "eval(SLO)"
          print x
