module System.MapleSSH (maple) where

import Data.Maybe(fromMaybe)
import Data.Char(isSpace)
import System.IO (hPutStrLn, hClose, hGetContents)
import System.Process (proc, CreateProcess(..), StdStream(CreatePipe), createProcess, waitForProcess)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(ExitSuccess))

-- Default values for SSH environment variables
defSSH, defUser, defServer, defCommand :: String
defSSH     = "/usr/bin/ssh"
defUser    = "ppaml"
defServer  = "karst.uits.iu.edu"
defCommand = "maple"
-- On the server side, ~/.modules should load maple/18, and ~/.mapleinit
-- should point to ~/hakaru/maple (updated by hakaru/maple/MapleUpdate.hs)

envVarsSSH :: IO (String, String, String, String)
envVarsSSH = do
    ssh     <- get "MAPLE_SSH"     defSSH
    user    <- get "MAPLE_USER"    defUser
    server  <- get "MAPLE_SERVER"  defServer
    command <- get "MAPLE_COMMAND" defCommand
    return (ssh, user, server, command)
    where get name def = fmap (fromMaybe def) (lookupEnv name)

process :: IO CreateProcess
process = do
    bin <- lookupEnv "LOCAL_MAPLE"
    case bin of
        Just b  -> return $ proc b ["-q", "-t"]
        Nothing -> 
          do (ssh, user, server, command) <- envVarsSSH
             let commands = command ++ " -q -t" -- quiet mode
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
