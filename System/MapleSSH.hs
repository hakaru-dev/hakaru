module System.MapleSSH (maple, withMaple) where

import Control.Monad
import Control.Concurrent
import Data.List
import Data.Maybe
import System.IO
import System.Process
import System.Environment

-- Default values for environment variables
defSSH    = "/usr/bin/ssh"
defUser   = "ppaml"
defServer = "quarry.uits.indiana.edu"
defModule = "maple/18"

maple :: String -> IO String
maple x = withMaple $ \eval -> eval x

envVars :: IO (String, String, String, String)
envVars = do ssh    <- get "MAPLE_SSH"    defSSH
             user   <- get "MAPLE_USER"   defUser
             server <- get "MAPLE_SERVER" defServer
             mod    <- get "MAPLE_MODULE" defModule
             return (ssh, user, server, mod)
             where env = getEnvironment
                   get name def = fmap (fromMaybe def . lookup name) env

mkMaple :: IO (Handle, Handle, ProcessHandle)
mkMaple = do
    (ssh, user, server, mapleModule) <- envVars
    let commands = "module load -s " ++ mapleModule ++ "; maple -q" -- quiet mode
    (Just inH, Just outH, Nothing, pid) <- createProcess (proc ssh ["-l" ++ user, server, commands]){ std_in = CreatePipe, std_out = CreatePipe, close_fds = True }
    let configHandle h = hSetBuffering h NoBuffering
    mapM_ configHandle [inH, outH]
    return (inH, outH, pid)

readUntil :: Handle -> String -> IO String
readUntil hdl str = fmap reverse (readUntil' (reverse str) [])
  where readUntil' xs ys | Just ys' <- stripPrefix xs ys
                         = return ys'
                         | otherwise
                         = do c <- hGetChar hdl
                              readUntil' xs (c:ys)

withMaple :: ((String -> IO String) -> IO a) -> IO a
withMaple k =
  do cmd <- newChan
     rsp <- newChan
     (inH, outH, _) <- mkMaple
     let term = "---"
     tid <- forkIO . forever $
              do c <- readChan cmd
                 let c' = c ++ ";printf(\"%s\",\"" ++ term ++ "\");" -- print a terminator
                 hPutStrLn inH c'
                 o <- fmap (unwords . words) $ readUntil outH term
                 writeChan rsp o
     r <- k $ \c -> do writeChan cmd c
                       readChan rsp
     killThread tid
     return r

test :: IO ()
test = withMaple $ \eval ->
        do x <- eval "1 + 1"
           y <- eval "eval(SLO)"
           print (x,y)

