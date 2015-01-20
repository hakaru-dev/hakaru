module Main where

import System.IO
import System.Process
import System.Exit

-- copy all *.mpl files to the server
-- upload files to server, build there, move archive?


ssh, user, serv :: String
ssh  = "ssh"
user = "ppaml"
serv = "karst.uits.iu.edu"


sshCommands :: [String]
sshCommands = [
  "cd hakaru/maple",
  "pwd",
  "git pull",
  "maple update-archive.mpl",
  "ls -l ppaml.mla"
  ]


run :: String -> [String] -> IO String
run prog commands = do
  let p = proc prog [user ++ "@" ++ serv]
  (Just inH, Just outH, Nothing, p') <- createProcess p { std_in = CreatePipe, std_out = CreatePipe, close_fds = True }
  mapM (hPutStrLn inH) commands
  hClose inH
  c <- hGetContents outH
  length c `seq` hClose outH
  exit <- waitForProcess p'
  case exit of
    ExitSuccess -> return $ c
    _ -> error (prog ++ ":" ++ show exit)


main :: IO ()
main = do
  result <- run ssh sshCommands
  putStrLn result
