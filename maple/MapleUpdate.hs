module Main where

import System.IO
import System.Process
import System.Exit

-- copy all *.mpl files to the server
-- upload files to server, build there, move archive?


-- the "-b -" option tells sftp to read commands from stdin
sftp, ssh, user, serv :: String
sftp = "sftp"
ssh  = "ssh"
user = "ppaml"
serv = "quarry.uits.indiana.edu"


sftpCommands :: [String]
sftpCommands = [
  "pwd",
  "mkdir maple",
  "cd maple",
  "put ../mochastic/Language/Hakaru/*.mpl .",
  "put update-archive.mpl ."
  ]

sshCommands :: [String]
sshCommands = [
  "cd maple",
  "maple update-archive.mpl",
  "rm *.mpl",
  "pwd",
  "ls"
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
  result <- run sftp sftpCommands
  putStrLn result
  result <- run ssh sshCommands
  putStrLn result
