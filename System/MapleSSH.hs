module System.MapleSSH (maple, withMaple) where

import Control.Monad
import Control.Concurrent
import Data.List
import System.IO
import System.Process

ssh, server, mapleModule :: String
ssh = "/usr/bin/ssh"
server = "quarry.uits.indiana.edu"
mapleModule = "maple/18"

maple :: String -> IO String
maple x = withMaple $ \eval -> eval x

mkMaple :: IO (Handle, Handle, Handle, ProcessHandle)
mkMaple = do let commands = "module load -s " ++ mapleModule ++ "; maple -t"
             -- The double -t option to ssh forces it to create a pseudo-tty even though its parent isn't one.
             -- If it doesn't do this, we somewhat bizarrely don't get prompts until after sending a line of input.
             (inH, outH, errH, pid) <- runInteractiveProcess ssh ["-t", "-t", server, commands] Nothing Nothing
             let configHandle h =
                   hSetBuffering h NoBuffering
             mapM_ configHandle [inH, outH, errH]
             return (inH, outH, errH, pid)

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
     (inH, outH, _, _) <- mkMaple
     readUntil outH "#-->" -- wait for the first prompt from Maple
     tid <- forkIO . forever $
              do c <- readChan cmd
                 let c' = c ++ ";"
                 hPutStrLn inH c'
                 _ <- readUntil outH c' -- discard local echo
                 o <- fmap (unwords . words) $ readUntil outH "#-->"
                 writeChan rsp o
     r <- k $ \c -> do writeChan cmd c
                       readChan rsp
     killThread tid
     return r

{-
test :: IO ()
test = withMaple $ \eval ->
        do x <- eval "1 + 1"
           y <- eval "2 * 2"
           print (x,y)
-}
