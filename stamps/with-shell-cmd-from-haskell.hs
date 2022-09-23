import System.Environment
import System.IO
import System.Process.Typed

config :: ProcessConfig Handle Handle ()
config = setStdin createPipe $ setStdout createPipe $ shell "z3 -in"

main = do
  args <- getArgs
  case args of
    [file] -> do
      p <- startProcess config
      transmit file (getStdin p) (getStdout p)
    _ -> putStrLn "usage: ./with-shell-cmd-from-haskell <file>"

transmit :: String -> Handle -> Handle -> IO ()
transmit file hIn hOut = do
  lines <$> readFile file >>= sendLines hIn hOut

sendLines :: Handle -> Handle -> [String] -> IO ()
sendLines hIn hOut [] = hClose hIn
sendLines hIn hOut (l : rest) = do
  send hIn l >> recv hOut
  sendLines hIn hOut rest

send :: Handle -> String -> IO ()
send h cmd = do
  hPutStrLn h cmd
  hFlush h

recv :: Handle -> IO ()
recv h = do
  resp <- hGetLine h
  putStrLn resp
