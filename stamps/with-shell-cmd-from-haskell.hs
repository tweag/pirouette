import System.Environment
import System.IO
import System.Process.Typed

config :: ProcessConfig Handle () ()
config = setStdin createPipe $ shell "z3 -in"

send :: Handle -> String -> IO ()
send h cmd = do
  hPutStrLn h cmd
  hFlush h

sendLines :: Handle -> [String] -> IO ()
sendLines h [] = hClose h
sendLines h (l : rest) = do
  send h l
  sendLines h rest

transmit :: String -> Handle -> IO ()
transmit file h = do
  lines <$> readFile file >>= sendLines h

main = do
  args <- getArgs
  case args of
    [file] -> do
      p <- startProcess config
      transmit file (getStdin p)
    _ -> putStrLn "usage: ./with-shell-cmd-from-haskell <file>"
