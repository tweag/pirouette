import qualified Data.ByteString as BS
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
  BS.split 10 <$> BS.readFile file >>= sendLines hIn hOut

sendLines :: Handle -> Handle -> [BS.ByteString] -> IO ()
sendLines hIn hOut [] = hClose hIn
sendLines hIn hOut (l : rest) = do
  send hIn l >> recv hOut
  sendLines hIn hOut rest

send :: Handle -> BS.ByteString -> IO ()
send h cmd = do
  BS.hPutStrLn h $ BS.snoc cmd 10
  hFlush h

recv :: Handle -> IO ()
recv h = do
  resp <- BS.hGetLine h
  BS.putStrLn resp
