import System.Environment
import Z3.Monad

send :: String -> Z3 AST
send cmd = parseSMTLib2String cmd [] [] [] []

sendLines :: [String] -> Z3 AST
sendLines [] = send "\n"
sendLines (l : rest) = do
  send l
  sendLines rest

transmit :: String -> IO (Z3 AST)
transmit file = do
  sendLines <$> lines <$> readFile file

main = do
  args <- getArgs
  case args of
    [file] -> do
      output <- (>>= astToString) <$> transmit file >>= evalZ3
      putStrLn output
    _ -> putStrLn "usage: ./with-bindings-from-haskell <file>"
