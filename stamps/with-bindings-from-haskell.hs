import System.Environment
import System.IO
import Z3.Monad

run :: String -> IO String
run file = evalZ3 (script file)

script :: String -> Z3 String
script file = do
  ast <- parseSMTLib2File file [] [] [] []
  astToString ast

main = do
  args <- getArgs
  case args of
    [file] -> run file >>= putStrLn
    _ -> putStrLn "usage: ./with-bindings-from-haskell <file>"
