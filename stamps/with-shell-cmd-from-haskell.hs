import System.Environment
import System.IO
import System.Process.Typed

run :: String -> ProcessConfig () () ()
run file = shell ("z3 " ++ file)

main = do
  args <- getArgs
  case args of
    [file] -> withProcessWait (run file) checkExitCode
    _ -> putStrLn "usage: ./with-shell-cmd-from-haskell <file>"
