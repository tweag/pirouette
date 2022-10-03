import System.Environment
import System.IO
import System.Process.Typed
import Z3.Base

main = do
  args <- getArgs
  case args of
    [file] -> do
      cfg <- mkConfig
      ctx <- mkContext cfg
      transmit file ctx
    _ -> putStrLn "usage: ./with-bindings-from-haskell <file>"

transmit :: String -> Context -> IO ()
transmit file ctx = do
  cmds <- lines <$> readFile file
  mapM_ (command ctx) cmds

command :: Context -> String -> IO ()
command ctx cmd = do
  resp <- evalSMTLib2String ctx cmd
  putStrLn resp
