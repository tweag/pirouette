import qualified Data.ByteString as BS
import Foreign.Ptr
import System.Environment
import System.IO
import Z3.Base.C

main = do
  args <- getArgs
  case args of
    [file] -> do
      cfg <- z3_mk_config
      ctx <- z3_mk_context cfg
      transmit file ctx
    _ -> putStrLn "usage: ./with-bindings-from-haskell <file>"

transmit :: String -> Ptr Z3_context -> IO ()
transmit file ctx = do
  cmds <- BS.split 10 <$> BS.readFile file
  mapM_ (command ctx) cmds

command :: Ptr Z3_context -> BS.ByteString -> IO ()
command ctx cmd = do
  resp <- BS.useAsCString cmd $ z3_eval_smtlib2_string ctx
  BS.packCString resp >>= BS.putStrLn
