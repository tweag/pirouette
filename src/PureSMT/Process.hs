{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module PureSMT.Process where

import Control.DeepSeq (force)
import Control.Monad
import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Char8 as BS
import Data.IORef
import qualified Debug.TimeStats as TimeStats
import Foreign.ForeignPtr
import qualified Language.C.Inline as C
import qualified Language.C.Inline.Unsafe as CU
import PureSMT.SExpr
import qualified PureSMT.Z3 as Z3
import Prelude hiding (const)

C.context (C.baseCtx <> C.fptrCtx <> C.bsCtx <> Z3.cContext)
C.include "z3.h"

data Solver = Solver
  { context :: ForeignPtr Z3.LogicalContext,
    debugMode :: Bool,
    queue :: IORef Builder -- only used in non-debug mode
  }

-- | Create a brand-new context for Z3 to work in.
initZ3Instance ::
  -- | Whether or not to debug the interaction
  Bool ->
  IO Solver
initZ3Instance dbg = TimeStats.measureM "launchSolver" $ do
  let ctxFinalizer =
        [C.funPtr| void free_context(Z3_context ctx) {
                                      Z3_del_context(ctx);
                                      } |]
  solverCtx <-
    newForeignPtr ctxFinalizer
      =<< [CU.block| Z3_context {
                     Z3_config cfg = Z3_mk_config();
                     Z3_context ctx = Z3_mk_context(cfg);
                     Z3_del_config(cfg);
                     return ctx;
                     } |]
  solverQueue <- newIORef mempty
  let solver = Solver solverCtx dbg solverQueue
  when (debugMode solver) $ do
    -- this should not be enabled in non-debug mode, as it messes with parsing
    -- the outputs of commands that are actually interesting
    setOption solver ":print-success" "true"
  setOption solver ":produce-models" "true"
  return solver

-- | Send a bytestring to Z3.
-- This function is thread-safe as long as concurrent instances do not share the
-- same logical context.
send :: Solver -> BS.ByteString -> IO SExpr
send solver cmd = do
  let ctx = context solver
  let !cmd' = cmd
  when (debugMode solver) $ do
    BS.putStrLn $ "[send] " `BS.append` cmd'
  resp <-
    TimeStats.measureM "Z3" $
      [CU.exp| const char* {
         Z3_eval_smtlib2_string($fptr-ptr:(Z3_context ctx), $bs-ptr:cmd')
         } |]
        >>= BS.packCString
  case TimeStats.measurePure "readSExpr" $ force $ readSExpr resp of
    Nothing -> do
      fail $ "solver replied with:\n" ++ BS.unpack resp
    Just (sexpr, _) -> do
      when (debugMode solver && sexpr /= Atom "success") $ do
        putStrLn $ "[recv] " ++ showsSExpr sexpr ""
      return sexpr

-- | Push a command on the solver's queue of commands to evaluate.
-- The command must not produce any output when evaluated.
putQueue :: Solver -> SExpr -> IO ()
putQueue solver expr = do
  let solverQueue = queue solver
  cmds <- readIORef solverQueue
  writeIORef solverQueue $ cmds <> renderSExpr expr

-- | Empty the queue of commands to evaluate and return its content as a bytestring.
flushQueue :: Solver -> IO (BS.ByteString)
flushQueue solver = do
  let solverQueue = queue solver
  cmds <- readIORef solverQueue
  writeIORef solverQueue mempty
  return $ serializeBatch cmds

-- | Have Z3 evaluate a command in SExpr format.
-- This forces the queued commands to be evaluated as well, but their results are
-- *not* checked for correctness.
command :: Solver -> SExpr -> IO SExpr
command solver expr = TimeStats.measureM "command" $ do
  cmds <- TimeStats.measureM "showsSExpr" $ do
    putQueue solver expr
    flushQueue solver
  send solver cmds

-- | A command with no interesting result.
-- In debug mode, the result is checked for correctness and the queue of commands
-- to evaluate is ignored.
-- In non-debug mode, the command must not produce any output when evaluated, and
-- it is not checked for correctness.
ackCommand :: Solver -> SExpr -> IO ()
ackCommand solver expr =
  TimeStats.measureM "command" $
    if debugMode solver
      then do
        let !cmd = TimeStats.measurePure "showsSExpr" $ serializeSingle $ renderSExpr expr
        resp <- send solver cmd
        case resp of
          Atom "success" -> return ()
          _ ->
            fail $
              unlines
                [ "Unexpected result from the SMT solver:",
                  "  Expected: success",
                  "  Result: " ++ showsSExpr resp ""
                ]
      else TimeStats.measureM "showsSExpr" $ putQueue solver expr

-- | A command entirely made out of atoms, with no interesting result.
-- See also `ackCommand`.
simpleCommand :: Solver -> [String] -> IO ()
simpleCommand solver = ackCommand solver . List . map Atom

-- | Run a command and return True if successful, and False if unsupported.
-- This is useful for setting options that are unsupported by some solvers, but used
-- by others.
-- See also `command`.
simpleCommandMaybe :: Solver -> [String] -> IO Bool
simpleCommandMaybe solver c =
  do
    res <- command solver (List (map Atom c))
    case res of
      Atom "success" -> return True
      Atom "unsupported" -> return False
      _ ->
        fail $
          unlines
            [ "Unexpected result from the SMT solver:",
              "  Expected: success or unsupported",
              "  Result: " ++ showsSExpr res ""
            ]

-- | Set a solver option.
setOption :: Solver -> String -> String -> IO ()
setOption s x y = simpleCommand s ["set-option", x, y]

-- | Set a solver option, returning False if the option is unsupported.
setOptionMaybe :: Solver -> String -> String -> IO Bool
setOptionMaybe s x y = simpleCommandMaybe s ["set-option", x, y]

-- | Set the solver's logic.  Usually, this should be done first.
setLogic :: Solver -> String -> IO ()
setLogic s x = simpleCommand s ["set-logic", x]

-- | Set the solver's logic, returning False if the logic is unsupported.
setLogicMaybe :: Solver -> String -> IO Bool
setLogicMaybe s x = simpleCommandMaybe s ["set-logic", x]

-- | Request unsat cores.  Returns if the solver supports them.
produceUnsatCores :: Solver -> IO Bool
produceUnsatCores s = setOptionMaybe s ":produce-unsat-cores" "true"

-- | Checkpoint state.
push :: Solver -> IO ()
push = flip simpleCommand ["push", "1"]

-- | Restore to last check-point.
pop :: Solver -> IO ()
pop = flip simpleCommand ["pop", "1"]

-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns an the declared name as a constant expression.
declare :: Solver -> String -> SExpr -> IO SExpr
declare solver f = declareFun solver f []

-- | Declare a function or a constant.
-- For convenience, returns an the declared name as a constant expression.
declareFun :: Solver -> String -> [SExpr] -> SExpr -> IO SExpr
declareFun solver f args r =
  do
    ackCommand solver $ fun "declare-fun" [Atom f, List args, r]
    return (const f)

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatype ::
  Solver ->
  -- | datatype name
  String ->
  -- | sort parameters
  [String] ->
  -- | constructors
  [(String, [(String, SExpr)])] ->
  IO ()
declareDatatype solver t ps cs =
  ackCommand solver $
    fun
      "declare-datatype"
      [ Atom t,
        datatypeDefn ps cs
      ]

-- | Declare an ADT using the format introduced in SmtLib 2.6.
declareDatatypes ::
  Solver ->
  [(String, [String], [(String, [(String, SExpr)])])] ->
  IO ()
declareDatatypes solver dts =
  ackCommand solver $
    fun
      "declare-datatypes"
      [ List [List [Atom nm, Atom (show $ length args)] | (nm, args, _) <- dts],
        List [datatypeDefn args cstrs | (_, args, cstrs) <- dts]
      ]

-- | Shared part of 'declareDatatype' and 'declareDatatypes'
datatypeDefn :: [String] -> [(String, [(String, SExpr)])] -> SExpr
datatypeDefn [] cs =
  List [List (Atom c : [List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs]
datatypeDefn ps cs =
  fun
    "par"
    [ List (map Atom ps),
      List [List (Atom c : [List [Atom s, argTy] | (s, argTy) <- args]) | (c, args) <- cs]
    ]

-- | Declare a constant.  A common abbreviation for 'declareFun'.
-- For convenience, returns the defined name as a constant expression.
define ::
  Solver ->
  -- | New symbol
  String ->
  -- | Symbol type
  SExpr ->
  -- | Symbol definition
  SExpr ->
  IO SExpr
define solver f = defineFun solver f []

-- | Define a function or a constant.
-- For convenience, returns an the defined name as a constant expression.
defineFun ::
  Solver ->
  -- | New symbol
  String ->
  -- | Parameters, with types
  [(String, SExpr)] ->
  -- | Type of result
  SExpr ->
  -- | Definition
  SExpr ->
  IO SExpr
defineFun solver f args t e =
  do
    ackCommand solver $
      fun
        "define-fun"
        [Atom f, List [List [const x, arg] | (x, arg) <- args], t, e]
    return (const f)

-- | Define a recursive function or a constant.  For convenience,
-- returns an the defined name as a constant expression.  This body
-- takes the function name as an argument.
defineFunRec ::
  Solver ->
  -- | New symbol
  String ->
  -- | Parameters, with types
  [(String, SExpr)] ->
  -- | Type of result
  SExpr ->
  -- | Definition
  (SExpr -> SExpr) ->
  IO SExpr
defineFunRec solver f args t e =
  do
    let fs = const f
    ackCommand solver $
      fun
        "define-fun-rec"
        [Atom f, List [List [const x, arg] | (x, arg) <- args], t, e fs]
    return fs

-- | Define a recursive function or a constant.  For convenience,
-- returns an the defined name as a constant expression.  This body
-- takes the function name as an argument.
defineFunsRec ::
  Solver ->
  [(String, [(String, SExpr)], SExpr, SExpr)] ->
  IO ()
defineFunsRec solver ds = ackCommand solver $ fun "define-funs-rec" [decls, bodies]
  where
    oneArg (f, args, t, _) = List [Atom f, List [List [const x, a] | (x, a) <- args], t]
    decls = List (map oneArg ds)
    bodies = List (map (\(_, _, _, body) -> body) ds)

-- | Assume a fact.
assert :: Solver -> SExpr -> IO ()
assert solver e = ackCommand solver $ fun "assert" [e]

-- | Check if the current set of assertion is consistent.
check :: Solver -> IO Result
check solver =
  do
    res <- command solver (List [Atom "check-sat"])
    case res of
      Atom "unsat" -> return Unsat
      Atom "unknown" -> return Unknown
      Atom "sat" -> return Sat
      _ ->
        fail $
          unlines
            [ "Unexpected result from the SMT solver:",
              "  Expected: unsat, unknown, or sat",
              "  Result: " ++ showsSExpr res ""
            ]

-- | Get the values of some s-expressions.
-- Only valid after a 'Sat' result.
getExprs :: Solver -> [SExpr] -> IO [(SExpr, Value)]
getExprs solver vals =
  do
    res <- command solver $ List [Atom "get-value", List vals]
    case res of
      List xs -> mapM getAns xs
      _ ->
        fail $
          unlines
            [ "Unexpected response from the SMT solver:",
              "  Exptected: a list",
              "  Result: " ++ showsSExpr res ""
            ]
  where
    getAns expr =
      case expr of
        List [e, v] -> return (e, sexprToVal v)
        _ ->
          fail $
            unlines
              [ "Unexpected response from the SMT solver:",
                "  Expected: (expr val)",
                "  Result: " ++ showsSExpr expr ""
              ]

-- | Get the values of some constants in the current model.
-- A special case of 'getExprs'.
-- Only valid after a 'Sat' result.
getConsts :: Solver -> [String] -> IO [(String, Value)]
getConsts solver xs =
  do
    ans <- getExprs solver (map Atom xs)
    return [(x, e) | (Atom x, e) <- ans]

-- | Get the value of a single expression.
getExpr :: Solver -> SExpr -> IO Value
getExpr solver x =
  do
    [(_, v)] <- getExprs solver [x]
    return v

-- | Get the value of a single constant.
getConst :: Solver -> String -> IO Value
getConst solver x = getExpr solver (Atom x)

-- | Returns the names of the (named) formulas involved in a contradiction.
getUnsatCore :: Solver -> IO [String]
getUnsatCore s =
  do
    res <- command s $ List [Atom "get-unsat-core"]
    case res of
      List xs -> mapM fromAtom xs
      _ -> unexpected "a list of atoms" res
  where
    fromAtom x =
      case x of
        Atom a -> return a
        _ -> unexpected "an atom" x

    unexpected x e =
      fail $
        unlines
          [ "Unexpected response from the SMT Solver:",
            "  Expected: " ++ x,
            "  Result: " ++ showsSExpr e ""
          ]
