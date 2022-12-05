{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module PureSMT.Z3 where

import qualified Data.Map as M
import Foreign.Ptr (Ptr)
import qualified Language.C.Inline.Context as C
import qualified Language.C.Types as C

data LogicalContext

cContext :: C.Context
cContext = mempty {C.ctxTypesTable = M.singleton (C.TypeName "Z3_context") [t|Ptr LogicalContext|]}
