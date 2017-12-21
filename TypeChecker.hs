{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

module TypeChecker where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

instance MonadError String Err where
  throwError msg = Bad msg
  catchError e h = case e of
    Ok a    -> Ok a
    Bad msg -> h msg

-- | Type checking monad
type TC = ReaderT Sig (StateT Cxt Err)

-- | Signature
type Sig = Map Id SigEntry
data SigEntry
  = FunSig
    { returnType :: Type
    , args       :: [Arg]
    }

-- | Context
data Cxt = Cxt
  { cxtReturnType :: Type
  , cxtBlocks     :: [Block]
  }
type Block = Map Id Type
binTypes = [Type_int, Type_double]
-- | Check a program
typecheck :: Program -> Err ()
typecheck (PDefs ds) = do
  -- Build signature
  let sig = Map.fromList sigPairs
      sigPairs = map sigEntry ds ++
        [ (Id "printInt", FunSig Type_void [ ADecl Type_int undefined ]),
          (Id "printDouble", FunSig Type_void [ ADecl Type_double undefined ]),
          (Id "readInt", FunSig Type_void [ADecl Type_int undefined]),
          (Id "readDouble", FunSig Type_void [ADecl Type_double undefined])
        ]
      sigEntry (DFun t f args _ss) = (f, FunSig t args)
  -- Check for duplicate function definitions
  let names = map fst sigPairs
      dup   = names List.\\ List.nub names
  unless (null dup) $ do
    throwError $ "the following functions are defined several times: " ++
      List.intercalate ", " (map printTree dup)
  -- Check function definitions
  evalStateT (runReaderT (checkDefs ds) sig) (Cxt Type_void [])
  -- Check for main
  checkMain sig

-- | Check that "main" is present and has correct function type.
checkMain :: Sig -> Err ()
checkMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig t args) -> do
      unless (t == Type_int) $ throwError $ "function main needs to return int"
      unless (null args) $ throwError $ "function main does not take arguments"
    Nothing -> throwError $ "function main is missing"

-- | Check all the function definitions.
checkDefs :: [Def] -> TC ()
checkDefs ds = mapM_ checkDef ds

-- | Check a function definition.
checkDef :: Def -> TC ()
checkDef (DFun t f args ss) = do
  -- The initial context is a single empty block.
  put $ Cxt t [Map.empty]
  -- Process function arguments.
  checkArgs args
  -- Check function body.
  checkStms ss

-- | Put function arguments as locals bindings in the top block.
checkArgs :: [Arg] -> TC ()
checkArgs args = mapM_ (\ (ADecl t x) -> newVar x t) args

checkStms :: [Stm] -> TC ()
checkStms ss = mapM_ checkStm ss

---TODO Possible implementation of this.
--inferIfVoid :: Type -> Bool
--inferIfVoid t = case t of
--   Type_void -> throwError $ "Variables cannot have type Void " ++ printTree exp
--   _-> do


checkStm :: Stm -> TC ()
checkStm = \case
  SExp e -> do
    --Infer the type of the Expressio
    _t <- inferExp e

    return ()

  SDecls t ids -> do
   --Case on Type
   case t of
      Type_void -> throwError $ "Variables cannot have type Void " ++ printTree ids
      _-> do
         --Add each Id with Type t to our Environment
         mapM (\ i -> newVar i t) ids

         return ()

  SInit t id exp -> do
   --Case on Type
   case t of
      Type_void -> throwError $ "Variables cannot have type Void " ++ printTree exp
      _-> do
          --Check if Expression matches Type
          checkExp exp t

          --Add the Variable id with Type t to our Environment
          newVar id t

          return ()

  SReturn exp -> do
    --Infer the Type of Expression
    t <-inferExp exp

    --Get Function Type
    typ <- gets cxtReturnType

    --Match Function Type with Return Type
    if typ == t
      then return ()
      else throwError $ "Return Type Error " ++ printTree exp

  SWhile exp stm -> do
    --Check the Expressions
    checkExp exp Type_bool

    --Check the Statements
    modify $ \ cxt -> cxt { cxtBlocks = (Map.empty) : (cxtBlocks cxt) }

    checkStm stm

    modify $ \ cxt -> cxt {  cxtBlocks = tail (cxtBlocks  cxt) }

    return ()

  SIfElse exp stm1 stm2 -> do
    --Check the Expressions
    checkExp exp Type_bool

    --Check If Statements
    modify $ \ cxt -> cxt { cxtBlocks = (Map.empty) : (cxtBlocks cxt) }

    checkStm stm1

    modify $ \ cxt -> cxt {  cxtBlocks = tail (cxtBlocks  cxt) }

    --Check Else Statements
    modify $ \ cxt -> cxt { cxtBlocks = (Map.empty) : (cxtBlocks cxt) }

    checkStm stm2

    modify $ \ cxt -> cxt {  cxtBlocks = tail (cxtBlocks  cxt) }

    return ()

  SBlock stms -> do
    --Put an empty block at the top of the block
    modify $ \ cxt -> cxt { cxtBlocks = (Map.empty) : (cxtBlocks cxt) }

    --Check Nested statements
    checkStms stms

    --Remove Topmost block
    modify $ \ cxt -> cxt {  cxtBlocks = tail (cxtBlocks  cxt) }

    return ()


inferExp :: Exp -> TC Type
inferExp = \case
  EInt _        -> return Type_int
  ETrue         -> return Type_bool;
  EFalse        -> return Type_bool;
  EDouble _     -> return Type_double;
  e@(EId id)    -> do
 --Get the list of context maps.
    block <- gets cxtBlocks

 --Union them, the first occurence will be the first from either.
    case Map.lookup id (Map.unions block) of
        Nothing -> throwError $ "undefined variable called " ++ printTree id
        Just t  -> return t

  e@(EApp f es) -> do
    sig <- ask

    case Map.lookup f sig of
      Nothing -> throwError $ "undefined function in call " ++ printTree e
      Just (FunSig t args) -> do

        -- Check that number of arguments matches the function arity
        unless (length args == length es) $ throwError $
          "wrong number of arguments in function call " ++ printTree e

        -- Check that the arguments have correct types
        let checkArg e (ADecl t _) = checkExp e t
        zipWithM_ checkArg es args

        -- Return the result type of the function
        return t

  e@(EPostIncr id) -> do
    --Get all contextBlocks
    blocks <- gets cxtBlocks

    --Lookup the Type of Id
    lookUpVar id blocks

  e@(EPostDecr id) -> do
    --Get all contextBlocks
    blocks <- gets cxtBlocks

    --Lookup the Type of Id
    lookUpVar id blocks

  e@(EPreIncr id) -> do
   --Get all contextBlocks
   blocks <- gets cxtBlocks

   --Lookup the Type of Id
   lookUpVar id blocks

  e@(EPreDecr id) -> do
   --Get all contextBlocks
   blocks <- gets cxtBlocks

   --Lookup the Type of Id
   lookUpVar id blocks

  ETimes exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return t

  EDiv exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return t

  EPlus exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return t

  EMinus exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return t

  ELt exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return Type_bool

  EGt exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return Type_bool

  ELtEq exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return Type_bool

  EGtEq exp1 exp2 -> do
    t <- inferBin binTypes exp1 exp2
    return Type_bool

  EEq exp1 exp2 -> do
    t <- inferBin [Type_int, Type_double, Type_bool] exp1 exp2
    return Type_bool

  ENEq exp1 exp2 -> do
    t <- inferBin [Type_int, Type_double, Type_bool] exp1 exp2
    return Type_bool

  EAnd exp1 exp2 -> do
    t <- inferBin [Type_bool] exp1 exp2
    return Type_bool

  EOr exp1 exp2 -> do
    t <- inferBin [Type_bool] exp1 exp2
    return Type_bool

  EAss id e -> do
  --Get the list of context maps.
     block <- gets cxtBlocks

  --Union them, the first occurence will be the first from either.
     case Map.lookup id (Map.unions block) of
         Nothing -> throwError $ "Undefined variable called " ++ printTree id
         Just t  -> do
           checkExp e t

           return t

inferBin :: [Type] -> Exp -> Exp  -> TC Type
inferBin types e1 e2 = do
  t <- inferExp e1
  if elem t types
    then do
      checkExp e2 t
      return t
    else
      throwError $ "Invalid Type in Expression " ++  (printTree e1) ++ " " ++ (printTree e2)

checkExp :: Exp -> Type -> TC ()
checkExp e t = do
  t' <- inferExp e
  unless (t == t') $ throwError $
    "inferred type " ++ printTree t' ++ " does not match expected type " ++ printTree t

newVar :: Id -> Type -> TC ()
newVar x t = do
  case t of
    Type_void -> throwError $ "Type of variable" ++ printTree x
    _         -> do
      block <- head <$> gets cxtBlocks

      when (Map.member x block) $
        throwError $ "variable " ++ printTree x ++ " shadows existing binding"

      let block' = Map.insert x t block
      modify $ \ cxt -> cxt { cxtBlocks = block' : tail (cxtBlocks cxt) }

nyi :: Show a => a -> TC b
nyi a = throwError $ "not yet implemented: checking " ++ show a

lookUpVar :: Id -> [Block]  -> TC Type
lookUpVar id blocks = case Map.lookup id (Map.unions blocks) of
    Nothing -> throwError $ "undefined variable called " ++ printTree id
    Just t  -> if elem t [Type_int, Type_double]
               then return t
               else throwError $ "Incr only defined for Int/Double " ++ printTree id
