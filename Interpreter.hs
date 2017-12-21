{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase, EmptyCase #-}

module Interpreter where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

-- | Monad
type Eval = ReaderT Sig (StateT Env IO)

-- | Signature
type Sig = Map Id SigEntry
data SigEntry
  = FunSig
    { args :: [Arg]
    , body :: [Stm]
    }

-- | Environment
type Env = [Block]
type Block = Map Id Val

-- | Value
data Val
  = VVoid
  | VInt Integer
  | VBool Bool
  | VDouble Double
  | VUndefined

-- | Result
data Res
  = RRet Val
  | RCont

interpret :: Program -> IO ()
interpret (PDefs ds) = do
  -- Build signature
  let sig = Map.fromList $ map sigEntry ds
      sigEntry (DFun _t f args ss) = (f, FunSig args ss)
  -- Invoke main
  runMain sig

runMain :: Sig -> IO ()
runMain sig = do
  case Map.lookup (Id "main") sig of
    Just (FunSig [] ss) -> do
      _res <- evalStateT (runReaderT (evalStms ss) sig) [Map.empty]
      return ()

instance Monoid (Eval Res) where
  mempty       = return RCont
  mappend m m' = m >>= \case
    RCont  -> m'
    RRet v -> return (RRet v)

evalStms :: [Stm] -> Eval Res
evalStms = foldMap evalStm

evalStm :: Stm -> Eval Res
evalStm = \case
  SExp e -> do
    _v <- evalExp e
    return RCont

  SDecls t ids -> do
    mapM (\ i -> newVar i) ids
    return RCont

  SInit t id exp -> do
    val <- evalExp exp
    newVar id
    updateVar id val
    return RCont
  s -> fail $ "Not yet implemented: evalStm for " ++ show s

evalExp :: Exp -> Eval Val
evalExp = \case
  ETrue     -> return $ VBool True
  EFalse    -> return $ VBool False
  EInt i    -> return $ VInt i
  EDouble i -> return $ VDouble i
  --e@(EId id)    -> do
    --case Map.lookup id (Map.unions Env) of
      --Just v -> return v
    --  Nothing -> fail $ "Variable has no bound value [i] " ++ printTree e
  EApp f es -> do
    vs <- mapM evalExp es
    case f of
      Id "printInt" -> case vs of
        [VInt i] -> do
          liftIO $ putStrLn $ show i
          return VVoid
  e -> fail $ "Not yet implemented: evalExp for " ++ show e


newVar :: Id -> Eval ()
newVar id = do
  --Get the entire Environment
  env <- get

  --Get the topmost Block
  let block =  head env

  --Check if bindings exist in current block
  when (Map.member id block) $ fail $ printTree id ++ "shadows existing bindings"

  --Insert Binding into block
  let block' = Map.insert id VUndefined block

  --Put the Modified Block back along with the rest of the Env
  put(block' : tail env)

updateVar :: Id -> Val -> Eval ()
updateVar id val = do
  --Get Environment
  env <- get

  --Check if Bindings exist for Variable
  when (Map.member id (Map.unions env)) $ fail $ printTree id ++ "Binding does not exist"

  --Get the relevant Block for the binding
  let a = Map.insert id val (Map.unions env)

  return ()
