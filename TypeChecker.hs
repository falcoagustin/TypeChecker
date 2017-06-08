module TypeChecker where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (foldM)

import AbsCpp
import PrintCpp
import ErrM


type Env        = (Signature,[Context]) 
type Signature  = Map Id ([Type],Type)  
type Context  = Map Id Type           

typecheck :: Program -> Err ()
typecheck (PDefs ds) = do
  env  <- foldM (\env  (DFun typ id args _) -> updateFun env id (argTypes args,typ) ) emptyEnv ds
  mapM_ (checkDef env) ds 
  where argTypes = map (\(ADecl typ _) -> typ) 
        stdFunctions = [ DFun Type_void   (Id "printInt")    [ADecl Type_int (Id "x")]    [],
                         DFun Type_void   (Id "printDouble") [ADecl Type_double (Id "x")] [],
                         DFun Type_int    (Id "readInt")     []                           [],
                         DFun Type_double (Id "readDouble")  []                           [] ]

newBlock :: Env -> Env
newBlock (s, cont) = 
    let empty_cont         = Map.empty
    in (s, empty_cont:cont)

emptyEnv :: Env
emptyEnv = let
 empty_s = Map.empty
 empty_cont   = Map.empty
 in (empty_s, [empty_cont])

lookupVar :: Env -> Id -> Err Type
lookupVar (_s, []) id = fail $ "Error"
lookupVar (s, c:cs) id =
    case Map.lookup id c of
      Just t      -> return t
      Nothing     -> lookupVar (s, cs) id
  
checkDef :: Env -> Def -> Err ()
checkDef env (DFun typ _ args stms) = do
    resultado <- foldM addArg env args
    checkStms resultado typ stms
    return ()
    where addArg env' (ADecl typ' id') = updateVar env' id' typ'


lookupFun :: Env -> Id -> Err ([Type],Type)
lookupFun (s, _cont) id =
    case Map.lookup id s of
      Just t      -> return t
      Nothing     -> fail $ "Error en lookupFun "

updateVar :: Env -> Id -> Type -> Err Env
updateVar (s, c:cs) id typ =
    let lookup_var = Map.lookup id c
    in case lookup_var of
        Nothing -> return (s, Map.insert id typ c:cs)
        Just t  -> fail $ "Variable ya declarada "

updateFun :: Env -> Id -> ([Type],Type) -> Err Env
updateFun (s, cont) id fun =
    let lookup_fun = Map.lookup id s
    in case lookup_fun of
        Nothing -> return (Map.insert id fun s, cont)
        Just _  -> fail $ "Error: variable ya declarada"

checkStms :: Env -> Type -> [Stm] -> Err Env
checkStms env typ stms = case stms of
    stm:stms -> do env' <- checkStm env typ stm
                   checkStms env' typ stms
    []       -> return env

checkExp :: Env -> Type -> Exp -> Err ()
checkExp env typ exp =
    do typ2 <- inferExp env exp
       if typ2 <= typ
       then return ()
       else fail $ "tipos diferentes. Hay un error"

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types env exp1 exp2 = do
    typ <- inferExp env exp1
    if typ `elem` types
    then do checkExp env typ exp2
            return typ
    else fail $ "Error en Inferencia de tipo binario"
  
checkStm :: Env -> Type -> Stm -> Err Env
checkStm env typ stm = case stm of
    SExp exp       -> do inferExp env exp
                         return env
    SInit t id exp -> do checkExp env t exp
                         updateVar env id t
    SDecls typ' []   -> fail $ "no hay una variable declarada para es tipo  "
    SDecls typ' vars -> foldM (\env' var -> updateVar env' var typ') env vars
    
    SReturn exp    -> do t_return <- inferExp env exp
                         if t_return <= typ
                         then return env
                         else fail $ "Tipo encontrado: " ++ show t_return ++
                                     "; se esperaba " ++ show typ
    SIfElse exp stm1 stm2 -> do checkExp env Type_bool exp
                                checkStm env typ stm1
                                checkStm env typ stm2   
    SWhile exp st  -> do checkExp env Type_bool exp
                         checkStm env typ st 
    SBlock stms    -> do checkStms (newBlock env) typ stms
                         return env

inferExp :: Env -> Exp -> Err Type
inferExp env exp = case exp of
    EInt _           -> return Type_int
    EDouble _        -> return Type_double
    ETrue            -> return Type_bool
    EFalse           -> return Type_bool
    EId id           -> lookupVar env id
    EPIncr exp       -> inferNum exp
    EPDecr exp       -> inferNum exp
    EIncr  exp       -> inferNum exp
    EDecr  exp       -> inferNum exp
    EAnd   exp1 exp2 -> inferBin [Type_bool] env exp1 exp2
    EOr    exp1 exp2 -> inferBin [Type_bool] env exp1 exp2      
    ETimes exp1 exp2 -> inferBin   [Type_int, Type_double] env exp1 exp2
    EDiv   exp1 exp2 -> inferBin   [Type_int, Type_double] env exp1 exp2
    EPlus  exp1 exp2 -> inferBin   [Type_int, Type_double] env exp1 exp2
    EMinus exp1 exp2 -> inferBin   [Type_int, Type_double] env exp1 exp2
    ELt    exp1 exp2 -> inferXBool [Type_int, Type_double] exp1 exp2
    EGt    exp1 exp2 -> inferXBool [Type_int, Type_double] exp1 exp2
    ELtEq  exp1 exp2 -> inferXBool [Type_int, Type_double] exp1 exp2
    EGtEq  exp1 exp2 -> inferXBool [Type_int, Type_double] exp1 exp2
    EEq    exp1 exp2 -> inferXBool [Type_int, Type_double, Type_bool] exp1 exp2
    ENEq   exp1 exp2 -> inferXBool [Type_int, Type_double, Type_bool] exp1 exp2
    EAss exp1@(EId _) exp2 -> inferBin [Type_int, Type_double, Type_bool]      env exp1 exp2
    EAss exp1 exp2         -> fail $ "Error de Expresiones " 
    
    EApp id exps     -> do (args, r) <- lookupFun env id
                           exps'     <- mapM (inferExp env) exps
                           if args >= exps'
                           then return r
                           else fail $ "Error de argumentos"
    
    where inferNum exp  = do typ <- inferExp env exp
                             if typ `elem` [Type_int, Type_double]
                             then return typ
                             else fail $ "Erro se detecto un tipo invalido "++ show typ    
          inferXBool x exp1 exp2 = do inferBin x env exp1 exp2
                                      return Type_bool
        
