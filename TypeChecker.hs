module TypeChecker where 

import AbsJanŻakGramatyka
import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import System.IO

data PoorFunc a = Func ([Arg a], Type a, PoorEnv a)
data PoorEnv a = Env (Map.Map Ident (Type a), Map.Map Ident (PoorFunc a)) 

type WeakerMonadStack a b = ReaderT (PoorEnv b) (ExceptT String IO) a

typeEvalExpr :: Expr ErrorInfo -> IO ()
typeEvalExpr expr = do {
  res <- runExceptT ((runReaderT (typeEval expr) (Env (Map.empty, Map.empty)) )); 
  case res of 
    Right goodRes -> return ()
    Left badRes -> hPutStrLn stderr ("ERROR at " ++ badRes)
}

getPos :: Type ErrorInfo -> ErrorInfo
getPos x = 
  case x of 
    (Bool a) -> a
    (Int a) -> a
    (Str a) -> a
    (Void a) -> a
    (Array a _ _) -> a
   

isBool :: Type ErrorInfo -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
isBool var =
    case var of 
      Bool _ -> return (Void errDummy)
      x -> throwError (vShow (getPos x) ++ " : got " ++ showType var ++ ", expected Bool")

isInt :: Type ErrorInfo -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
isInt var =
    case var of 
      Int _ -> return (Void errDummy)
      x -> throwError (vShow (getPos x) ++ " : got " ++ showType var ++ ", expected Int")

isString :: Type ErrorInfo -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
isString var =
    case var of 
      Str _ -> return (Void errDummy)
      x -> throwError (vShow (getPos x) ++ " : " ++ showType var ++ ", expected String")


typeEval :: Expr ErrorInfo -> WeakerMonadStack (Type ErrorInfo) ErrorInfo 
typeEval (ELitInt a _) = return (Int a)
typeEval (ELitTrue a) = return (Bool a)
typeEval (ELitFalse a) = return (Bool a)
typeEval (EString a _) = return (Str a)


typeEval (Neg a expr) = do {
  n <- typeEval expr;
  isInt n;
  return (Int a)
}

typeEval (Not a expr) = do {
  val <- typeEval expr;
  isBool val;
  return (Bool a)
}

typeEval (EMul a expr1 strOp expr2) = do {
  n1 <- typeEval expr1;
  n2 <- typeEval expr2;
  isInt n1;
  isInt n2;
  return (Int a)
}

typeEval (EAdd a expr1 weakOp expr2) = do {
  n1 <- typeEval expr1;
  n2 <- typeEval expr2;
  case (n1, n2) of 
    (Int _, Int _) -> return (Int a)
    (Str _, Str _) -> 
      case weakOp of
        Plus a -> return (Str a)
        Minus a -> throwError ((vShow a) ++ " : You cannot substract strings")
    _ -> throwError ((vShow a) ++ " : You can add/substract Integers and Strings")
}

typeEval (ERel a expr1 relation expr2) = do {
  n1 <- typeEval expr1;
  n2 <- typeEval expr2;
  case (n1, n2) of 
    (Int _, Int _) -> return (Bool a)
    (Bool _, Bool _) -> case relation of 
                          Eq _ -> return (Bool a)
                          NotEq _ -> return (Bool a)
                          _ -> throwError ((vShow a) ++ " : You cannot " ++ (show relation) ++ " booleans")                              
    (Str _, Str _) -> case relation of 
                        Eq a -> return (Bool a)
                        NotEq a -> return (Bool a)
                        _ -> throwError ((vShow a) ++ " : You cannot " ++ show relation ++ " strings")                              

    _ -> throwError ((vShow a) ++ " : Unspecified relation of " ++ show relation)
}

typeEval (EAnd a expr1 expr2) = do {
  n1 <- typeEval expr1;
  n2 <- typeEval expr2;
  isBool n1;
  isBool n2;
  return (Bool a)
}

typeEval (EOr a expr1 expr2) = do {
  typeEval (EAnd a expr1 expr2)
}

typeEval (EVar_ a var) = do {
  Env (vEnv, _) <- ask;
  case (Map.member var vEnv) of
    True -> return (vEnv Map.! var)
    False -> throwError ((vShow a) ++ " : Variable " ++ fShow var ++ " is not defined")
}

typeEval (EVarArr_ a var) = do {
  Env (vEnv, _) <- ask;
  let (ArrIdent a ident (ELitInt _ _)) = var in
    case (Map.member ident vEnv) of
      True -> case (vEnv Map.! ident) of 
          (Array _ internalType _) -> return internalType
          _ -> throwError (vShow a ++ " : "++ fShow ident ++ " is not an array")
      False -> throwError ((vShow a) ++ " : Variable " ++ vShowExp var ++ " is not defined")
}

typeEval (EVar a var) = 
  case var of 
    (NormalIdent a ident) -> typeEval (EVar_ a ident)
    (ArrIdent a ident exp) -> do {
      val <- typeEval exp;
      isInt val;
      let varWithArr = ArrIdent a ident (ELitInt a 0) in 
        typeEval (EVarArr_ a varWithArr)
    }


typeEval (EApp err ident exprs) = do {
  Env (_, fEnv) <- ask;
  case ident of 
    (Ident "print") -> let exp = head exprs in do { 
        n <- typeEval exp;  
        case n of 
          Void _ -> throwError (vShow err ++  " : You can't print Voids")
          _ -> return (Void err)

    }
    _ -> case (Map.member ident fEnv) of
          True -> let (Func (args, wantedType, Env (vEnvBackThen, fEnvBackThen))) = fEnv Map.! ident in 
                    case (length(exprs) == length(args)) of
                      True -> do {
                        tryToMatch exprs (Prelude.map (\(ArgDef _ vType _) -> vType) args);
                        return wantedType
                      }
                      False -> throwError (vShow err ++ " : Function " ++ (fShow ident) ++ " expected " ++ (show (length(args))) ++ " arguments but " ++ (show (length(exprs))) ++ " was supplied")  
          False -> throwError (vShow err ++ " : Function " ++ fShow ident ++ " is not defined")
}

tryToMatch ::  [Expr ErrorInfo] -> [Type ErrorInfo] -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
tryToMatch exprs args = do {
  case exprs of 
    (h:t) -> do {
      val <- typeEval (h);
      if  (compareTypes val (head args)) then 
        tryToMatch t (tail args)
      else do {
        throwError (vShow (getPos (head args)) ++  " : Expected type " ++ showType (head args) ++ " but got " ++ showType (val))
      }
    }
    _ -> return (Void errDummy)
}

-------------------------------------------------- STATEMENTS ------------------------------------------------

typeExec :: [Stmt ErrorInfo] -> IO ()
typeExec stmt = do {
  res <- runExceptT ((runReaderT (typeExecStmts stmt) (Env (Map.empty, Map.empty)) )); 
  case res of 
    Right goodRes -> return ()
    Left badRes -> hPutStrLn stderr ("TYPING ERROR: " ++ badRes)
}


typeExecStmts :: [Stmt ErrorInfo] -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
typeExecStmts (s1:(s2:s3)) = do { 
  x <- typeExecSingleStmt s1;
  case x of 
    (Void _) -> local (typeModifyEnv s1) (typeExecStmts (s2:s3))
    _ -> return x
}

typeExecStmts (s1:[]) = do {
  val <- typeExecSingleStmt s1;
  return val
}

typeExecStmts ([]) = do {
  return (Void errDummy);
}


typeModifyEnv :: (Stmt ErrorInfo) -> (PoorEnv ErrorInfo) -> (PoorEnv ErrorInfo)
typeModifyEnv (Decl _ vType []) env = env 

typeModifyEnv (Decl _ vType (item:tail)) (Env (vEnv, fEnv)) = 
  case item of     
    (Init a vName _) -> typeModifyEnv (Decl a vType tail) (Env (Map.insert vName vType vEnv, fEnv))
    (EmpInit a vName ) -> typeModifyEnv (Decl a vType tail) (Env (Map.insert vName vType vEnv, fEnv))

typeModifyEnv (FunToStmt _ (FunDef _ fType fIdent args _)) (Env (vEnv, fEnv)) = 
  Env (vEnv, Map.insert fIdent (Func (args, fType, Env (vEnv, fEnv))) fEnv)

typeModifyEnv _ envs = envs


typeExecSingleStmt :: Stmt ErrorInfo -> WeakerMonadStack (Type ErrorInfo) ErrorInfo
typeExecSingleStmt (EmptySt a) = return (Void a)


typeExecSingleStmt (Decl err vType items) = do { 
  Env (vEnv, fEnv) <- ask;
  case items of 
    [] -> return (Void err)
    (h:tail) -> do {
                  case h of 
                    (Init err vName expr) -> do {
                        newVal <- typeEval expr;
                        if (compareTypes newVal vType) then do {
                          local (typeModifyEnv (Decl err vType [h])) (typeExecSingleStmt (Decl err vType tail))
                        }
                        else 
                          throwError (vShow err ++ " : Cannot match types in assignment")
                      }
                    (EmpInit err vName) -> do {
                        case vType of 
                          (Array err vArrType expr) -> do {
                            val <- typeEval expr;
                            case val of 
                              Int _ -> do {
                                local (typeModifyEnv (Decl err vType [h])) (typeExecSingleStmt (Decl err vType tail))
                              } 
                              _ -> throwError (vShow err ++ " : Array range must be of Integer type")
                          }
                          _ -> do {
                            local (typeModifyEnv (Decl err vType [h])) (typeExecSingleStmt (Decl err vType tail))
                          }
                    }
                }
}

typeExecSingleStmt (SExp err expr) = do {
  _ <- typeEval expr;
  return (Void err)
}


typeExecSingleStmt (ModToStmt err modifyStmt) = do {
  Env (vEnv, fEnv) <- ask;
  let ident = expToIdent (getIdentFromModStmt modifyStmt) in  
    case (Map.member ident vEnv) of
      False -> throwError (vShow err ++ " : " ++ fShow ident ++ " is not defined ")
      True -> 
        case modifyStmt of 
          (Assign err newIdent expr) -> do {
            newType <- typeEval expr;
            case newIdent of
              (ArrIdent _ _ ex) -> do {
                x <- typeEval ex;
                case x of
                  (Int _) ->
                    case (vEnv Map.! ident) of 
                      (Array _ vecType _) -> 
                        if not (compareTypes vecType newType) then                
                          throwError (vShow err ++ " : Cannot change type of " ++ vShowExp newIdent ++ " to " ++ showType newType)
                        else             
                          return (Void err)
                      _ -> throwError (vShow err ++ " : " ++ fShow ident ++ " is not an array")
                  _ -> throwError (vShow err ++ " : Array index must be an Int")
              }
              _ -> 
                if not (compareTypes (vEnv Map.! ident) newType) then
                  throwError (vShow err ++ " : Cannot change type of " ++ vShowExp newIdent ++ " to " ++ showType newType)
                else 
                  return (Void err)
          }
            
          (Incr err ident) -> typeExecSingleStmt(ModToStmt err (Assign err ident (EAdd err (EVar err ident) (Plus err) (ELitInt err 1))))
          (Decr err ident) -> typeExecSingleStmt(ModToStmt err (Assign err ident (EAdd err (EVar err ident) (Minus err) (ELitInt err 1))))
}

typeExecSingleStmt (Ret err expr) = do {
  n <- typeEval expr;
  case n of 
    (Void _) -> throwError (vShow err ++ " : Cannot return voids")  
    _ -> return n
}

typeExecSingleStmt (VRet err) = do {
  return (Void err)
}


typeExecSingleStmt (If err1 expr (BlockDef _ stmts)) = do {
  val <- typeEval expr;
  isBool val;
  typeExecStmts stmts
}

typeExecSingleStmt (IfElse err expr (BlockDef _ stmtsTrue) (BlockDef _ stmtsFalse)) = do {
  val <- typeEval expr;
  isBool val;
  typeExecStmts stmtsTrue;
  typeExecStmts stmtsFalse
}

typeExecSingleStmt (While err expr (BlockDef err2 stmts)) = do {
  val <- typeEval expr;
  isBool val;
  typeExecStmts stmts
}

typeExecSingleStmt (Break err) = do {
  return (Void err)
}

typeExecSingleStmt (Continue err) = do {
  return (Void err)
}

typeExecSingleStmt (StmToB _ (BlockDef _ stmts)) = do {
  typeExecStmts stmts;
}


typeExecSingleStmt (FunToStmt err (FunDef err2 fType ident args (BlockDef err3 block))) = do {
  x <- local (typeModifyEnv (FunToStmt err (FunDef err2 fType ident args (BlockDef err3 block)))) 
  (typeExecStmts ((Prelude.map (\(ArgDef _ vType ident) -> Decl err vType [EmpInit err ident]) args) ++ block));

  if (compareTypes x fType) then
    return (Void err)
  else 
    throwError (vShow err ++ " : function should return " ++ showType fType ++ " but got " ++ showType x) 
} 


typeExecSingleStmt (ForPscl err vName iniVal endingVal (BlockDef _ stmts))  = do {
  ini <- typeEval iniVal;
  end <- typeEval endingVal;
  isInt ini;
  isInt end;
  typeExecStmts ([Decl err (Int err) [EmpInit err vName]] ++ stmts)
}

typeExecSingleStmt (Const_ err _) = do {
  return (Void err)
}

typeExecSingleStmt (UnConst_ err _) = do {
  return (Void err)
}

typeProgram (ProgramDef err funcs) =
  let convertedProg = Prelude.map (\(funDef) -> (FunToStmt err funDef)) funcs in  
    let wholeProg = foldl (\acc el -> acc ++ [el]) [] convertedProg in do {  
      typeExec wholeProg
    }

runWithTypeCheck (ProgramDef err funcs) = 
    let convertedProg = Prelude.map (\(funDef) -> (FunToStmt err funDef)) funcs in  
    let wholeProg = foldl (\acc el -> acc ++ [el]) [] convertedProg in do {  
      res <- runExceptT ((runReaderT (typeExecStmts wholeProg) (Env (Map.empty, Map.empty)) )); 
      case res of 
        Right goodRes -> runProgram (ProgramDef err funcs)
        Left badRes -> hPutStrLn stderr ("TYPING ERROR: " ++ badRes)
    }
  