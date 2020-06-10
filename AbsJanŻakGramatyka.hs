module AbsJanŻakGramatyka where

-- Haskell module generated by the BNF converter

import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import System.IO
import qualified Data.Set as Set

newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
data Program a = ProgramDef a [FuncDecl a]
  deriving (Eq, Ord, Show, Read)

instance Functor Program where
    fmap f x = case x of
        ProgramDef a funcdecls -> ProgramDef (f a) (map (fmap f) funcdecls)
data FuncDecl a = FunDef a (Type a) Ident [Arg a] (Block a)
  deriving (Eq, Ord, Show, Read)

instance Functor FuncDecl where
    fmap f x = case x of
        FunDef a type_ ident args block -> FunDef (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)
data Arg a = ArgDef a (Type a) Ident
  deriving (Eq, Ord, Show, Read)

instance Functor Arg where
    fmap f x = case x of
        ArgDef a type_ ident -> ArgDef (f a) (fmap f type_) ident
data Stmt a
    = FunToStmt a (FuncDecl a)
    | EmptySt a
    | StmToB a (Block a)
    | Decl a (Type a) [Item a]
    | ModToStmt a (ModifyStmt a)
    | Ret a (Expr a)
    | VRet a
    | If a (Expr a) (Block a)
    | IfElse a (Expr a) (Block a) (Block a)
    | While a (Expr a) (Block a)
    | ForPscl a Ident (Expr a) (Expr a) (Block a)
    | SExp a (Expr a)
    | Break a
    | Continue a
    | Const_ a Ident    
    | UnConst_ a Ident
    | ForPscl_ a Ident Integer Integer [Stmt a] 

    
  deriving (Eq, Ord, Show, Read)

instance Functor Stmt where
    fmap f x = case x of
        FunToStmt a funcdecl -> FunToStmt (f a) (fmap f funcdecl)
        EmptySt a -> EmptySt (f a)
        StmToB a block -> StmToB (f a) (fmap f block)
        Decl a type_ items -> Decl (f a) (fmap f type_) (map (fmap f) items)
        ModToStmt a modifystmt -> ModToStmt (f a) (fmap f modifystmt)
        Ret a expr -> Ret (f a) (fmap f expr)
        VRet a -> VRet (f a)
        If a expr block -> If (f a) (fmap f expr) (fmap f block)
        IfElse a expr block1 block2 -> IfElse (f a) (fmap f expr) (fmap f block1) (fmap f block2)
        While a expr block -> While (f a) (fmap f expr) (fmap f block)
        ForPscl a ident expr1 expr2 block -> ForPscl (f a) ident (fmap f expr1) (fmap f expr2) (fmap f block)
        SExp a expr -> SExp (f a) (fmap f expr)
        Break a -> Break (f a)
        Continue a -> Continue (f a)
data ExpIdent a = ArrIdent a Ident (Expr a) | NormalIdent a Ident
  deriving (Eq, Ord, Show, Read)

instance Functor ExpIdent where
    fmap f x = case x of
        ArrIdent a ident expr -> ArrIdent (f a) ident (fmap f expr)
        NormalIdent a ident -> NormalIdent (f a) ident
data Block a = BlockDef a [Stmt a]
  deriving (Eq, Ord, Show, Read)

instance Functor Block where
    fmap f x = case x of
        BlockDef a stmts -> BlockDef (f a) (map (fmap f) stmts)
data Item a = Init a Ident (Expr a) | EmpInit a Ident
  deriving (Eq, Ord, Show, Read)

instance Functor Item where
    fmap f x = case x of
        Init a ident expr -> Init (f a) ident (fmap f expr)
        EmpInit a ident -> EmpInit (f a) ident
data ModifyStmt a
    = Assign a (ExpIdent a) (Expr a)
    | Incr a (ExpIdent a)
    | Decr a (ExpIdent a)
  deriving (Eq, Ord, Show, Read)

instance Functor ModifyStmt where
    fmap f x = case x of
        Assign a expident expr -> Assign (f a) (fmap f expident) (fmap f expr)
        Incr a expident -> Incr (f a) (fmap f expident)
        Decr a expident -> Decr (f a) (fmap f expident)
data Type a
    = Int a | Str a | Bool a | Void a | Array a (Type a) (Expr a)
  deriving (Eq, Ord, Show, Read)

instance Functor Type where
    fmap f x = case x of
        Int a -> Int (f a)
        Str a -> Str (f a)
        Bool a -> Bool (f a)
        Void a -> Void (f a)
        Array a type_ expr -> Array (f a) (fmap f type_) (fmap f expr)
data Expr a
    = EVar a (ExpIdent a)
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EApp a Ident [Expr a]
    | EString a String
    | Neg a (Expr a)
    | Not a (Expr a)
    | EMul a (Expr a) (StrOp a) (Expr a)
    | EAdd a (Expr a) (WeakOp a) (Expr a)
    | ERel a (Expr a) (RelOp a) (Expr a)
    | EAnd a (Expr a) (Expr a)
    | EOr a (Expr a) (Expr a)
    | EVar_ a Ident
    | EVarArr_ a (ExpIdent a)
    | ELitArray_ a [Expr a]
  deriving (Eq, Ord, Show, Read)

instance Functor Expr where
    fmap f x = case x of
        EVar a expident -> EVar (f a) (fmap f expident)
        ELitInt a integer -> ELitInt (f a) integer
        ELitTrue a -> ELitTrue (f a)
        ELitFalse a -> ELitFalse (f a)
        EApp a ident exprs -> EApp (f a) ident (map (fmap f) exprs)
        EString a string -> EString (f a) string
        Neg a expr -> Neg (f a) (fmap f expr)
        Not a expr -> Not (f a) (fmap f expr)
        EMul a expr1 strop expr2 -> EMul (f a) (fmap f expr1) (fmap f strop) (fmap f expr2)
        EAdd a expr1 weakop expr2 -> EAdd (f a) (fmap f expr1) (fmap f weakop) (fmap f expr2)
        ERel a expr1 relop expr2 -> ERel (f a) (fmap f expr1) (fmap f relop) (fmap f expr2)
        EAnd a expr1 expr2 -> EAnd (f a) (fmap f expr1) (fmap f expr2)
        EOr a expr1 expr2 -> EOr (f a) (fmap f expr1) (fmap f expr2)
data WeakOp a = Plus a | Minus a
  deriving (Eq, Ord, Show, Read)

instance Functor WeakOp where
    fmap f x = case x of
        Plus a -> Plus (f a)
        Minus a -> Minus (f a)
data StrOp a = Mul a | Div a | Mod a
  deriving (Eq, Ord, Show, Read)

instance Functor StrOp where
    fmap f x = case x of
        Mul a -> Mul (f a)
        Div a -> Div (f a)
        Mod a -> Mod (f a)
data RelOp a
    = Less a | LessOrEq a | Greater a | GrtOrEq a | Eq a | NotEq a
  deriving (Eq, Ord, Show, Read)

instance Functor RelOp where
    fmap f x = case x of
        Less a -> Less (f a)
        LessOrEq a -> LessOrEq (f a)
        Greater a -> Greater (f a)
        GrtOrEq a -> GrtOrEq (f a)
        Eq a -> Eq (f a)
        NotEq a -> NotEq (f a)



-------------------------------------- DECLARATIONS OF TYPES -------------------------------
data VarType = VInt Integer | VString String | VBool Bool | VArr (Vector.Vector VarType) | VVoid | VEmpty | VBreak ErrorInfo | VContinue ErrorInfo

type ErrorInfo = Maybe (Int, Int)

vShow :: ErrorInfo -> String
vShow errInfo = 
    case errInfo of 
        Just (x,y) -> "(" ++ show x ++ "," ++ show y ++ ")"
        _ -> "()"  

errDummy = Just (0,0)

instance Show VarType where
  show x = 
    case x of 
      VInt x -> show x
      VString str -> show str
      VBool x -> show x
      _ -> ""

instance Eq VarType where
  x == y = 
    case (x, y) of
      (VInt x1, VInt y1) -> x1 == y1
      (VString x1, VString y1) -> x1 == y1
      (VBool x1, VBool y1) -> x1 == y1
      (VEmpty, VEmpty) -> True
      _ -> False


vShowExp :: ExpIdent ErrorInfo -> String
vShowExp x = 
   (case x of 
      (ArrIdent _ (Ident vName) (ELitInt _ n) ) -> (stripString (show vName) ++ "[" ++ show n ++ "]")
      (NormalIdent _ (Ident vName) ) -> (show vName))

fShow :: Ident -> String 
fShow (Ident fName) = show fName


data Func a = CFunc (Integer, Map.Map Ident Integer, Map.Map Ident (Func a), (Type a), [Arg a])
data Env a = CEnv (Map.Map Ident Integer, Map.Map Ident (Func a), Integer, Set.Set Integer) 
type Store a = (Map.Map Integer VarType, Map.Map Integer (Block a))

type MonadStack a b = ReaderT (Env b) (StateT (Store b) (ExceptT String IO)) a


-------------------------------------- SIMPLE EXPRESSIONS -------------------------------
identToExp :: Ident -> ExpIdent ErrorInfo
identToExp ident = (NormalIdent errDummy ident)

expToIdent :: ExpIdent ErrorInfo -> Ident 
expToIdent (ArrIdent errDummy ident _) = ident
expToIdent (NormalIdent _ ident) = ident

stripExpIdent :: ExpIdent ErrorInfo -> ExpIdent ErrorInfo
stripExpIdent (NormalIdent _ ident) = (NormalIdent errDummy ident)
stripExpIdent (ArrIdent _ ident (ELitInt _ x)) = (ArrIdent errDummy ident (ELitInt errDummy x))


evalExpr :: Expr ErrorInfo -> IO ()
evalExpr expr = do {
  res <- runExceptT ((runStateT (runReaderT (eval expr) (CEnv (Map.empty, Map.empty, 0, Set.empty))) (Map.empty, Map.empty))); 
  case res of 
    Right goodRes -> return ()
    Left badRes -> hPutStrLn stderr ("ERROR at " ++ badRes)
}

stripString :: String -> String
stripString (h:t) = 
  let sRev = reverse t in 
    let (h2:t2) = sRev in 
      reverse t2

eval :: Expr ErrorInfo -> MonadStack VarType ErrorInfo 
eval (ELitInt a n) = return (VInt n)
eval (ELitTrue a) = return (VBool True)
eval (ELitFalse a) = return (VBool False)
eval (EString a str) = return (VString (stripString str))

eval (Neg a expr) = do {
  n <- eval expr;
  case n of 
    (VInt nestedVal) -> return (VInt (- nestedVal))
    _ -> throwError ((vShow a) ++ " : Negation must be applied on Int type")
}

eval (Not a expr) = do {
  val <- eval expr;
  case val of 
    (VBool nestedVal) -> return (VBool (not nestedVal))
    _ -> throwError ((vShow a) ++ " : Not must be applied on Bool type")
}

eval (EMul a expr1 strOp expr2) = do {
  n1 <- eval expr1;
  n2 <- eval expr2;
  case (n1, n2) of 
    (VInt nested1, VInt nested2) -> case strOp of 
                                      Mul a -> return (VInt (nested1 * nested2))
                                      Div a -> 
                                        case nested2 of 
                                          0 -> throwError ((vShow a) ++ " : You cannot divide by 0")
                                          _ -> return (VInt (nested1 `div` nested2))

                                      Mod a -> case nested2 of 
                                          0 -> throwError ((vShow a) ++ " : You cannot modulo by 0")
                                          _ -> return (VInt (nested1 `mod` nested2))
    _ -> throwError ((vShow a) ++ " : You can only multiple/divide/modulo Integers")
}

eval (EAdd a expr1 weakOp expr2) = do {
  n1 <- eval expr1;
  n2 <- eval expr2;
  case (n1, n2) of 
    (VInt nested1, VInt nested2) -> case weakOp of 
                                      Plus a -> return (VInt (nested1 + nested2))
                                      Minus a -> return (VInt (nested1 - nested2))
    (VString str1, VString str2) -> case weakOp of
                                      Plus a -> return (VString (str1 ++ str2))
                                      Minus a -> throwError ((vShow a) ++ " : You cannot substract strings")
    _ -> throwError ((vShow a) ++ " : You can add/substract Integers and Strings")
}

eval (ERel a expr1 relation expr2) = do {
  n1 <- eval expr1;
  n2 <- eval expr2;
  case (n1, n2) of 
    (VInt nested1, VInt nested2) -> case relation of 
                                      Less a -> return (VBool (nested1 < nested2))
                                      LessOrEq a -> return (VBool (nested1 <= nested2))
                                      Greater a -> return (VBool (nested1 > nested2))
                                      GrtOrEq a -> return (VBool (nested1 >= nested2))
                                      Eq a -> return (VBool (nested1 == nested2))
                                      NotEq a -> return (VBool (nested1 /= nested2))
    (VBool v1, VBool v2) -> case relation of 
                              Eq a -> return (VBool (v1 == v2))
                              NotEq a -> return (VBool (v1 /= v2))
                              _ -> throwError ((vShow a) ++ " : You cannot " ++ (show relation) ++ " booleans")                              
    (VString str1, VString str2) -> case relation of 
                                      Eq a -> return (VBool (str1 == str2))
                                      NotEq a -> return (VBool (str1 /= str2))
                                      _ -> throwError ((vShow a) ++ " : You cannot " ++ show relation ++ " strings")                              

    _ -> throwError ((vShow a) ++ " : Unspecified relation of " ++ show relation)
}

eval (EAnd a expr1 expr2) = do {
  n1 <- eval expr1;
  n2 <- eval expr2;
  case (n1, n2) of
    (VBool nested1, VBool nested2) -> return (VBool (nested1 && nested2))
    _ -> throwError ((vShow a) ++ " : You can only AND Booleans")
}

eval (EOr a expr1 expr2) = do {
  n1 <- eval expr1;
  n2 <- eval expr2;
  case (n1, n2) of
    (VBool nested1, VBool nested2) -> return (VBool (nested1 || nested2))
    _ -> throwError ((vShow a) ++ " : You can only OR Booleans")
}

eval (EVar_ a var) = do {
  CEnv (vEnv, _, _, _) <- ask;
  (vStore, _) <- get;
  case (Map.member var vEnv) of
    True -> let location = ((vEnv) Map.! var) in  
              return ((vStore) Map.! location)
    False -> throwError ((vShow a) ++ " : Variable " ++ fShow var ++ " is not defined")
}

eval (EVarArr_ a var) = do {
  CEnv (vEnv, _, _, _) <- ask;
  (vStore, _) <- get;
  let (ArrIdent a ident (ELitInt _ index)) = var in
    case (Map.member ident vEnv) of
      True -> 
        let location = ((vEnv) Map.! ident) in
          case (vStore Map.! location) of 
            (VArr vec) -> 
              let indexInt = fromIntegral index in 
                if length vec <= indexInt || indexInt < 0 then
                  throwError (vShow a ++ " : index out of bounds")
                else
                  return (vec Vector.! indexInt)
            _ -> throwError (vShow a ++ " : " ++ fShow ident ++ " is accessed as an array while it is not an array")
      False -> throwError ((vShow a) ++ " : Variable " ++ vShowExp var ++ " is not defined")
}

eval (EVar a var) = 
  case var of 
    NormalIdent a ident -> eval (EVar_ a ident)
    ArrIdent a ident exp -> do {
      val <- eval exp;
      case val of 
      (VInt n) ->
        let varWithArr = ArrIdent a ident (ELitInt a n) in 
          eval (EVarArr_ a varWithArr)
      _ -> throwError ((vShow a) ++ " : Array index must be of Integer type")
    }


eval (EApp err ident exprs) = do {
  CEnv (_, fEnv, lastLoc, constedVars) <- ask;
  (_, fStore) <- get;
  case ident of 
    (Ident "print") -> case (length exprs) of 
      1 -> let exp = head exprs in do { 
            n <- eval exp;  
            case n of 
              VVoid -> throwError (vShow err ++  " : You can't print Voids")
              _ -> do {
                      case n of 
                        VInt x -> do {
                          liftIO(print(x)); 
                          return VEmpty
                        }
                        VString str -> do {
                          liftIO(print(str)); 
                          return VEmpty
                        }
                        VBool v -> do {
                          liftIO(print(v)); 
                          return VEmpty
                        }
                  }
            }
      _ -> throwError (vShow err ++ " : print only accepts one argument")

    _ -> case (Map.member ident fEnv) of
          True -> let (CFunc (location, vEnvBackThen, fEnvBackThen, wantedType, args)) = fEnv Map.! ident in 
                    let func = fStore Map.! location in 
                      let (BlockDef a funcContent) = func in
                          case (length(exprs) == length(args)) of
                            True -> 
                              do {
                                calcExprs <- evalMany exprs;  
                                let decls = zipWith (\(ArgDef a vType vIdent) (val) -> (Decl a vType [Init a vIdent (varToExpr val)])) args (calcExprs) in 
                                  let newFEnv = (Map.insert ident (fEnv Map.! ident) fEnvBackThen) in do {
                                    x <- local (\_ -> CEnv (vEnvBackThen, newFEnv, lastLoc, constedVars)) (execStmts (decls ++ funcContent));
                                    case x of 
                                      VBreak err -> throwError (vShow err ++ " : Uncaught break")
                                      VContinue err -> throwError (vShow err ++ " : Uncaught continue")
                                      _ -> if(compareTypes (getType x) wantedType) then
                                            return x 
                                           else 
                                            throwError (vShow err ++ " : Function returned " ++ (showType (getType x)) ++ " but " ++ (showType wantedType) ++ " was expected")

                                }
                              }
                            False -> throwError (vShow err ++ " : Function " ++ (fShow ident) ++ " expected " ++ (show (length(args))) ++ " arguments but " ++ (show (length(exprs))) ++ " was supplied")  
                        
          False -> throwError (vShow err ++ " : Function " ++ fShow ident ++ " is not defined")
}


eval (ELitArray_ _ elements) = do {
  calcEl <- evalMany elements; 
  return (VArr (Vector.fromList (calcEl))) 
}

varToExpr :: VarType -> Expr ErrorInfo
varToExpr var = 
  case var of 
    VInt n -> ELitInt errDummy n
    VString s -> EString errDummy (['"'] ++ s ++ ['"'])
    VBool b -> case b of 
                 True -> ELitTrue errDummy
                 False -> ELitFalse errDummy
    VArr vec ->
      let unpacked = Vector.toList vec in 
        ELitArray_  errDummy ((Prelude.map (\el -> varToExpr el) unpacked))

evalMany :: [Expr ErrorInfo] -> MonadStack [VarType] ErrorInfo
evalMany [] = return ([])
evalMany (exp:tail) = do {
  n <- eval exp;
  ns <- evalMany tail;
  return (n:ns)
}

getIdentFromModStmt :: ModifyStmt ErrorInfo -> ExpIdent ErrorInfo
getIdentFromModStmt modifyStmt = 
  case modifyStmt of 
    Assign _ ident _ -> ident
    Incr _ ident -> ident
    Decr _ ident -> ident


getNameFromItem :: Item ErrorInfo -> Ident 
getNameFromItem item = 
  case item of
    (Init _ vName _) -> vName
    (EmpInit _ vName) -> vName
    
defValue :: Type ErrorInfo -> VarType
defValue val = 
  case val of 
    Int _ -> VInt 0
    Str _ -> VString ""
    Bool _ -> VBool True 
    _ -> VVoid

getType :: VarType -> Type ErrorInfo
getType var = 
  case var of 
    (VInt _) -> Int errDummy
    (VString _) -> Str errDummy
    (VBool _) -> Bool errDummy
    (VArr vec) -> Array errDummy (getType (vec Vector.! 0)) (ELitTrue errDummy)
    _ -> Void errDummy

compareTypes :: Type ErrorInfo -> Type ErrorInfo -> Bool
compareTypes t1 t2 = 
  case (t1, t2) of 
    (Int _, Int _) -> True
    (Str _, Str _) -> True
    (Bool _, Bool _) -> True
    (Void _, Void _) -> True
    (Array _ vec1 _, Array _ vec2 _) -> compareTypes (vec1) (vec2)
    _ -> False

showType :: Type ErrorInfo -> String
showType t = 
  case t of 
    (Int _) -> "Int"
    (Str _) -> "String"
    (Bool _) -> "Boolean"
    (Void _) -> "Void"
    (Array _ vec _) -> "Array of " ++ showType vec
    
    
typeMatch :: VarType -> VarType -> Bool
typeMatch val1 val2 = ((getType val1) == (getType val2))


getIdentFromArg :: Arg ErrorInfo -> String
getIdentFromArg (ArgDef _ _ (Ident id)) = id

-------------------------------------------------- STATEMENTS ------------------------------------------------

exec :: [Stmt ErrorInfo] -> IO ()
exec stmt = do {
  res <- runExceptT ((runStateT (runReaderT (execStmts stmt) (CEnv (Map.empty, Map.empty, 0, Set.empty))) (Map.empty, Map.empty))); 
  case res of 
    Right goodRes -> return ()
    Left badRes -> hPutStrLn stderr ("RUNTIME ERROR: " ++ badRes)
}


execStmts :: [Stmt ErrorInfo] -> MonadStack VarType ErrorInfo
execStmts (s1:(s2:s3)) = do { 
  x <- execSingleStmt s1;
  if x == VEmpty then
    local (modifyEnv s1) (execStmts (s2:s3))
  else 
    return x
}

execStmts (s1:[]) = do {
  val <- execSingleStmt s1;
  return val
}

execStmts ([]) = do {
  return VEmpty;
}


modifyEnv :: (Stmt ErrorInfo) -> (Env ErrorInfo) -> (Env ErrorInfo)
modifyEnv (Decl _ vType []) env = env 

modifyEnv (Decl _ vType (item:tail)) (CEnv (vEnv, fEnv, lastLoc, constedVars)) = 
  case item of     
    (Init a vName _) -> modifyEnv (Decl a vType tail) (CEnv (Map.insert vName lastLoc vEnv, fEnv, lastLoc + 1, constedVars))
    (EmpInit a vName ) -> modifyEnv (Decl a vType tail) (CEnv (Map.insert vName lastLoc vEnv, fEnv, lastLoc + 1, constedVars))

modifyEnv (FunToStmt _ (FunDef _ fType fIdent args _)) (CEnv (vEnv, fEnv, lastLoc, constedVars)) = 
  CEnv (vEnv, Map.insert fIdent (CFunc (lastLoc, vEnv, fEnv, fType, args)) fEnv, lastLoc + 1, constedVars)

modifyEnv (Const_ _ ident) (CEnv (vEnv, fEnv, lastLoc, constedVars)) = 
  CEnv (vEnv, fEnv, lastLoc, Set.insert (vEnv Map.! ident) constedVars)

modifyEnv (UnConst_ _ ident) (CEnv (vEnv, fEnv, lastLoc, constedVars)) = 
  CEnv (vEnv, fEnv, lastLoc, Set.delete (vEnv Map.! ident) constedVars)

modifyEnv _ envs = envs




execSingleStmt :: Stmt ErrorInfo -> MonadStack VarType ErrorInfo
execSingleStmt (EmptySt _) = return VEmpty

execSingleStmt (Decl _ vType items) = do { 
  CEnv (vEnv, _, vLastLoc, _) <- ask;
  (vStore, fStore) <- get;
  case items of 
    [] -> return VEmpty
    (h:tail) -> do {
                  case h of 
                    (Init err vName expr) -> do {
                        newVal <- eval expr;
                        if (compareTypes (getType newVal) vType) then do {
                          put(Map.insert vLastLoc newVal vStore, fStore);        
                          local (modifyEnv (Decl err vType [h])) (execSingleStmt (Decl err vType tail))
                        }
                        else 
                          throwError (vShow err ++ " : Cannot match types in assignment")
                      }
                    (EmpInit err vName) -> do {
                        case vType of 
                          (Array err vArrType expr) -> do {
                            val <- eval expr;
                            case val of 
                              VInt n -> do {
                                put(Map.insert vLastLoc (VArr (Vector.replicate (fromIntegral n) (defValue vArrType))) vStore, fStore);        
                                local (modifyEnv (Decl err vType [h])) (execSingleStmt (Decl err vType tail))
                              } 
                              _ -> throwError (vShow err ++ " : Array range must be of Integer type")
                          }
                          _ -> do {
                            put(Map.insert vLastLoc (defValue vType) vStore, fStore);        
                            local (modifyEnv (Decl err vType [h])) (execSingleStmt (Decl err vType tail))
                          }
                    }
                }
}

execSingleStmt (SExp _ expr) = do {
  _ <- eval expr;
  return VEmpty
}

execSingleStmt (ModToStmt err modifyStmt) = do {
  CEnv (vEnv, _, _, constedVars) <- ask;
  (vStore, fStore) <- get;
  let ident = expToIdent (getIdentFromModStmt modifyStmt) in  
    case (Map.member ident vEnv) of
      False -> throwError (vShow err ++ " : " ++ fShow ident ++ " is not defined ")
      True -> 
        let loc = vEnv Map.! ident in
          if (Set.member loc constedVars) then
            throwError (vShow err ++ " : " ++ fShow ident ++ " is const and cannot be modified") 
          else 
            case modifyStmt of 
              (Assign err ident expr) -> do {
                newVal <- eval expr;
                case ident of
                  (ArrIdent _ newIdent ex) -> do {
                    x <- eval ex;
                    case x of
                      (VInt val) ->
                        case (vStore Map.! loc) of 
                          (VArr vec) -> 
                            if not (typeMatch (vec Vector.! 1) newVal) then                
                              throwError (vShow err ++ " : Cannot change type of " ++ vShowExp ident ++ " to " ++ showType (getType newVal))
                            else             
                              if (length vec <= fromIntegral val || fromIntegral val < 0) then 
                                throwError (vShow err ++ " : " ++ show val ++ " is out of bounds")
                              else
                                let newVec = vec Vector.// [(fromIntegral val, newVal)] in do {
                                  put(Map.insert loc (VArr newVec) vStore, fStore);
                                  return VEmpty
                                }
                          _ -> throwError (vShow err ++ " : " ++ fShow newIdent ++ " is not an array")
                      _ -> throwError (vShow err ++ " : Array slices must be an Int")
                  }
                  _ -> 
                    if not (typeMatch (vStore Map.! loc) newVal) then
                      throwError (vShow err ++ " : Cannot change type of " ++ vShowExp ident ++ " to " ++ showType (getType newVal))
                    else do {
                      put(Map.insert loc newVal vStore, fStore);
                      return VEmpty
                    }
              }
              (Incr err ident) -> execSingleStmt(ModToStmt err (Assign err ident (EAdd err (EVar err ident) (Plus err) (ELitInt err 1))))
              (Decr err ident) -> execSingleStmt(ModToStmt err (Assign err ident (EAdd err (EVar err ident) (Minus err) (ELitInt err 1))))
}

execSingleStmt (Ret err expr) = do {
  n <- eval expr;
  case n of 
    (VVoid) -> throwError (vShow err ++ " : Cannot return voids")  
    _ -> return n
}

execSingleStmt (VRet _) = do {
  return VVoid
}

execSingleStmt (If err1 expr (BlockDef _ stmts)) = do {
  val <- eval expr;
  case val of 
    (VBool True) -> execStmts stmts
    (VBool False) -> return VEmpty
    _ -> throwError (vShow err1 ++ " : Condition in IF statement must be of Boolean type")
}

execSingleStmt (IfElse err expr (BlockDef _ stmtsTrue) (BlockDef _ stmtsFalse)) = do {
  val <- eval expr;
  case val of 
    (VBool True) -> execStmts stmtsTrue
    (VBool False) -> execStmts stmtsFalse
    _ -> throwError (vShow err ++ " : Condition in IF-ELSE statement must be of Boolean type")
}

execSingleStmt (While err expr (BlockDef err2 stmts)) = do {
  val <- eval expr;
  case val of 
    (VBool True) -> do {
      x <- execStmts stmts;
      case x of 
        VBreak _ -> return VEmpty
        VEmpty -> execStmts [(While err expr (BlockDef err2 stmts))]
        VContinue _ -> execStmts [(While err expr (BlockDef err2 stmts))]
        _ -> return x;
    }
    (VBool False) -> return VEmpty
    _-> throwError (vShow err ++ " : Condition in WHILE statement must be of Boolean type")
}

execSingleStmt (Break err) = do {
  return (VBreak err)
}
execSingleStmt (Continue err) = do {
  return (VContinue err)
}

execSingleStmt (StmToB _ (BlockDef _ stmts)) = do {
  execStmts stmts;
}

execSingleStmt (FunToStmt err (FunDef _ fType fIdent fArgs fContent)) = do {
  CEnv (vEnv, _, vLastLoc, _) <- ask;
  (vStore, fStore) <- get;

  let argNames = Prelude.map getIdentFromArg fArgs in 
    case (length (Set.fromList argNames) == length argNames) of 
      True -> do {
        put(vStore, Map.insert vLastLoc fContent fStore);        
        return VEmpty
      }
      False -> throwError (vShow err ++ " : Functions can't have duplicate argument names.")
} 

execSingleStmt (ForPscl err vName iniVal endingVal (BlockDef err2 stmts))  = do {
  ini <- eval iniVal;
  end <- eval endingVal;
  case (ini, end) of 
    (VInt iniVal, VInt endVal) ->
      execStmts ([Decl err (Int err) [(Init err vName (ELitInt err iniVal))]] ++ [ForPscl_ err vName iniVal endVal stmts])
    _ -> throwError (vShow err ++ " : Iterator in FOR must be of type Int")
}

execSingleStmt (Const_ _ ident) = do {
  return VEmpty
}

execSingleStmt (ForPscl_ err vName iniVal endingVal stmts) = 
  if(iniVal <= endingVal) then 
    do {
      execStmts ([Const_ err vName] ++ 
                 stmts ++ 
                 [UnConst_ err vName] ++ 
                 [ModToStmt err (Incr err (identToExp vName))] ++ 
                 [ForPscl_ err vName (iniVal + 1) endingVal stmts]);
    }
  else 
    return VEmpty

execSingleStmt (UnConst_ _ ident) = do {
  return VEmpty
}



runProgram (ProgramDef _ funcs) = do {
  searchForMain funcs [] 
}

searchForMain funcs functionsBefore =
  case funcs of 
    (h:t) -> case h of
               (FunDef _ (Int _) (Ident "main") _ (BlockDef err block)) ->
                  let allFuncs = reverse (h:functionsBefore) in 
                    exec (
                      (Prelude.map (\x -> FunToStmt err x) allFuncs) ++ 
                      [Decl err (Int err) [Init err (Ident "x") (EApp err (Ident "main") [])]]
                    )  
               (FunDef _ fType (Ident ident) args (BlockDef _ block)) -> 
                 searchForMain t (h:functionsBefore)
    _ -> hPutStrLn stderr "RUNTIME ERROR: main not found"
