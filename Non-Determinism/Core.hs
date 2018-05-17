module Core where

import Control.Monad (liftM2)
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- Core syntax
--------------------------------------------------------------------------------

type Ident = String
data Core = CInt Integer | CAdd Core Core | CMult Core Core
          | CBool Bool | CIs0 Core | CIf Core Core Core
          | CVar Ident | CLam Ident CType Core | CApp Core Core | CLet Ident Core Core
          | CPair Core Core | CLetPair Ident Ident Core Core
          | CUnit | CLetUnit Core Core
          | CInl CType CType Core | CInr CType CType Core
          | CCase Core (Ident, Core) (Ident, Core)
          | CFix Core
          | CFail CType | COr Core Core

  deriving (Eq, Show)

data CType = CTInt | CTBool | CTFun CType CType
           | CTProd CType CType | CTOne
           | CTSum CType CType
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Typing and type checking
--------------------------------------------------------------------------------

type TEnv = [(Ident, CType)]

check :: TEnv -> Core -> Maybe CType
check _ (CInt _) =
    return CTInt
check g (CAdd e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check g (CMult e1 e2) =
    do CTInt <- check g e1
       CTInt <- check g e2
       return CTInt
check _ (CBool _) =
    return CTBool
check g (CIs0 e) =
    do CTInt <- check g e
       return CTBool
check g (CIf e1 e2 e3) =
    do CTBool <- check g e1
       t2 <- check g e2
       t3 <- check g e3
       if t2 == t3 then return t2 else Nothing
check g (CVar x) =
    lookup x g
check g (CLam x t1 e) =
    do t2 <- check ((x, t1):g) e
       return (CTFun t1 t2)
check g (CApp e1 e2) =
    do CTFun t1 t2 <- check g e1
       t1' <- check g e2
       if t1 == t1' then return t2 else Nothing
check g (CLet x e1 e2) =
    do t <- check g e1
       check ((x, t) : g) e2
check g (CPair e1 e2) =
    do t1 <- check g e1
       t2 <- check g e2
       return (CTProd t1 t2)
check g (CLetPair x1 x2 e1 e2) =
    do CTProd t1 t2 <- check g e1
       check ((x1, t1) : (x2, t2) : g) e2
check g CUnit =
    return CTOne
check g (CLetUnit e1 e2) =
    do CTOne <- check g e1
       check g e2
check g (CInl t1 t2 e) =
    do t <- check g e
       if t == t1 then return (CTSum t1 t2) else Nothing
check g (CInr t1 t2 e) =
    do t <- check g e
       if t == t2 then return (CTSum t1 t2) else Nothing
check g (CCase e (x1, e1) (x2, e2)) =
    do CTSum t1 t2 <- check g e
       u1 <- check ((x1, t1) : g) e1
       u2 <- check ((x2, t2) : g) e2
       if u1 == u2 then return u1 else Nothing
check g (CFix f) =
    do CTFun t (CTFun u v) <- check g f
       if t == CTFun u v then return t else Nothing
check g (CFail t) =
    Just t
check g (COr e1 e2) =
    do t1 <- check g e1
       t2 <- check g e2
       return t1

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data Value = VInt Integer | VBool Bool | VFun VEnv Ident Core
           | VPair Value Value | VUnit
           | VInl Value | VInr Value
  deriving (Eq, Show)

intermediate :: [Choices x] -> (Choices x)
intermediate ((Choices t1):t1List) =
    let (Choices intermediateList) = intermediate t1List in
        (Choices (merge t1 intermediateList))
intermediate finalList = (Choices [])

merge :: [x] -> [x] -> [x]
merge xs     []     = xs
merge []     ys     = ys
merge (x:xs) (y:ys) = x : y : merge xs ys


type VEnv = [(Ident, Value)]

-- Result data type: a list of possible results

data Choices t = Choices [t]

instance Show t => Show (Choices t) where
    show (Choices vs) = intercalate ", " (map show vs)

instance Functor Choices where
    fmap f = (>>= return . f)

instance Applicative Choices where
    pure = return
    (<*>) = liftM2 ($)

instance Monad Choices where
    return t1 = (Choices (t1:[]))
    Choices vs >>= f = intermediate(map f vs)

-- Evaluation

eval :: VEnv -> Core -> Choices Value
eval _ (CInt x) =
    return (VInt x)
eval h (CAdd e1 e2) =
    do VInt x1 <- eval h e1
       VInt x2 <- eval h e2
       return (VInt (x1 + x2))
eval h (CMult e1 e2) =
    do VInt x1 <- eval h e1
       VInt x2 <- eval h e2
       return (VInt (x1 * x2))
eval _ (CBool b) =
    return (VBool b)
eval h (CIs0 e) =
    do VInt x <- eval h e
       return (VBool (x == 0))
eval h (CIf e e1 e2) =
    do VBool b <- eval h e
       if b then eval h e1 else eval h e2
eval h (CVar x) =
    let Just v = lookup x h in return v
eval h (CLam x t e) =
    return (VFun h x e)
eval h (CApp e1 e2) =
    do VFun h' x e <- eval h e1
       v <- eval h e2
       eval ((x, v) : h') e
eval h (CLet x e1 e2) =
    do v <- eval h e1
       eval ((x, v) : h) e2
eval h (CPair e1 e2) =
    do v1 <- eval h e1
       v2 <- eval h e2
       return (VPair v1 v2)
eval h (CLetPair x1 x2 e1 e2) =
    do VPair v1 v2 <- eval h e1
       eval ((x1, v1) : (x2, v2) : h) e2
eval h (CFix f) =
    return (VFun h "$x" (CApp (CApp f (CFix f)) (CVar "$x")))
eval h CUnit =
    return VUnit
eval h (CLetUnit e1 e2) =
    do VUnit <- eval h e1
       eval h e2
eval h (CFail _) =
    Choices[]
eval h (COr e1 e2) =
    let Choices v1 = eval h e1 in
    let Choices v2 = eval h e2 in
    Choices (v1 ++ v2)