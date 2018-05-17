module Sugar where

import Control.Monad (guard)
import Data.Char (isLower, isUpper)
import Data.List (sortBy)
import Text.Parsec hiding (parse)
import Text.Parsec.Language
import Text.Parsec.Token as T

import Core

--------------------------------------------------------------------------------
-- Sugared syntax
--------------------------------------------------------------------------------

data Type = TInt | TBool | TFun Type Type
          | TDatatype String
  deriving (Eq, Show)

data Expr = EInt Integer | EAdd Expr Expr | EMult Expr Expr
          | EBool Bool | EIs0 Expr | EIf Expr Expr Expr
          | EVar Ident | ELam Ident Type Expr | EApp Expr Expr | ELet Ident Expr Expr
          | ECon Ident [Expr] | ECase Expr [(Ident, [Ident], Expr)]
          | EUnit | ELetUnit Expr Expr
          | EDatatype Ident [(Ident, [Type])] Expr
          | EFix Expr
          | EFail Type | EOr Expr Expr
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Desugaring
--------------------------------------------------------------------------------

type DtypeEnv = [(Ident, [(Ident, [CType])])]

prodT [] = CTOne
prodT ts = foldr1 CTProd ts

desugarTy :: DtypeEnv -> Type -> Maybe CType
desugarTy _ TInt =
    return CTInt
desugarTy _ TBool =
    return CTBool
desugarTy dtypes (TFun t1 t2) =
    do t1' <- desugarTy dtypes t1
       t2' <- desugarTy dtypes t2
       return (CTFun t1' t2')
desugarTy dtypes (TDatatype k) =
    do ctors <- lookup k dtypes
       return (foldr1 CTSum (map (prodT . snd) ctors))

desugar :: DtypeEnv -> Expr -> Maybe Core
desugar _ (EInt i) =
    return (CInt i)
desugar dtypes (EAdd e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CAdd e1' e2')
desugar dtypes (EMult e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CMult e1' e2')
desugar _ (EBool b) =
    return (CBool b)
desugar dtypes (EIs0 e) =
    do e' <- desugar dtypes e
       return (CIs0 e')
desugar dtypes (EIf e1 e2 e3) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       e3' <- desugar dtypes e3
       return (CIf e1' e2' e3')
desugar _ (EVar x) =
    return (CVar x)
desugar dtypes (ELam x t e) =
    do t' <- desugarTy dtypes t
       e' <- desugar dtypes e
       return (CLam x t' e')
desugar dtypes (EApp e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CApp e1' e2')
desugar dtypes (ELet x e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CLet x e1' e2')
desugar dtypes EUnit =
    return CUnit
desugar dtypes (ELetUnit e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (CLetUnit e1' e2')
desugar dtypes (EDatatype dtname ctors e) =
    do ctors' <- mapM desugarCtor ctors
       desugar ((dtname, sortBy (\x y -> compare (fst x) (fst y)) ctors') : dtypes) e
    where desugarCtor (ctor, ts) =
              do ts' <- mapM (desugarTy dtypes) ts
                 return (ctor, ts')
desugar dtypes (ECon k es) =
    do con <- buildCon
       es' <- mapM (desugar dtypes) es
       return (con (if null es then CUnit else foldr1 CPair es'))
    where lookupByCtor [] = Nothing
          lookupByCtor ((_, ctors) : rest)
              | k `elem` map fst ctors = Just ctors
              | otherwise = lookupByCtor rest
          buildCon =
              do ctors <- lookupByCtor dtypes
                 return (loop ctors)
              where leftType ts = prodT ts
                    rightType ctors = foldr1 CTSum (map (prodT . snd) ctors)
                    loop [(ctor, ts)]
                        | ctor == k = id
                    loop ((ctor, ts) : ctors)
                        | ctor == k = CInl (leftType ts) (rightType ctors)
                        | otherwise = CInr (leftType ts) (rightType ctors) . loop ctors
desugar _ (ECase e []) =
    Nothing
desugar dtypes (ECase e bs@((k, _, _):_)) =
    do ctors <- lookupByCtor dtypes
       e' <- desugar dtypes e
       buildCases ctors e'
    where lookupByCtor [] = Nothing
          lookupByCtor ((_, ctors) : rest)
              | k `elem` map fst ctors = Just ctors
              | otherwise = lookupByCtor rest
          buildBranch [] e  = ("$y", e)
          buildBranch [x] e = (x, e)
          buildBranch xs e  = ("$y", buildLets xs (CVar "$y") e)
              where buildLets [x, y] e1 e2 =
                        CLetPair x y e1 e2
                    buildLets (x : xs) e1 e2 =
                        CLetPair x "$x" e1 (buildLets xs (CVar "$x") e2)
          findBranch k [] = Nothing
          findBranch k ((k', vs, e) : bs)
              | k == k' = Just (vs, e)
              | otherwise = findBranch k bs
          buildCases [(k1, _), (k2, _)] e =
              do (vs1, e1) <- findBranch k1 bs
                 (vs2, e2) <- findBranch k2 bs
                 e1' <- desugar dtypes e1
                 e2' <- desugar dtypes e2
                 return (CCase e (buildBranch vs1 e1') (buildBranch vs2 e2'))
          buildCases ((k, _) : ctors) e =
              do (vs1, e1) <- findBranch k bs
                 e1' <- desugar dtypes e1
                 rest <- buildCases ctors (CVar "$x")
                 return (CCase e (buildBranch vs1 e1') ("$x", rest))
desugar dtypes (EFix e) =
    do e' <- desugar dtypes e
       return (CFix e')
desugar dtypes (EFail t) =
    do t' <- desugarTy dtypes t
       return (CFail t')
desugar dtypes (EOr e1 e2) =
    do e1' <- desugar dtypes e1
       e2' <- desugar dtypes e2
       return (COr e1' e2')


--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

parse :: String -> Either ParseError Expr
parse = runParser (terminal (whiteSpace l >> exprp)) () ""
    where l = makeTokenParser $
              haskellDef { commentLine = "--"
                         , reservedNames = ["True", "False", "if", "then", "else",
                                            "let", "in", "Int", "Bool",
                                            "case", "of", "data", "or", "fail"]
                         , reservedOpNames = ["+", "*", "\\", "->", ":", ",", ";", "|"] }

          terminal p = do x <- p
                          eof
                          return x
          identifier = T.identifier l
          reserved = T.reserved l
          reservedOp = T.reservedOp l
          parens = T.parens l
          brackets = T.brackets l
          lexeme = T.lexeme l
          comma = T.comma l

          variable = try (do v <- identifier
                             guard (isLower (head v))
                             return v) <?> "identifier"

          constructor = try (do v <- identifier
                                guard (isUpper (head v))
                                return v) <?> "constructor"

          exprp = lamp

          lamp = (do reservedOp "\\"
                     x <- identifier
                     reservedOp ":"
                     t <- atomtp
                     reservedOp "->"
                     e <- exprp
                     return (ELam x t e)) <|>
                 (do reserved "if"
                     e1 <- exprp
                     reserved "then"
                     e2 <- exprp
                     reserved "else"
                     e3 <- exprp
                     return (EIf e1 e2 e3)) <|>
                 (do reserved "data"
                     k <- constructor
                     reservedOp "="
                     ctors <- sepBy1 (do k <- constructor
                                         vs <- many typep
                                         return (k, vs))
                                     (reservedOp "|")
                     reserved "in"
                     e <- exprp
                     return (EDatatype k ctors e)) <|>
                 (do reserved "case"
                     e <- exprp
                     reserved "of"
                     bs <- sepBy1 (do k <- constructor
                                      vs <- many variable
                                      reservedOp "->"
                                      e <- exprp
                                      return (k, vs, e))
                                  (reservedOp "|")
                     return (ECase e bs)) <|>
                 (do reserved "let"
                     x <- identifier
                     reservedOp "="
                     e1 <- exprp
                     reserved "in"
                     e2 <- exprp
                     return (ELet x e1 e2)) <|>
                 seqp

          seqp = chainl1 addp ((reservedOp ";" >> return ELetUnit) <|>
                               (reserved "or" >> return EOr))

          addp = chainl1 multp ((reservedOp "+" >> return EAdd) <|>
                                (reservedOp "-" >> return (\e1 e2 -> EAdd e1 (EMult e2 (EInt (-1))))))

          multp = chainl1 applp (reservedOp "*" >> return EMult)

          applp = (do k <- constructor
                      es <- many atomp
                      return (ECon k es)) <|>
                  (do es <- many1 atomp
                      case es of
                        [EVar "isz", e] -> return (EIs0 e)
                        [EVar "fix", e] -> return (EFix e)
                        _ -> return (foldl1 EApp es))

          atomp = choice [ EInt `fmap` lexeme intConst
                         , EBool `fmap` boolConst
                         , EVar `fmap` identifier
                         , EFail `fmap` (reserved "fail" >> brackets typep)
                         , do me <- parens (optionMaybe exprp)
                              case me of
                                Nothing -> return EUnit
                                Just e  -> return e ]

          intConst = do ds <- many1 digit
                        return (read ds)

          boolConst = (reserved "True" >> return True) <|>
                      (reserved "False" >> return False)

          typep = chainr1 atomtp (reservedOp "->" >> return TFun)

          atomtp = (reserved "Int" >> return TInt) <|>
                   (reserved "Bool" >> return TBool) <|>
                   (TDatatype `fmap` constructor) <|>
                   parens typep
