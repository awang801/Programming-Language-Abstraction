module Main where

import Data.List (partition)
import System.Environment (getArgs)
import System.IO (hSetBuffering, BufferMode(..), stdout)

import Core
import Sugar as D

check' e = case check [] e of
             Nothing -> Left "type error"
             Just t  -> Right t

eval' e = return (eval [] e)

go s = let result = do e <- parse s
                       e' <- desugar e
                       _ <- check' e'
                       return (show (eval [] e'))
       in case result of
            Left e -> putStrLn ("ERROR: " ++ show e)
            Right s -> putStrLn s
    where parse s = case D.parse s of
                      Left err -> Left (show err)
                      Right e  -> Right e
          desugar e = case D.desugar [] e of
                        Nothing -> Left "desugaring error"
                        Just e  -> Right e


main = do args <- getArgs
          let print (Left err) = putStrLn ("ERROR: " ++ err)
              print (Right v)  = putStrLn v
              repl = do putStr "> "
                        s <- getLine
                        if s == ":q"
                        then return ()
                        else do go s
                                repl

          if null args
          then do hSetBuffering stdout NoBuffering
                  repl
          else mapM_ (\file -> readFile file >>= go) args
