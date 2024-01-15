import Data.List
import Data.Maybe
import Data.Char
-- Terms
data LambdaExpr = Var String | App LambdaExpr LambdaExpr | Abs String LambdaExpr | Y
        deriving (Show, Eq)
-- Tokens
data LambdaToken = LPar | RPar | Dot | Backslash | VarToken String | Err String | YComb | PT LambdaExpr | AssignOp | Command Commands
        deriving (Show, Eq)
-- Commands
data Commands = QuitC | PrintC | StepC Int 
    deriving (Show, Eq)
-- Environment
type Env = [(String, LambdaExpr)]

-- Lexer
-- Process the user’s input (string)  into a list of tokens (LambdaToken)
lexer :: String -> [LambdaToken]
lexer "" = []
lexer ('\n' : xs) = lexer xs
lexer (' ' : xs) = lexer xs
lexer ('(' : xs) = LPar : lexer xs
lexer (')' : xs) = RPar : lexer xs
lexer ('.' : xs) = Dot : lexer xs
lexer ('=' : xs) = AssignOp : lexer xs
lexer ('s':'t':'e':'p':' ':xs) = Command (StepC (read num)) : lexer rest
    where (num, rest) = span isDigit xs
lexer (c:cs)
    | isAlpha c =
        let (var, rest) = span isAlphaNum (c:cs) -- Alphanumeric chars are variable names
        in VarToken var : lexer rest
    | c == '\\' = Backslash : lexer cs -- Backslash character for abstraction
    | isLower c = 
        let (var, rest) = span (\x -> isAlphaNum x || x == ' ') (c:cs) -- Var names can be lowercase
        in VarToken var : lexer rest 
    | otherwise = Err ("Error: " ++ [c]) : lexer cs  -- Anything else is error

-- Shift Reducer
-- Performs shift-reduce parsing on tokens. 
sr :: [LambdaToken] -> [LambdaToken] -> [LambdaToken]
sr (VarToken v : ts) q = sr (PT (Var v) : ts) q
sr (YComb : s) q = sr (PT Y : s) q
sr (PT t2 : PT t1 : s) q = sr (PT (App t1 t2) : s) q
sr s (LPar : q) = sr (LPar : s) q 
sr (RPar : PT e : LPar  : s) q = sr (PT e : s) q
sr (PT t : Dot : PT (Var v) : Backslash : s) q = sr (PT (Abs v t) : s) q
sr s (Err e : q) = [Err ("Error: " ++ show q ++ ": " ++ e)]
sr s (q : qs) = sr (q : s) qs
sr s [] = s

-- Parser
-- Parses list of tokens into term string
parser :: [LambdaToken] -> Either LambdaExpr String
parser tokens =
    case result of
        [PT term] -> Left term
        [Err errMsg] -> Right errMsg -- Error if cannot be parsed
        s -> Right $ "Parsing error " ++ show s
    where
        result = sr [] tokens

-- allVars
-- Generates all possible variable names.
allVars :: [String]
allVars = "" : rest
  where
    rest = allVars >>= (\var -> [var ++ [c] | c <- ['A' .. 'Z']])

-- freshVar
-- Generates a fresh variable name.
freshVar :: [String] -> String
freshVar xs =
  let ids = map (`elemIndex` allVars) xs
      index = maximum (0 : catMaybes ids)
   in allVars !! (index + 1)

-- fv
-- List of free Variables for an expression.
fv :: LambdaExpr -> [String]
fv (Var x) = [x]
fv (App s t) = nub $ fv s ++ fv t
fv (Abs x t) = filter (/= x) (fv t)

-- subst
-- Substitutes an expression for a given expression.
subst :: (String,LambdaExpr) -> LambdaExpr -> LambdaExpr
subst (x,s) (Var y) -- If var substituted matches curr var, replace with given expression
    | y == x = s 
    | otherwise = Var y
subst (x, newV) (App t1 t2) = App (subst (x,t1) newV)(subst (x,t2) newV) -- apply substitution recursively
subst (x,a) t@(Abs y newV)
    | x == y = t -- if bound variable, no substitution 
    | not (elem y (fv a)) = Abs y (subst (x,a) newV) -- replace bound variable
    | otherwise =
      let y' = freshVar (x : y : fv a ++ fv t) -- generate fresh variable
          newV' = subst (y,Var y') newV -- subst var with fresh var 
       in Abs y' (subst (x,a) newV') -- apply subst

-- tsub
-- Substitutes (single) an expression for a given variable in expression.
-- Used for substAll.
tsub :: (String, LambdaExpr) -> LambdaExpr -> LambdaExpr
tsub (a, t) (Var b) | a == b = t
                    | otherwise = Var b
tsub (a, t) (App t1 t2) = App (tsub (a, t) t1) (tsub (a, t) t2)
tsub (a, t) (Abs x t') = Abs x (tsub (a, t) t')
tsub _ t = t

-- substAll 
-- Applies substitution to the expression in the entire environment.
substAll :: Env -> LambdaExpr -> LambdaExpr
substAll [] t = t
substAll (at:ts) t = substAll ts (tsub at t)

-- update
-- Updates environment with new variable binding.
update :: String -> LambdaExpr -> Env -> Env
update x e [] = [(x, e)]
update x e ((z, v):env) | x == z = (x, e) : env
                       | otherwise = (z, v) : update x e env

-- eval
-- Reduces lambda expressions. If application is abstraction applied to arg,
-- perform beta reduction. 
eval :: LambdaExpr -> LambdaExpr
eval (Var x) = Var x  -- Variables remain unchanged
eval (App (Abs x t1) t2) = subst (x, t2) t1  -- Beta reduction
eval (App t1 t2) = App (eval t1) (eval t2)  -- Evaluate function and argument
eval (Abs x t) = Abs x (eval t)  -- Evaluate the body of an abstraction
eval _ = error "No rule can be applied."


-- performRed
-- Performs reduction steps in REPL at a number specified by user.
performRed :: Int -> Env -> IO ()
performRed n env =
    if n <= 0
        then repl env
        else do
            let reducedEnv = reduce env
            putStrLn $ "Step " ++ show n ++ ": Environment after reduction - " ++ show reducedEnv
            performRed (n - 1) reducedEnv

-- reduce
-- Reduces expressions in the environment.
reduce :: Env -> Env
reduce [] = []
reduce ((var, expr) : rest) = (var, substAll rest (eval expr)) : reduce rest -- reduce each binding in environment

-- main
-- Initiates REPL.
main :: IO ()
main = do
    putStrLn "Lambda Calculus Calculator"
    putStrLn "Type 'exit' to quit."
    >> repl []

-- repl
-- REPL, interactive environment that gives the following options to user:
-- exit program
-- evaluate expression
-- assign variable (ex. I = \x.x)
-- step through reduction
repl :: Env -> IO ()
repl env = do
    putStr "\\> "
    input <- getLine
    if input == "exit"
        then putStrLn "Exiting."
        else do
            let tokens = lexer input -- lexer input
            case tokens of
                [Command (StepC n)] -> do -- step through reduction
                    putStrLn $ "Stepping " ++ show n ++ " times:"
                    performRed n env
                (VarToken var : AssignOp : xs) -> do -- assign variable
                    putStrLn $ "Variable assignment: " ++ var
                    case sr [] xs of
                        [PT e] -> do
                            let updatedEnv = update var e env -- update environment
                            putStrLn $ "Updated environment: " ++ show updatedEnv
                            repl updatedEnv
                        s -> putStrLn ("Error" ++ show s) >> repl env
                ts -> case parser tokens of -- parse input
                    Left expression -> do
                        putStrLn $ "Parsed expression: " ++ show expression
                        let evaluatedExpression = eval (substAll env expression)
                        putStrLn $ "Evaluated expression: " ++ show evaluatedExpression
                        repl env
                    Right errMsg -> do
                        putStrLn $ "Error: " ++ errMsg
                        repl env