import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

-- AST with named variables
data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  deriving (Eq, Show)

-- Free variables
freeVars :: Expr -> Set String
freeVars (Var x)     = Set.singleton x
freeVars (Lam x e)   = Set.delete x (freeVars e)
freeVars (App e1 e2) = freeVars e1 `Set.union` freeVars e2

-- Generate fresh variable not in the given set
freshVar :: Set String -> String -> String
freshVar used x =
  let candidates = x : [x ++ show i | i <- [1..]]
  in head (filter (`Set.notMember` used) candidates)

-- Capture-avoiding substitution [x ↦ s]e
subst :: String -> Expr -> Expr -> Expr
subst x s expr = case expr of
  Var y
    | y == x    -> s
    | otherwise -> Var y
  Lam y e1
    | y == x    -> Lam y e1
    | y `Set.notMember` freeVars s -> Lam y (subst x s e1)
    | otherwise ->
        let y' = freshVar (freeVars e1 `Set.union` freeVars s) y
            e1' = subst y (Var y') e1
        in Lam y' (subst x s e1')
  App e1 e2 -> App (subst x s e1) (subst x s e2)

-- One-step beta reduction
step :: Expr -> Maybe Expr
step expr = case expr of
  App (Lam x e1) e2 -> Just (subst x e2 e1)         -- beta reduction
  App e1 e2 -> case step e1 of
    Just e1' -> Just (App e1' e2)
    Nothing  -> App e1 <$> step e2
  Lam x e -> Lam x <$> step e
  _ -> Nothing

-- Full evaluation (normal order)
eval :: Expr -> Expr
eval e = maybe e eval (step e)

-- Pretty printer
pretty :: Expr -> String
pretty = go False
  where
    go _ (Var x) = x
    go _ (Lam x e) = "λ" ++ x ++ ". " ++ go False e
    go p (App e1 e2) =
      let s1 = go True e1
          s2 = go True e2
      in if p then "(" ++ s1 ++ " " ++ s2 ++ ")" else s1 ++ " " ++ s2

-- Examples
idExpr :: Expr
idExpr = Lam "x" (Var "x")

constExpr :: Expr
constExpr = Lam "x" (Lam "y" (Var "x"))

example :: Expr
example = App idExpr (Lam "y" (Var "y"))  -- (λx. x) (λy. y)

main :: IO ()
main = do
  putStrLn "Evaluating (λx. x) (λy. y):"
  print $ pretty $ eval example



