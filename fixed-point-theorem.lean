inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term
  deriving Repr, BEq

open Term

/-- Substitute variable `x` with term `s` in term `t` -/
def subst (t : Term) (x : String) (s : Term) : Term :=
  match t with
  | var y        => if y = x then s else var y
  | app t1 t2    => app (subst t1 x s) (subst t2 x s)
  | lam y body   => 
    if y = x then lam y body
    else lam y (subst body x s)

/-- One-step beta reduction -/
inductive beta : Term → Term → Prop where
  | beta_step (x : String) (t s : Term) : 
    beta (app (lam x t) s) (subst t x s)
  | app_l (t1 t1' t2 : Term) (h : beta t1 t1') :
    beta (app t1 t2) (app t1' t2)
  | app_r (t1 t2 t2' : Term) (h : beta t2 t2') :
    beta (app t1 t2) (app t1 t2')
  | lam_b (x : String) (t t' : Term) (h : beta t t') :
    beta (lam x t) (lam x t')

/-- Multi-step beta reduction (reflexive transitive closure) -/
inductive beta_star : Term → Term → Prop where
  | refl (t : Term) : beta_star t t
  | trans (t u v : Term) (h1 : beta t u) (h2 : beta_star u v) : beta_star t v

/-- The Y combinator term: Y = λf.(λx.f (x x)) (λx.f (x x)) -/
def Y : Term :=
  lam "f" (app 
    (lam "x" (app (var "f") (app (var "x") (var "x"))))
    (lam "x" (app (var "f") (app (var "x") (var "x")))))

/-- Define fixed point property: x is a fixed point of f if f x reduces to x -/
def fixed_point (f x : Term) : Prop := beta_star (app f x) x

/-- Theorem: For any term f, Y f is a fixed point of f -/
theorem fixed_point_theorem (f : Term) : fixed_point f (app Y f) := by
  -- We want to prove beta_star (app f (app Y f)) (app Y f)
  -- The reduction proceeds:
  -- app (Y f) reduces by beta to (app f (app Y f))
  -- So they are related by beta reduction steps.

  -- First, recall:
  -- Y f = (λf.(λx.f (x x)) (λx.f (x x))) f
  -- reduces to (λx.f (x x)) (λx.f (x x))
  -- which beta reduces to f ((λx.f (x x)) (λx.f (x x))) = f (Y f)

  -- So (Y f) beta reduces to (f (Y f))

  -- Since beta_star is transitive and reflexive, we can chain these steps.

  -- Step 1: (Y f) →β (app (lam "x" (app f (app (var "x") (var "x")))) (lam "x" (app f (app (var "x") (var "x")))))
  have step1 : beta (app Y f) (app (lam "x" (app f (app (var "x") (var "x")))) (lam "x" (app f (app (var "x") (var "x"))))) := 
    beta.beta_step "f" (app (lam "x" (app f (app (var "x") (var "x")))) (lam "x" (app f (app (var "x") (var "x"))))) f

  -- Step 2: Apply beta to get f (Y f)
  have step2 : beta (app (lam "x" (app f (app (var "x") (var "x")))) (lam "x" (app f (app (var "x") (var "x"))))) (app f (app (lam "x" (app f (app (var "x") (var "x")))) (lam "x" (app f (app (var "x") (var "x")))))) :=
    beta.beta_step "x" (app f (app (var "x") (var "x"))) (lam "x" (app f (app (var "x") (var "x"))))

  -- Compose these two beta steps into beta_star steps
  apply beta_star.trans (app Y f) _ _ step1 (beta_star.trans _ _ _ step2 (beta_star.refl _))

