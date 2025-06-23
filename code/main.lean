import Mathlib.Data.Set.Basic

inductive Term : Type
  | var : String → Term
  | abs : String → Term → Term
  | app : Term → Term → Term

def Term.toString : Term → String
  | var x    => x
  | abs x M  => "(λ" ++ x ++ "." ++ toString M ++ ")"
  | app M N  => "(" ++ toString M ++ toString N ++ ")"

open Std

def subterm : Term → 

def term := (Term.abs "x" (Term.app (Term.var "x") (Term.var "y")))
#eval Term.toString term

  
