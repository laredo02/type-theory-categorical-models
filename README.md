

# Part 1: Lambda Calculus & Type Systems

## 1. Untyped Lambda Calculus
- Syntax: \lambda, application, variables
- Reduction: \alpha, \beta, \eta
- Church encodings (Booleans, Naturals)
- Fixed-point combinators (Y) and recursion
- Limitations: Non-termination, lack of safety

## 2. Simply Typed Lambda Calculus (STLC)
- Types: base, functions (→), products/sums (×, +)
- Typing judgments (Γ ⊢ M : τ)
- Normalization (strong vs. weak)
- Curry-Howard preview: STLC ≃ Propositional Logic

## 3. Parametric Polymorphism (System F)
- Type abstraction/application (Λα. M, M [τ])
- Theorems for Free (parametricity)
- Limitations: No value-dependence

## 4. Dependent Types (λΠ, Martin-Löf)
- Π-types (∀), Σ-types (∃), equality types (Id)
- Inductive types (Nats, Lists)
- Example: Vectors (Vec A n), certified sorting

# Part 2: Logic & the Curry-Howard Isomorphism

## 1. Propositional Logic
- Natural deduction: →, ∧, ∨, ⊥ rules
- Intuitionistic vs. classical (excluded middle)
- BHK interpretation (proofs as programs)

## 2. Curry-Howard for STLC
- Propositions-as-Types (A → B ≈ function type)
- Proofs-as-Terms (Modus Ponens ≈ application)
- Examples:
  - A → (B → A) ≈ λa. λb. a (K combinator)
  - ¬A ≈ A → ⊥

## 3. Predicate Logic & Dependent Types
- Universal quantifier (∀ ≈ Π-type)
- Existential quantifier (∃ ≈ Σ-type)
- Example: ∀n ∈ ℕ. ∃m ∈ ℕ. m > n ≈ dependent function + pair

## 4. Proof Theory & Computation
- Cut elimination ≈ β-reduction
- Normalization ≈ program termination

# Part 3: Categorical Semantics (Types as Objects, Programs as Morphisms)

## 1. Categories of Types
- Cartesian Closed Categories (CCC) for STLC:
  - Products (A × B) ≈ conjunction (A ∧ B)
  - Exponentials (B^A) ≈ implication (A → B)
- Functorial semantics of System F

## 2. Dependent Types & LCCCs
- Locally Cartesian Closed Categories (LCCC):
  - Π-types ≈ right adjoints to substitution
  - Σ-types ≈ left adjoints
- Fibrations for predicate logic

## 3. Parametricity as Naturality [Maybe]
- Reynolds' abstraction theorem ≈ dinaturality
- Polymorphic functions as natural transformations

## 4. Advanced Topics [Maybe]
- Monads/comonads for effects
- Homotopy Type Theory (univalence)

# Appendices

## C. Papers: Church, Reynolds, Martin-Löf, Hindley-Milner
