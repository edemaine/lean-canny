/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Int.Basic

/-! # Serialization for the formal abstract

Explicit expression trees use balanced brackets. Constructor tags, dimensions,
and variable indices are unary; signed integer magnitudes are binary. This
module implements that convention independently of the abstract's syntax.
The mathematical definitions and main results remain in `Abstract`.
-/

@[expose] public section
namespace LeanCanny.AbstractEncoding

def node (children : List (List Bool)) : List Bool := false :: (children.flatten ++ [true])
def unary (n : ℕ) : List Bool := node (List.replicate n (node []))
def bit (b : Bool) : List Bool := if b then node [node []] else node []

def integer : ℤ → List Bool
  | .ofNat n => node [unary 0, node (n.bits.map bit)]
  | .negSucc n => node [unary 1, node (n.bits.map bit)]

/-- Fold the four expression constructors into their literal binary codes. -/
def term {n : ℕ} {T : Type}
    {const : ℤ → T} {var : Fin n → T} {add mul : T → T → T}
    (rec : ∀ {P : T → Type}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) →
      (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t) : T → List Bool :=
  rec (P := fun _ => List Bool)
    (fun z => node [unary 0, integer z])
    (fun i => node [unary 1, unary i.val])
    (fun _ _ a b => node [unary 2, a, b])
    (fun _ _ a b => node [unary 3, a, b])

/-- Fold the term and Boolean constructors into their literal binary codes. -/
def formula {n : ℕ} {T F : Type}
    {const : ℤ → T} {var : Fin n → T} {add mul : T → T → T}
    {falsum : F} {eqZero ltZero : T → F} {neg : F → F} {conj disj : F → F → F}
    (termRec : ∀ {P : T → Type}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) →
      (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t)
    (rec : ∀ {P : F → Type}, P falsum → (∀ t, P (eqZero t)) →
      (∀ t, P (ltZero t)) → (∀ p, P p → P (neg p)) →
      (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p) : F → List Bool :=
  let termCode := term termRec
  rec (P := fun _ => List Bool)
    (node [unary 0])
    (fun t => node [unary 1, termCode t])
    (fun t => node [unary 2, termCode t])
    (fun _ p => node [unary 3, p])
    (fun _ _ p q => node [unary 4, p, q])
    (fun _ _ p q => node [unary 5, p, q])

def space {F : Type} (code : F → List Bool) (n : ℕ) (p : F) : List Bool :=
  node [unary 1, unary n, code p]

def point {F : Type} (code : F → List Bool) (n : ℕ) (p : F) (ab : F × F) : List Bool :=
  node [unary 0, unary n, code p, code ab.1, code ab.2]

end LeanCanny.AbstractEncoding
