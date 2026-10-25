/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationListComplexity
public import Mathlib.Basic.Complex.Basic

/-! # Complex arithmetic networks as real polynomial equations

Each complex wire has two real coordinates. Every constant, addition,
multiplication, or zero constraint writes two real equations of bounded
arithmetic depth. Shared wires stay shared; no polynomial is expanded.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding
open scoped Classical

inductive Gate where
  | constant (out : ℕ) (value : ℤ)
  | add (out left right : ℕ)
  | mul (out left right : ℕ)
  | zero (wire : ℕ)
  deriving DecidableEq, Repr

def Gate.Holds (env : ℕ → ℂ) : Gate → Prop
  | .constant out z => env out = z
  | .add out left right => env out = env left + env right
  | .mul out left right => env out = env left * env right
  | .zero wire => env wire = 0

def realWire (i : ℕ) : Term := .var (2 * i)
def imagWire (i : ℕ) : Term := .var (2 * i + 1)
def difference (a b : Term) : Term := .add a (.mul (.const (-1)) b)

theorem eval_difference {R : Type*} [CommRing R] (env : ℕ → R) (a b : Term) :
    (difference a b).eval env = a.eval env - b.eval env := by simp [difference, Term.eval, sub_eq_add_neg]

def Gate.equations : Gate → List Term
  | .constant out z => [difference (realWire out) (.const z), imagWire out]
  | .add out left right =>
      [difference (realWire out) (.add (realWire left) (realWire right)),
        difference (imagWire out) (.add (imagWire left) (imagWire right))]
  | .mul out left right =>
      [difference (realWire out)
        (difference (.mul (realWire left) (realWire right)) (.mul (imagWire left) (imagWire right))),
        difference (imagWire out)
          (.add (.mul (realWire left) (imagWire right)) (.mul (imagWire left) (realWire right)))]
  | .zero wire => [realWire wire, imagWire wire]

def complexEnv (env : ℕ → ℝ) (i : ℕ) : ℂ := ⟨env (2 * i), env (2 * i + 1)⟩

theorem gate_equations_iff (g : Gate) (env : ℕ → ℝ) :
    (∀ t ∈ g.equations, t.eval env = 0) ↔ g.Holds (complexEnv env) := by
  cases g <;> simp [Gate.equations, Gate.Holds, eval_difference, realWire, imagWire,
    Term.eval, Complex.ext_iff, complexEnv, sub_eq_zero]

def realEnv (env : ℕ → ℂ) (i : ℕ) : ℝ :=
  if i % 2 = 0 then (env (i / 2)).re else (env (i / 2)).im

theorem realEnv_even (env : ℕ → ℂ) (i : ℕ) : realEnv env (2 * i) = (env i).re := by
  simp [realEnv, Nat.mul_comm]

theorem realEnv_odd (env : ℕ → ℂ) (i : ℕ) : realEnv env (2 * i + 1) = (env i).im := by
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp only [realEnv, hm, one_ne_zero, ite_false, hd]

theorem complexEnv_realEnv (env : ℕ → ℂ) : complexEnv (realEnv env) = env := by
  funext i
  apply Complex.ext
  · exact realEnv_even env i
  · exact realEnv_odd env i

def equations (gates : List Gate) : List Term := gates.flatMap Gate.equations

theorem equations_iff (gates : List Gate) (env : ℕ → ℝ) :
    (∀ t ∈ equations gates, t.eval env = 0) ↔ ∀ g ∈ gates, g.Holds (complexEnv env) := by
  constructor
  · intro h g hg
    apply (gate_equations_iff g env).mp
    intro t ht
    exact h t (List.mem_flatMap.mpr ⟨g, hg, ht⟩)
  · intro h t ht
    obtain ⟨g, hg, ht⟩ := List.mem_flatMap.mp ht
    exact (gate_equations_iff g env).mpr (h g hg) t ht

def Satisfiable (gates : List Gate) : Prop := ∃ env : ℕ → ℂ, ∀ g ∈ gates, g.Holds env

theorem satisfiable_iff_real (gates : List Gate) :
    Satisfiable gates ↔ ∃ env : ℕ → ℝ, ∀ t ∈ equations gates, t.eval env = 0 := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨realEnv env, (equations_iff gates _).mpr ?_⟩
    rwa [complexEnv_realEnv]
  · rintro ⟨env, h⟩
    exact ⟨complexEnv env, (equations_iff gates env).mp h⟩

def pairData (a b : Data) : Data := .l [a, b]

def Gate.toData : Gate → Data
  | .constant out z => pairData (Codec.unary 0) (pairData (Codec.unary out) (Term.const z).toData)
  | .add out left right => pairData (Codec.unary 1)
      (pairData (Codec.unary out) (pairData (Codec.unary left) (Codec.unary right)))
  | .mul out left right => pairData (Codec.unary 2)
      (pairData (Codec.unary out) (pairData (Codec.unary left) (Codec.unary right)))
  | .zero wire => pairData (Codec.unary 3) (Codec.unary wire)

def Gate.encode (g : Gate) : List Bool := g.toData.toBits
def forest (gates : List Gate) : List Bool := (gates.map Gate.encode).flatten
def encode (gates : List Gate) : List Bool := (Data.l (gates.map Gate.toData)).toBits

theorem forest_cons (g : Gate) (gates : List Gate) : forest (g :: gates) = g.encode ++ forest gates := rfl

theorem encode_eq_wrap (gates : List Gate) : encode gates = Brackets.wrap (forest gates) := by
  unfold encode forest
  rw [Data.toBits_l, List.map_map]
  rfl

theorem forest_length_ge (gates : List Gate) : gates.length ≤ (forest gates).length := by
  induction gates with
  | nil => simp [forest]
  | cons g gates ih =>
    have hp : 0 < g.encode.length := by simp [Gate.encode]
    simp only [forest_cons, List.length_append, List.length_cons]
    omega

end LeanCanny.ETR.ComplexCircuit
