/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ParameterSourceBudget
public import LeanCanny.Algebra.DyadicSignPatternSpace

/-! # Polynomial-space root-sign counts for a sufficiently small parameter

The dyadic exponent is computed from the original degree and coefficient-mass
bounds. Symbolic principal-test bounds prove that this choice has the eventual
root-sign count; no test-polynomial evaluator or infinitesimal sign oracle is
supplied to the algorithm. The query-family size remains polynomially bounded.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalRootBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open DyadicSignPatternBits

def parameterCode (F : Family) (c : List Bool) : List Bool := BinaryNat.succ
  (ParameterBudget.patternCode (F.root.degree c) (F.degree c) (F.count c) (F.root.mass c) (F.mass c))

theorem parameterCode_FP (F : Family) (hF : ControlsPolyTime F) : parameterCode F ∈ FP := by
  have h := mem_FP_comp (ParameterBudget.patternCode_FP hF.root.degree hF.degree hF.count hF.root.mass hF.mass)
    BinaryNat.succ_mem_FP
  refine mem_FP_of_eq h ?_
  intro c
  simp only [parameterCode, Function.comp_apply]

theorem parameterCode_value (F : Family) (c : List Bool) : Nat.fromBitsLE (parameterCode F c) =
    ParameterTarski.patternSourceBound (Nat.fromBitsLE (F.root.degree c)) (Nat.fromBitsLE (F.degree c))
      (Nat.fromBitsLE (F.count c)) (Nat.fromBitsLE (F.root.mass c)) (Nat.fromBitsLE (F.mass c)) + 1 := by
  simp only [parameterCode, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, ParameterBudget.patternCode_value]

def withExponent (F : Family) (s : List Bool → List Bool) : Family := { F with root := { F.root with exponent := s } }

theorem withExponent_controls (F : Family) (s : List Bool → List Bool) (hF : ControlsPolyTime F) (hs : s ∈ FP) :
    ControlsPolyTime (withExponent F s) :=
  ⟨⟨hF.root.degree, hF.root.parameterDegree, hs, hF.root.mass⟩,
    hF.count, hF.countUnary, hF.degree, hF.parameterDegree, hF.mass⟩

def effective (F : Family) : Family := withExponent F (parameterCode F)

theorem effective_controls (F : Family) (hF : ControlsPolyTime F) : ControlsPolyTime (effective F) :=
  withExponent_controls F (parameterCode F) hF (parameterCode_FP F hF)

def withExponentAccess {F : Family} (a : Access F) (s : List Bool → List Bool) : Access (withExponent F s) where
  root := ⟨a.root.coefficient, a.root.coefficient_eq⟩
  coefficient := a.coefficient
  pattern := a.pattern
  coefficient_eq := a.coefficient_eq
  pattern_eq := a.pattern_eq

def effectiveAccess {F : Family} (a : Access F) : Access (effective F) := withExponentAccess a (parameterCode F)

def queries (F : Family) (c : List Bool) (i : Fin (Nat.fromBitsLE (F.count c))) : (ℤ[X])[X] :=
  F.polynomial c i.val

def pattern (F : Family) (c : List Bool) (i : Fin (Nat.fromBitsLE (F.count c))) : SignType := F.pattern c i.val

theorem withExponent_rootCount (F : Family) (s : List Bool → List Bool) (c : List Bool) :
    DyadicSignPatternBits.rootCount (withExponent F s) c = RootSignQueries.signCount
      ((F.root.polynomial c).map (ParameterTarski.evalHom (InfinitesimalSign.dyadic (Nat.fromBitsLE (s c))))).roots.toFinset
      (fun i => (queries F c i).map (ParameterTarski.evalHom (InfinitesimalSign.dyadic (Nat.fromBitsLE (s c)))))
      (pattern F c) := by rfl

noncomputable def reference (F : Family) (c : List Bool) : ℝ :=
  InfinitesimalSign.dyadic (ParameterTarski.patternBudget (F.root.polynomial c) (queries F c) + 1)

noncomputable def eventualRootCount (F : Family) (c : List Bool) : ℕ := RootSignQueries.signCount
  ((F.root.polynomial c).map (ParameterTarski.evalHom (reference F c))).roots.toFinset
  (fun i => (queries F c i).map (ParameterTarski.evalHom (reference F c))) (pattern F c)

theorem effective_rootCount (F : Family) (c : List Bool) :
    DyadicSignPatternBits.rootCount (effective F) c = eventualRootCount F c := by
  have hb := ParameterTarski.pattern_bounded_of_coeff (F.root.polynomial c) (queries F c)
    (Nat.fromBitsLE (F.root.degree c)) (Nat.fromBitsLE (F.degree c))
    (Nat.fromBitsLE (F.root.mass c)) (Nat.fromBitsLE (F.mass c))
    (F.root.polynomial_degree c) (fun i => F.polynomial_degree c i.val)
    (F.root.coefficient_mass c) (fun i => F.coefficient_mass c i.val)
  simp only [Fintype.card_fin] at hb
  have he := ParameterTarski.rootCount_eq_reference (F.root.polynomial c) (queries F c) (pattern F c)
    _ (Nat.fromBitsLE (parameterCode F c)) hb (by rw [parameterCode_value]; omega)
    _ (InfinitesimalSign.dyadic_pos (Nat.fromBitsLE (parameterCode F c))) le_rfl
  rw [effective, withExponent_rootCount]
  exact he

theorem withExponentEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (s : List Bool → List Bool) (hs : s ∈ FP) (ht : a.pattern ∈ FP)
    (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (DyadicSignPatternBits.rootCount (withExponent F s) c)) :=
  DyadicSignPatternBits.rootCountEvaluator (withExponentAccess a s) (withExponent_controls F s hF hs) ht H P

/-- The original uniform bivariate coefficient routines are the only space-bounded
arithmetic sources. The exponent is derived internally from their FP bounds. -/
theorem rootCountEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (eventualRootCount F c)) := by
  let E := withExponentEvaluator a hF (parameterCode F) (parameterCode_FP F hF) hs H P
  exact E.congr (funext fun c => congrArg BinaryNatCode.encode (effective_rootCount F c))

def positiveLanguage (F : Family) : Language := {c | 0 < eventualRootCount F c}

theorem positiveDecider {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    SpaceDecider (positiveLanguage F) := by
  have hflag := (stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  apply (InfinitesimalRootBits.rootCountEvaluator a hF hs H P).decider (fun v => decide (v ≠ [])) hflag
  intro c
  change 0 < eventualRootCount F c ↔ decide (BinaryNatCode.encode (eventualRootCount F c) ≠ []) = true
  simp only [decide_eq_true_eq, BinaryNatCode.encode,
    ne_eq, BinaryNat.bits_eq_nil_iff]
  omega

theorem positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.root.coefficient) (P : SpaceFunction a.coefficient) :
    positiveLanguage F ∈ PSPACE := (positiveDecider a hF hs H P).mem_PSPACE

end LeanCanny.Algebra.InfinitesimalRootBits
