/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveNativeAnnihilators
public import LeanCanny.Algebra.CoerciveQuerySystem

/-! # Exact all-coordinate root-product filtering for coercive samples -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveNativeSampling
open LeanCanny.Algebra CoerciveSourceSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def Satisfies (bits : List Bool) (y : Fin (dimension bits + 1) → ℝ) : Prop :=
  (∀ i, (CoerciveQuerySystem.gradient (polynomial bits) (degreeAllowance bits) i).eval₂
    (Int.castRingHom ℝ) y = 0) ∧
  (CoerciveQuerySystem.bound (n := dimension bits) (degreeAllowance bits) (penaltyExponent bits)).eval₂
    (Int.castRingHom ℝ) y ≤ 0 ∧
  (CoerciveQuerySystem.residual (polynomial bits) (penaltyExponent bits)).eval₂ (Int.castRingHom ℝ) y ≤ 0

theorem sample_iff (bits : List Bool) (s : ℝ) (x : Fin (dimension bits) → ℝ) :
    Sample bits s x ↔ Satisfies bits (Fin.cons s x) :=
  CoerciveQuerySystem.sample_iff _ _ _ _ _

theorem exists_sample_iff_root_product (bits : List Bool) (s : ℝ) :
    (∃ x, Sample bits s x) ↔
      ∃ y : Fin (dimension bits + 1) → ℝ,
        (∀ i, (CoerciveNativeAnnihilators.original bits i.val).eval₂
          (SymbolicScaledSquarefree.scalarEvaluation s) (y i) = 0) ∧ Satisfies bits y := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Fin.cons s x, ?_, (sample_iff bits s x).mp hx⟩
    exact CoerciveNativeAnnihilators.critical_roots bits s x
      ((CoerciveSourceSampling.sample_iff bits s x).mp hx).1
  · rintro ⟨y, hy, hq⟩
    have hp : y 0 = s := (CoerciveNativeAnnihilators.pin_root_iff s (y 0)).mp (hy 0)
    have he : Fin.cons s (Fin.tail y) = y := by
      rw [← hp]
      exact Fin.cons_self_tail y
    refine ⟨Fin.tail y, (sample_iff bits s (Fin.tail y)).mpr ?_⟩
    rwa [he]

end LeanCanny.ETR.CoerciveNativeSampling
