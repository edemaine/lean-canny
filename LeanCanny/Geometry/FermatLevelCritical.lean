/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelLift
public import Mathlib.Topology.Order.IntermediateValue

/-! # Bounded level lifts of unconstrained critical points

A large fixed integer coefficient supplies a free objective in [-1,1]. This
proves the hypersurface equation rather than assuming the critical value is
zero. The bound on the original value remains explicit.
-/
@[expose] public section
namespace LeanCanny.Geometry.FermatLevelCritical
open LeanCanny.Algebra MvPolynomial Set

 theorem exists_level (w : ℝ) (A : ℤ) (d : ℕ) (hd : Even d) (hw : |w| ≤ (A:ℝ)-1) :
    ∃ v ∈ Icc (-1:ℝ) 1, w+v^d-(A:ℝ)*v=0 := by
  let f : ℝ → ℝ := fun v => w+v^d-(A:ℝ)*v
  have HF : Continuous f := (continuous_const.add (continuous_id.pow d)).sub (continuous_const.mul continuous_id)
  have HL := abs_le.mp hw
  have HM : (0:ℝ) ∈ Icc (f 1) (f (-1)) := by
    constructor
    · dsimp [f]
      norm_num
      linarith [HL.2]
    · dsimp [f]
      rw [hd.neg_one_pow]
      nlinarith [HL.1]
  obtain ⟨v,hv,hfv⟩ := intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 1) HF.continuousOn HM
  exact ⟨v,hv,hfv⟩

variable {n : ℕ}

theorem lift_critical (P : IntegralMixedHistory.SpatialSource n) (A : ℤ)
    (hP : P.leading=1) (hd : Even P.degree) (x : Fin (n+1) → ℝ)
    (hw : |(FermatLevelLift.polynomial P).eval₂ (Int.castRingHom ℝ) x| ≤ (A:ℝ)-1)
    (offset : ℕ) (hg : ∀ i : Fin (n+1), offset ≤ i.val →
      (pderiv i (FermatLevelLift.polynomial P)).eval₂ (Int.castRingHom ℝ) x=0) :
    ∃ v ∈ Icc (-1:ℝ) 1,
      (FermatLevelLift.polynomial (FermatLevelLift.source P A)).eval₂ (Int.castRingHom ℝ) (Fin.snoc x v)=0 ∧
      ∀ i : Fin (n+1), offset ≤ i.val →
        (pderiv i.castSucc (FermatLevelLift.polynomial (FermatLevelLift.source P A))).eval₂
          (Int.castRingHom ℝ) (Fin.snoc x v)=0 := by
  obtain ⟨v,hv,HE⟩ := exists_level _ A P.degree hd hw
  refine ⟨v,hv,?_,?_⟩
  · rw [FermatLevelLift.eval_source,hP]
    simpa only [Int.cast_one,one_mul] using HE
  · intro i hi
    rw [FermatLevelLift.derivative,eval₂_rename]
    have HC : (Fin.snoc x v) ∘ Fin.castSucc=x := by funext j; simp
    rw [HC]
    exact hg i hi

end LeanCanny.Geometry.FermatLevelCritical
