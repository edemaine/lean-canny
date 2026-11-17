/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFeatureSeparator
public import LeanCanny.CountingHierarchy.SparseRootSelection

/-! # Short fingerprints selecting a prescribed real root

Powers of one finite-field element compress an entire Thom signature to a
weighted integer sum. The two parameters have polynomial binary length in the
degree bound. Unlike selection by a sparse sublist, this selects every
prescribed root, as required by coordinate sampling in the two-block argument.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical BigOperators

def fingerprintWeight (p gamma j : ℕ) : ℕ := gamma ^ j % p

noncomputable def derivativeFingerprint (q : ℝ[X]) (D p gamma : ℕ) (x : ℝ) : ℤ :=
  ∑ i : Fin D, (fingerprintWeight p gamma i.val : ℤ) *
    (ThomEncoding.sign q x (i.val + 1) : ℤ)

private theorem sign_int_injective : Function.Injective (fun s : SignType => (s : ℤ)) := by
  intro a b h
  cases a <;> cases b <;> norm_num at *

private theorem sign_int_bounds (s : SignType) : -1 ≤ (s : ℤ) ∧ (s : ℤ) ≤ 1 := by
  cases s <;> norm_num

theorem derivativeFingerprint_natAbs_le (q : ℝ[X]) (D p gamma : ℕ) (x : ℝ) (hp : 0 < p) :
    (derivativeFingerprint q D p gamma x).natAbs ≤ D * p := by
  rw [derivativeFingerprint]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin D, p := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hs : (ThomEncoding.sign q x (i.val + 1) : ℤ).natAbs ≤ 1 := by
        generalize ThomEncoding.sign q x (i.val + 1) = c
        cases c <;> decide
      have hw : fingerprintWeight p gamma i.val ≤ p := (Nat.mod_lt _ hp).le
      exact (Nat.mul_le_mul hw hs).trans_eq (Nat.mul_one _)
    _ = D * p := by simp

/-- A single pair of short parameters separates all roots in the supplied
finite root set. Every resulting integer fingerprint selects its root uniquely. -/
theorem exists_derivative_fingerprint (q : ℝ[X]) (hq : q ≠ 0) (D : ℕ)
    (hD : q.natDegree ≤ D) (S : Finset ℝ) (hroot : ∀ x ∈ S, q.eval x = 0) :
    ∃ p gamma : ℕ, p.Prime ∧ 2 < p ∧ p ≤ 2 * (D ^ 3 + 2) ∧ gamma < p ∧
      Function.Injective (fun x : S => derivativeFingerprint q D p gamma x.val) := by
  let a : S → Fin D → ℤ := fun x i => (ThomEncoding.sign q x.val (i.val + 1) : ℤ)
  have ha : Function.Injective a := by
    intro x y he
    apply Subtype.ext
    apply ThomEncoding.root_eq q hq D hD x.val y.val (hroot _ x.property) (hroot _ y.property)
    intro k hk
    cases k with
    | zero => simp only [ThomEncoding.sign, Function.iterate_zero_apply, hroot _ x.property,
        hroot _ y.property]
    | succ k => exact sign_int_injective (congrFun he ⟨k, by omega⟩)
  obtain ⟨p, hp, hl, hu, t, ht⟩ := FiniteFeatureSeparator.exists_prime_parameter a ha
    (fun x i => sign_int_bounds _)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hc : Fintype.card S ≤ D := by
    rw [Fintype.card_coe]
    have hs : S.val ⊆ q.roots := fun x hx => (Polynomial.mem_roots hq).mpr (hroot x hx)
    exact (Polynomial.card_le_degree_of_subset_roots hs).trans hD
  refine ⟨p, t.val, hp, by omega, hu.trans ?_, ZMod.val_lt t, ?_⟩
  · have hm : D * Fintype.card S ^ 2 ≤ D * D ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)
    nlinarith
  · have hcast (x : S) : (derivativeFingerprint q D p t.val x.val : ZMod p) =
        ∑ i : Fin D, (a x i : ZMod p) * t ^ i.val := by
      simp only [derivativeFingerprint, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
        fingerprintWeight, ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val, a]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    intro x y he
    apply ht
    exact (hcast x).symm.trans ((congrArg (Int.castRingHom (ZMod p)) he).trans (hcast y))

end LeanCanny.CountingHierarchy
