/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ParameterizedGridQueryUniformBounds

/-! # Actual Cartesian root branches preserving all bounded query signs

The finite labels are products of the actual head-root labels at one anchor.
Continuous paths and all query-sign transports are constructed internally.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedCartesianBranches
open LeanCanny.Algebra Polynomial Set ParameterizedGridQuerySign
open scoped Classical

noncomputable abbrev Index {n : ℕ} (p : Fin n → (ℤ[X])[X])
    (a b : ℝ) (s : Ioo a b) := ∀ i, ParameterizedOrderedRootBranches.Index (p i) a b s

def cutoff (n D E H : ℕ) := ParameterizedRootQuerySign.cutMassBound (D + 1) H + 1 +
  cutoffBudget n (commonWidth n D E) H

theorem cutoff_binary {n D E H : List Bool → ℕ}
    (hn : UnaryFn n) (hd : BinaryFn D) (he : BinaryFn E) (hh : BinaryFn H) :
    BinaryFn (fun c => cutoff (n c) (D c) (E c) (H c)) :=
  ((ParameterizedRootQuerySign.cutMassBound_binary (hd.add (BinaryFn.const 1)) hh).add
    (BinaryFn.const 1)).add (commonCutoff_binary hn hd he hh)

private theorem head_avoids {n : ℕ} (p : Fin n → (ℤ[X])[X]) (D E H : ℕ)
    (hpos : ∀ i, 0 < (p i).natDegree) (hd : ∀ i, (p i).natDegree ≤ D)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    {a b : ℝ} (ha : (2 : ℝ) ^ cutoff n D E H ≤ a) (i : Fin n) :
    ParameterizedRootQuerySign.Avoids (p i) (fun _ : Unit => X) a b := by
  have hn : p i ≠ 0 := by
    intro hz
    have hh := hpos i
    rw [hz, natDegree_zero] at hh
    omega
  apply ParameterizedRootQuerySign.avoids_after_input_bounds (p i) hn
    (fun _ : Unit => X) (D + 1) H ((hd i).trans (Nat.le_succ D))
  · intro j
    rw [natDegree_X]
    omega
  · exact hp i
  · intro j k
    simp only [coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ _
      rw [coefficientMass_C, Int.natAbs_one]
      exact Nat.one_le_two_pow
    · simp
  · apply le_trans _ ha
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Nat.le_add_right _ _

theorem finite_index {n : ℕ} (p : Fin n → (ℤ[X])[X]) (D E H : ℕ)
    (hpos : ∀ i, 0 < (p i).natDegree) (hd : ∀ i, (p i).natDegree ≤ D)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    {a b : ℝ} (ha : (2 : ℝ) ^ cutoff n D E H ≤ a) (s : Ioo a b) :
    Finite (Index p a b s) := by
  let (i : Fin n) : Finite (ParameterizedOrderedRootBranches.Index (p i) a b s) :=
    ParameterizedOrderedRootBranches.finite_index (p i) (fun _ : Unit => X)
      (head_avoids p D E H hpos hd hp ha i) s
  infer_instance

theorem exists_branches {n : ℕ} {J : Type*} (p : Fin n → (ℤ[X])[X])
    (Q : J → MvPolynomial (Fin n) ℤ[X]) (D E H : ℕ)
    (hpos : ∀ i, 0 < (p i).natDegree) (hd : ∀ i, (p i).natDegree ≤ D)
    (he : ∀ j, (Q j).totalDegree ≤ E)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    (hq : ∀ j v, coefficientMass ((Q j).coeff v) ≤ 2 ^ H)
    {a b : ℝ} (ha : (2 : ℝ) ^ cutoff n D E H ≤ a) (s : Ioo a b) :
    ∃ curve : Index p a b s → C(Ioo a b, Fin n → ℝ),
      (∀ l i, curve l s i = (l i).val.val.val.2 0) ∧
      (∀ l t i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (curve l t i) = 0) ∧
      (∀ t : Ioo a b, ∀ x : Fin n → ℝ,
        (∀ i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (x i) = 0) ↔
          ∃! l, curve l t = x) ∧
      (∀ l k i u v, curve l u i < curve k u i ↔ curve l v i < curve k v i) ∧
      (∀ l j u v,
        SignType.sign ((Q j).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u.val) (curve l u)) =
          SignType.sign ((Q j).eval₂ (SymbolicScaledSquarefree.scalarEvaluation v.val) (curve l v))) := by
  have hh (i : Fin n) := ParameterizedOrderedRootBranches.exists_ordered_branches (p i)
    (fun _ : Unit => X) (head_avoids p D E H hpos hd hp ha i) s
  choose branch hanchor hroot hcover horder hsign using hh
  let curve (l : Index p a b s) : C(Ioo a b, Fin n → ℝ) :=
    ⟨fun t i => branch i (l i) t 0, continuous_pi (fun i =>
      (continuous_apply 0).comp (branch i (l i)).continuous)⟩
  have roots (l : Index p a b s) (t : Ioo a b) (i : Fin n) :
      (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (curve l t i) = 0 :=
    hroot i (l i) t
  refine ⟨curve, ?_, roots, ?_, ?_, ?_⟩
  · intro l i
    exact congrArg (fun x => x 0) (hanchor i (l i))
  · intro t x
    constructor
    · intro hx
      have hc (i : Fin n) := (hcover i t (fun _ => x i)).mp (hx i)
      choose l hl hu using hc
      refine ⟨l, funext (fun i => congrArg (fun z => z 0) (hl i)), ?_⟩
      intro k hk
      funext i
      apply hu i (k i)
      funext z
      have hz : z = 0 := Subsingleton.elim _ _
      simpa only [hz, curve, ContinuousMap.coe_mk] using congrArg (fun z => z i) hk
    · rintro ⟨l, hl, _⟩ i
      rw [← hl]
      exact roots l t i
  · intro l k i u v
    exact horder i (l i) (k i) u v
  · intro l j u v
    apply sign_after_common_input_bounds p (Q j) hpos D E H hd (he j) hp (hq j) _ (curve l) (roots l) u v
    apply le_trans _ ha
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Nat.le_add_left _ _

end LeanCanny.Geometry.ParameterizedCartesianBranches
