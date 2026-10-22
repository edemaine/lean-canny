/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AsymmetricProjection
public import LeanCanny.Algebra.CoordinateRecoveryBounds

/-! # Rational coordinates from asymmetric finite-set projections

The bounded directions in `AsymmetricProjection` satisfy the hypotheses of the
existing univariate subresultant recovery theorem. For a point x, the parameter
is (k+1)*L(x), and recovery gives x_j = L(x) + N/D with D nonzero.
The polynomials here are nodal products over a supplied finite point set;
constructing them from an encoded multivariate system remains separate work.
-/

@[expose] public section

namespace LeanCanny.Algebra.AsymmetricProjection
open Polynomial

variable {ι K : Type*} [Fintype ι] [Field K]

theorem plus_injective (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι)
    (hinj : Set.InjOn (pairValue (K := K) c k j)
      ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K)))) :
    Set.InjOn (plus c k j) (s : Set (ι → K)) := by
  intro a ha b hb he
  have hp : (a, a) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, ha⟩
  have hq : (b, a) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨hb, ha⟩
  exact congrArg Prod.fst (hinj hp hq (by simp only [pairValue, LeanCanny.Algebra.shear, he]))

theorem minus_injective (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι)
    (hinj : Set.InjOn (pairValue (K := K) c k j)
      ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K)))) :
    Set.InjOn (minus c j) (s : Set (ι → K)) := by
  intro a ha b hb he
  have hp : (a, a) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, ha⟩
  have hq : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
  exact congrArg Prod.snd (hinj hp hq (by simp only [pairValue, LeanCanny.Algebra.shear, he]))

omit [Fintype ι] in
theorem nodal_zero_iff (s : Finset (ι → K)) (f : (ι → K) → K) (t : K) :
    (Lagrange.nodal s f).eval t = 0 ↔ ∃ x ∈ s, f x = t := by
  classical
  rw [Lagrange.eval_nodal, Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero, eq_comm]

omit [Fintype ι] in
theorem nodal_splits (s : Finset (ι → K)) (f : (ι → K) → K) :
    (Lagrange.nodal s f).Splits :=
  Polynomial.Splits.prod (fun _ _ => Polynomial.Splits.X_sub_C _)

omit [Fintype ι] in
theorem nodal_rootPairs_injective (s : Finset (ι → K)) (f g : (ι → K) → K) (k : ℕ)
    (hinj : Set.InjOn (fun p => LeanCanny.Algebra.shear k (f p.1, g p.2))
      ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K)))) :
    Set.InjOn (LeanCanny.Algebra.shear k)
      (rootPairs (L := K) (Lagrange.nodal s f) (Lagrange.nodal s g) : Set (K × K)) := by
  intro p hp q hq he
  obtain ⟨hpa, hpb⟩ := (mem_rootPairs _ _ Lagrange.nodal_ne_zero Lagrange.nodal_ne_zero p).mp hp
  obtain ⟨hqa, hqb⟩ := (mem_rootPairs _ _ Lagrange.nodal_ne_zero Lagrange.nodal_ne_zero q).mp hq
  obtain ⟨a, ha, hea⟩ := (nodal_zero_iff s f p.1).mp (by simpa using hpa)
  obtain ⟨b, hb, heb⟩ := (nodal_zero_iff s g p.2).mp (by simpa using hpb)
  obtain ⟨d, hd, hed⟩ := (nodal_zero_iff s f q.1).mp (by simpa using hqa)
  obtain ⟨e, he', hee⟩ := (nodal_zero_iff s g q.2).mp (by simpa using hqb)
  have hvec : (a, b) = (d, e) := hinj (Finset.mem_product.mpr ⟨ha, hb⟩)
    (Finset.mem_product.mpr ⟨hd, he'⟩) (by simpa only [hea, heb, hed, hee] using he)
  exact Prod.ext (by simpa only [hea, hed] using congrArg (fun r => f r.1) hvec)
    (by simpa only [heb, hee] using congrArg (fun r => g r.2) hvec)

theorem recover_coordinate (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι)
    (hinj : Set.InjOn (pairValue (K := K) c k j)
      ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K))))
    (x : ι → K) (hx : x ∈ s) :
    let pPlus := Lagrange.nodal s (plus c k j)
    let pMinus := Lagrange.nodal s (minus c j)
    let θ := ((k : K) + 1) * projection c x
    let N := (coordinateNumerator pPlus pMinus k).eval θ
    let D := (coordinateDenominator pPlus pMinus k).eval θ
    D ≠ 0 ∧ x j = projection c x + N / D := by
  have hsep : (Lagrange.nodal s (minus c j)).Separable :=
    separable_prod_X_sub_C_iff'.mpr (minus_injective s c k j hinj)
  have hs : ((Lagrange.nodal s (minus c j)).map (algebraMap K K)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using nodal_splits s (minus c j)
  have hroot := coordinate_recovery_spec (Lagrange.nodal s (plus c k j))
    (Lagrange.nodal s (minus c j)) k (plus c k j x) (minus c j x)
    Lagrange.nodal_ne_zero hsep hs (nodal_rootPairs_injective s _ _ k hinj)
    (by simpa using Lagrange.eval_nodal_at_node (v := plus c k j) hx)
    (by simpa using Lagrange.eval_nodal_at_node (v := minus c j) hx)
  dsimp only at hroot ⊢
  have hθ : LeanCanny.Algebra.shear k (plus c k j x, minus c j x) =
      ((k : K) + 1) * projection c x := diagonal_pairValue c k j x
  simp only [hθ, Polynomial.coe_aeval_eq_eval] at hroot
  refine ⟨hroot.1, ?_⟩
  have he := hroot.2.1
  change projection c x - x j = _ at he
  rw [neg_div] at he
  linear_combination -he

/-- Denominator expressed in the original projection parameter L(x). -/
noncomputable def rationalDenominator (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) : K[X] :=
  (coordinateDenominator (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k).comp
    (C ((k : K) + 1) * X)

/-- Numerator expressed in the original projection parameter L(x). -/
noncomputable def rationalNumerator (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) : K[X] :=
  X * rationalDenominator s c k j +
    (coordinateNumerator (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k).comp
      (C ((k : K) + 1) * X)

theorem eval_rationalDenominator (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) (t : K) :
    (rationalDenominator s c k j).eval t =
      (coordinateDenominator (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k).eval
        (((k : K) + 1) * t) := by
  simp [rationalDenominator]

theorem eval_rationalNumerator (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) (t : K) :
    (rationalNumerator s c k j).eval t = t * (rationalDenominator s c k j).eval t +
      (coordinateNumerator (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k).eval
        (((k : K) + 1) * t) := by
  simp [rationalNumerator]

theorem recover_rational_coordinate (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι)
    (hinj : Set.InjOn (pairValue (K := K) c k j)
      ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K))))
    (x : ι → K) (hx : x ∈ s) :
    (rationalDenominator s c k j).eval (projection c x) ≠ 0 ∧
      (rationalNumerator s c k j).eval (projection c x) /
        (rationalDenominator s c k j).eval (projection c x) = x j := by
  have hr := recover_coordinate s c k j hinj x hx
  have hd : (rationalDenominator s c k j).eval (projection c x) ≠ 0 := by
    rw [eval_rationalDenominator]
    exact hr.1
  refine ⟨hd, ?_⟩
  rw [eval_rationalNumerator, add_div, mul_div_cancel_right₀ _ hd, eval_rationalDenominator]
  exact hr.2.symm

omit [Fintype ι] in
private theorem scaled_comp_natDegree_le (p : K[X]) (k : ℕ) :
    (p.comp (C ((k : K) + 1) * X)).natDegree ≤ p.natDegree := by
  have hlinear : (C ((k : K) + 1) * X).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simp)
  exact natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left p.natDegree hlinear)

theorem rationalDenominator_natDegree_le (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) :
    (rationalDenominator s c k j).natDegree ≤ max 1 ((s.card - 1) * s.card) := by
  apply (scaled_comp_natDegree_le _ k).trans
  simpa only [Lagrange.natDegree_nodal] using coordinateDenominator_natDegree_le
    (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k

theorem rationalNumerator_natDegree_le (s : Finset (ι → K)) (c : ι → ℕ) (k : ℕ) (j : ι) :
    (rationalNumerator s c k j).natDegree ≤ 1 + max 1 ((s.card - 1) * s.card) := by
  have hn : ((coordinateNumerator (Lagrange.nodal s (plus c k j))
      (Lagrange.nodal s (minus c j)) k).comp (C ((k : K) + 1) * X)).natDegree ≤
      max 1 ((s.card - 1) * s.card) := by
    apply (scaled_comp_natDegree_le _ k).trans
    simpa only [Lagrange.natDegree_nodal] using coordinateNumerator_natDegree_le
      (Lagrange.nodal s (plus c k j)) (Lagrange.nodal s (minus c j)) k
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by
      simpa only [natDegree_X] using Nat.add_le_add_left (rationalDenominator_natDegree_le s c k j) 1)
  · omega

theorem exists_bounded_rational_coordinates [CharZero K] (s : Finset (ι → K)) :
    ∃ k : ℕ, ∃ c : ι → ℕ, 0 < k ∧ k ≤ s.card ^ 4 + 1 ∧
      (∀ i, c i ≤ (Fintype.card ι + 1) * s.card ^ 4) ∧
      Set.InjOn (projection (K := K) c) (s : Set (ι → K)) ∧
      (Lagrange.nodal s (projection c)).Separable ∧
      ∀ j, ∀ x ∈ s, (rationalDenominator s c k j).eval (projection c x) ≠ 0 ∧
        (rationalNumerator s c k j).eval (projection c x) /
          (rationalDenominator s c k j).eval (projection c x) = x j := by
  obtain ⟨k, c, hk, hkb, hc, hp, hpair⟩ := exists_bounded_direction s
  exact ⟨k, c, hk, hkb, hc, hp, separable_prod_X_sub_C_iff'.mpr hp,
    fun j x hx => recover_rational_coordinate s c k j (hpair j) x hx⟩

end LeanCanny.Algebra.AsymmetricProjection
