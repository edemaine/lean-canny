/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Separation

/-! # Bounded asymmetric encodings of finite vector pairs

A positive integer weight separates a finite set of vector pairs by a+k*b.
For pairs drawn from N points, k <= N^4+1 suffices. Avoiding these vector
collisions removes identities that a later choice of projection direction
cannot fix in symmetric coordinate recovery.
-/

@[expose] public section

namespace LeanCanny.Algebra.VectorSeparation

variable {ι K : Type*} [Field K] [CharZero K]

def shear (k : ℕ) (p : (ι → K) × (ι → K)) : ι → K := fun i => p.1 i + (k : K) * p.2 i

omit [Field K] [CharZero K] in
private theorem exists_ne (a b : ι → K) (h : a ≠ b) : ∃ i, a i ≠ b i := by
  classical
  by_contra hn
  apply h
  funext i
  by_contra hi
  exact hn ⟨i, hi⟩

private noncomputable def witness (a b : ι → K) (h : a ≠ b) : ι := Classical.choose (exists_ne a b h)

omit [Field K] [CharZero K] in
private theorem witness_ne (a b : ι → K) (h : a ≠ b) : a (witness a b h) ≠ b (witness a b h) :=
  Classical.choose_spec (exists_ne a b h)

private noncomputable def badSlope (p q : (ι → K) × (ι → K)) : K := by
  classical
  exact if h : p.2 = q.2 then 0 else
    (p.1 (witness p.2 q.2 h) - q.1 (witness p.2 q.2 h)) /
      (q.2 (witness p.2 q.2 h) - p.2 (witness p.2 q.2 h))

theorem exists_positive_bounded_separating_shear (s : Finset ((ι → K) × (ι → K))) :
    ∃ k : ℕ, 0 < k ∧ k ≤ s.card ^ 2 + 1 ∧ Set.InjOn (shear (K := K) k) (s : Set ((ι → K) × (ι → K))) := by
  classical
  let slopes := (s ×ˢ s).image (fun pq => badSlope pq.1 pq.2)
  let bad := insert (0 : K) slopes
  obtain ⟨k, hk, hnot⟩ := exists_nat_le_card_notMem bad
  have hcard : bad.card ≤ s.card ^ 2 + 1 := by
    apply (Finset.card_insert_le _ _).trans
    apply Nat.add_le_add_right
    exact Finset.card_image_le.trans (by simp [Finset.card_product, pow_two])
  have hkpos : 0 < k := by
    by_contra hn
    have he : k = 0 := by omega
    apply hnot
    simp only [he, Nat.cast_zero, bad, Finset.mem_insert_self]
  refine ⟨k, hkpos, hk.trans hcard, ?_⟩
  intro p hp q hq heq
  by_cases hsecond : p.2 = q.2
  · apply Prod.ext _ hsecond
    funext i
    have h := congrFun heq i
    simpa only [shear, hsecond, add_left_inj] using h
  · exfalso
    apply hnot
    apply Finset.mem_insert_of_mem
    have hden : q.2 (witness p.2 q.2 hsecond) - p.2 (witness p.2 q.2 hsecond) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (witness_ne p.2 q.2 hsecond))
    have hslope : (k : K) = badSlope p q := by
      unfold badSlope
      rw [dite_eq_right hsecond]
      apply (eq_div_iff hden).mpr
      have h := congrFun heq (witness p.2 q.2 hsecond)
      unfold shear at h
      linear_combination -h
    rw [hslope]
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩

theorem exists_bounded_pair_encoding (s : Finset (ι → K)) :
    ∃ k : ℕ, 0 < k ∧ k ≤ s.card ^ 4 + 1 ∧
      Set.InjOn (shear (K := K) k) ((s ×ˢ s : Finset ((ι → K) × (ι → K))) : Set ((ι → K) × (ι → K))) := by
  obtain ⟨k, hk, hb, hinj⟩ := exists_positive_bounded_separating_shear (s ×ˢ s)
  refine ⟨k, hk, hb.trans_eq ?_, hinj⟩
  rw [Finset.card_product]
  ring

end LeanCanny.Algebra.VectorSeparation
