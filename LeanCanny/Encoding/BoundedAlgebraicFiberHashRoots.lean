/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberPencilCuts

/-! # Exact integer roots of the selected hash polynomial

The real roots of the native integer determinant are exactly the selected
integer hash values. Its integer root set has the original fiber-root
count, and every value has the constructed polynomial bit bound.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberHashRoots
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

noncomputable def values (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Finset ℤ :=
  Finset.univ.image (BoundedAlgebraicFiberHashChoice.hash P F c)

theorem mem_values (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) :
    z ∈ values P F c ↔ ∃ x, BoundedAlgebraicFiberHashChoice.hash P F c x = z := by
  simp only [values, Finset.mem_image, Finset.mem_univ, true_and]

theorem values_card (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : (values P F c).card = BoundedAlgebraicSlice.RootCount.count P F c := by
  rw [values, Finset.card_image_of_injective _ (BoundedAlgebraicFiberHashChoice.hash_injective P F c), Finset.card_univ]
  exact Fintype.card_coe _

theorem values_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) (hz : z ∈ values P F c) :
    z.natAbs < 2 ^ BoundedAlgebraicFiberHashChoice.hashBits F c := by
  obtain ⟨x, rfl⟩ := (mem_values P F c z).mp hz
  exact Nat.size_le.mp (BoundedAlgebraicFiberHashChoice.hash_bits P F c x)

theorem rootSet_eq (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    BoundedAlgebraicFiberPencilCuts.rootSet P F (BoundedAlgebraicFiberHashChoice.value P F c) =
      (values P F c).image (Int.castRingHom ℝ) := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedAlgebraicFiberHashChoice.value_spec P F c
  have hh (x : BoundedAlgebraicFiberRecordSpan.Root P F c) : BoundedAlgebraicFiberHashChoice.hash P F c x =
      BoundedAlgebraicFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x := by
    unfold BoundedAlgebraicFiberHashChoice.hash
    rw [hv]
    simp only [BoundedAlgebraicFiberWeightedMoments.context, BoundedAlgebraicFiberWeightedMoments.modulus,
      BoundedAlgebraicFiberWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by ext z; simp
  have hm := congrArg (fun p : ℚ[X] => p.map (Rat.castHom ℝ))
    (BoundedAlgebraicFiberPencilSource.determinant_packet P F c m t)
  rw [Polynomial.map_map, hcomp, BoundedAlgebraicFiberBasisPencil.pencil_eq] at hm
  rw [hv, BoundedAlgebraicFiberPencilCuts.rootSet, hm,
    FunctionBasisPencil.mapped_roots (Rat.castHom ℝ) (Rat.castHom ℝ).injective _ _
      (BoundedAlgebraicFiberBasisPencil.square_det_ne_zero P F c)]
  change (Finset.univ.image (fun i : Fin (BoundedAlgebraicSlice.RootCount.count P F c) =>
      (Rat.castHom ℝ) ((BoundedAlgebraicFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t
        (BoundedAlgebraicFiberBasisPencil.rootEquiv P F c i) : ℤ) : ℚ))) = _
  rw [values, Finset.image_image]
  apply Finset.ext
  intro z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
    Rat.coe_castHom, Rat.cast_intCast, Int.coe_castRingHom, hh]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨BoundedAlgebraicFiberBasisPencil.rootEquiv P F c i, hi⟩
  · rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := (BoundedAlgebraicFiberBasisPencil.rootEquiv P F c).surjective x
    exact ⟨i, hx⟩

theorem real_mem_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) :
    (z : ℝ) ∈ BoundedAlgebraicFiberPencilCuts.rootSet P F (BoundedAlgebraicFiberHashChoice.value P F c) ↔ z ∈ values P F c := by
  rw [rootSet_eq]
  simp only [Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

noncomputable def rank (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) : ℕ :=
  ((values P F c).filter (fun a => a < z)).card

private theorem ordered_rank {α : Type*} [LinearOrder α] (s : Finset α) (x : {a // a ∈ s}) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun a => a < x.val)).card := by
  let e := (s.orderIsoOfFin rfl).symm
  rw [← Finset.card_range (e x).val]
  symm
  apply Finset.card_bij (fun y hy => (e ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
  · intro y hy
    rw [Finset.mem_range]
    exact e.lt_iff_lt.mpr (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact congrArg Subtype.val (e.injective (Fin.ext hab))
  · intro n hn
    have hn' : n < (e x).val := Finset.mem_range.mp hn
    let j : Fin s.card := ⟨n, hn'.trans (e x).isLt⟩
    refine ⟨(e.symm j).val, Finset.mem_filter.mpr ⟨(e.symm j).property, ?_⟩, ?_⟩
    · change e.symm j < x
      have h := e.symm.strictMono (show j < e x from hn')
      rw [e.symm_apply_apply] at h
      exact h
    · simp only [e.apply_symm_apply]
      rfl

theorem rank_lt (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) (hz : z ∈ values P F c) :
    rank P F c z < BoundedAlgebraicSlice.RootCount.count P F c := by
  have H := ((values P F c).orderIsoOfFin rfl).symm ⟨z, hz⟩ |>.isLt
  rw [ordered_rank, values_card] at H
  exact H

theorem exists_rank (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : ℕ) (hr : r < BoundedAlgebraicSlice.RootCount.count P F c) :
    ∃ z ∈ values P F c, rank P F c z = r := by
  have hr' : r < (values P F c).card := by rwa [values_card]
  let e := (values P F c).orderIsoOfFin rfl
  let x := e ⟨r, hr'⟩
  refine ⟨x.val, x.property, ?_⟩
  have H := ordered_rank (values P F c) x
  rw [e.symm_apply_apply] at H
  exact H.symm

theorem rank_unique (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) {a b : ℤ} (ha : a ∈ values P F c) (hb : b ∈ values P F c)
    (he : rank P F c a = rank P F c b) : a = b := by
  let e := (values P F c).orderIsoOfFin rfl
  have hr : (e.symm ⟨a, ha⟩).val = (e.symm ⟨b, hb⟩).val := by
    rw [ordered_rank, ordered_rank]
    exact he
  exact congrArg Subtype.val (e.symm.injective (Fin.ext hr))

end LeanCanny.Encoding.BoundedAlgebraicFiberHashRoots
