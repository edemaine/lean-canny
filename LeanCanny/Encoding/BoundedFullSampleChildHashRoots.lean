/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildPencilCuts

/-! # Exact integer roots of the selected hash polynomial

The real roots of the native integer determinant are exactly the selected
integer hash values. Its integer root set has the original regular-child
count, and every value has the constructed polynomial bit bound.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildHashRoots
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

noncomputable def values (P : Inputs) (c : List Bool) : Finset ℤ :=
  Finset.univ.image (BoundedFullSampleChildHashChoice.hash P c)

theorem mem_values (P : Inputs) (c : List Bool) (z : ℤ) :
    z ∈ values P c ↔ ∃ x, BoundedFullSampleChildHashChoice.hash P c x = z := by
  simp only [values, Finset.mem_image, Finset.mem_univ, true_and]

theorem values_card (P : Inputs) (c : List Bool) : (values P c).card = BoundedFullSampleChildRegularCount.count P c := by
  rw [values, Finset.card_image_of_injective _ (BoundedFullSampleChildHashChoice.hash_injective P c), Finset.card_univ]
  rw [Fintype.card_coe]
  exact BoundedFullSampleChildQueries.roots_card P c

theorem values_bound (P : Inputs) (c : List Bool) (z : ℤ) (hz : z ∈ values P c) :
    z.natAbs < 2 ^ BoundedFullSampleChildHashChoice.hashBits P c := by
  obtain ⟨x, rfl⟩ := (mem_values P c z).mp hz
  exact Nat.size_le.mp (BoundedFullSampleChildHashChoice.hash_bits P c x)

theorem rootSet_eq (P : Inputs) (c : List Bool) :
    BoundedFullSampleChildPencilCuts.rootSet P (BoundedFullSampleChildHashChoice.value P c) =
      (values P c).image (Int.castRingHom ℝ) := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedFullSampleChildHashChoice.value_spec P c
  have hh (x : BoundedFullSampleChildRecordSpan.Root P c) : BoundedFullSampleChildHashChoice.hash P c x =
      BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x := by
    unfold BoundedFullSampleChildHashChoice.hash
    rw [hv]
    simp only [BoundedFullSampleChildWeightedMoments.context, BoundedFullSampleChildWeightedMoments.modulus,
      BoundedFullSampleChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by ext z; simp
  have hm := congrArg (fun p : ℚ[X] => p.map (Rat.castHom ℝ))
    (BoundedFullSampleChildPencilSource.determinant_packet P c m t)
  rw [Polynomial.map_map, hcomp, BoundedFullSampleChildBasisPencil.pencil_eq] at hm
  rw [hv, BoundedFullSampleChildPencilCuts.rootSet, hm,
    FunctionBasisPencil.mapped_roots (Rat.castHom ℝ) (Rat.castHom ℝ).injective _ _
      (BoundedFullSampleChildBasisPencil.square_det_ne_zero P c)]
  change (Finset.univ.image (fun i : Fin (BoundedFullSampleChildRegularCount.count P c) =>
      (Rat.castHom ℝ) ((BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t
        (BoundedFullSampleChildBasisPencil.rootEquiv P c i) : ℤ) : ℚ))) = _
  rw [values, Finset.image_image]
  apply Finset.ext
  intro z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply,
    Rat.coe_castHom, Rat.cast_intCast, Int.coe_castRingHom, hh]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨BoundedFullSampleChildBasisPencil.rootEquiv P c i, hi⟩
  · rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := (BoundedFullSampleChildBasisPencil.rootEquiv P c).surjective x
    exact ⟨i, hx⟩

theorem real_mem_iff (P : Inputs) (c : List Bool) (z : ℤ) :
    (z : ℝ) ∈ BoundedFullSampleChildPencilCuts.rootSet P (BoundedFullSampleChildHashChoice.value P c) ↔ z ∈ values P c := by
  rw [rootSet_eq]
  simp only [Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

noncomputable def rank (P : Inputs) (c : List Bool) (z : ℤ) : ℕ :=
  ((values P c).filter (fun a => a < z)).card

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

theorem rank_lt (P : Inputs) (c : List Bool) (z : ℤ) (hz : z ∈ values P c) :
    rank P c z < BoundedFullSampleChildRegularCount.count P c := by
  have H := ((values P c).orderIsoOfFin rfl).symm ⟨z, hz⟩ |>.isLt
  rw [ordered_rank, values_card] at H
  exact H

theorem exists_rank (P : Inputs) (c : List Bool) (r : ℕ) (hr : r < BoundedFullSampleChildRegularCount.count P c) :
    ∃ z ∈ values P c, rank P c z = r := by
  have hr' : r < (values P c).card := by rwa [values_card]
  let e := (values P c).orderIsoOfFin rfl
  let x := e ⟨r, hr'⟩
  refine ⟨x.val, x.property, ?_⟩
  have H := ordered_rank (values P c) x
  rw [e.symm_apply_apply] at H
  exact H.symm

theorem rank_unique (P : Inputs) (c : List Bool) {a b : ℤ} (ha : a ∈ values P c) (hb : b ∈ values P c)
    (he : rank P c a = rank P c b) : a = b := by
  let e := (values P c).orderIsoOfFin rfl
  have hr : (e.symm ⟨a, ha⟩).val = (e.symm ⟨b, hb⟩).val := by
    rw [ordered_rank, ordered_rank]
    exact he
  exact congrArg Subtype.val (e.symm.injective (Fin.ext hr))

end LeanCanny.Encoding.BoundedFullSampleChildHashRoots
