/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalParameterRoots
public import LeanCanny.Algebra.RationalSubstitutionSignWith
public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds

/-! # Exact critical-sample filters on the native rational parameter

Even denominator powers turn each original critical equation into an integer
univariate polynomial. On parameter roots, simultaneous vanishing is exactly
the critical-sample condition. Decoding gives a bijection for both real and
complex samples; no extraneous coordinate-root tuples survive the filters.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalFilters
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate

noncomputable def row (P : Readers) (w : List Bool) : Fin (P.dim (pairFst w) + 4) :=
  ⟨min (Nat.fromBitsLE (pairSnd w)) (P.dim (pairFst w) + 3), by omega⟩

theorem row_unary {P : Readers} (h : P.PolyTime) : UnaryFn (fun w => (row P w).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))

theorem row_packet (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4)) :
    (row P (pair c (BinaryNatCode.encode i.val))).val = i.val := by
  simp only [row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.min_eq_left (by have := i.isLt; omega)

noncomputable def gridDegree (P : Readers) (c : List Bool) : ℕ := 2 ^ BoundedCriticalProjection.systemWidth P c

theorem gridDegree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (gridDegree P) :=
  (BinaryFn.const 2).powUnary (BoundedCriticalProjection.systemWidth_unary h)

theorem equation_degree (P : Readers) (c : List Bool) (j i : Fin (P.dim c + 4)) :
    (BoundedFullCriticalSamples.equations P c j).degreeOf i < gridDegree P c :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans_lt
    ((BoundedFullCriticalSamples.equations_degree P c j).trans_lt (BoundedProjectionMacaulay.width_fits P c))

noncomputable def numerator (P : Readers) (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i))).numerator
noncomputable def denominator (P : Readers) (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i))).denominator

noncomputable def polynomial (P : Readers) (w : List Bool) : Polynomial ℤ :=
  RationalSubstitution.clearedWith (fun _ => gridDegree P (pairFst w))
    (BoundedFullCriticalSamples.equations P (pairFst w) (row P w))
    (fun i => numerator P (pairFst w) i.val) (fun i => denominator P (pairFst w) i.val)

variable {K : Type*} [Field K] [CharZero K]

theorem eval (P : Readers) (w : List Bool) (theta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P (pairFst w)).eval₂ (Int.castRingHom K) theta = 0) :
    (polynomial P w).eval₂ (Int.castRingHom K) theta =
      (∏ i : Fin (P.dim (pairFst w) + 4), (denominator P (pairFst w) i.val).eval₂
        (Int.castRingHom K) theta ^ (2 * gridDegree P (pairFst w))) *
      (BoundedFullCriticalSamples.equations P (pairFst w) (row P w)).eval₂ (Int.castRingHom K)
        (BoundedCriticalParameterRoots.decode P (pairFst w) theta) := by
  have H := RationalSubstitution.eval₂_clearedWith (Int.castRingHom K) theta
    (fun _ => gridDegree P (pairFst w)) (BoundedFullCriticalSamples.equations P (pairFst w) (row P w))
    (fun i => numerator P (pairFst w) i.val) (fun i => denominator P (pairFst w) i.val)
    (fun i => (equation_degree P (pairFst w) (row P w) i).le)
    (fun i => BoundedCriticalParameterRoots.denominator_ne_zero P (pairFst w) theta ht i)
  have hd : BoundedCriticalParameterRoots.decode P (pairFst w) theta =
      fun i => (numerator P (pairFst w) i.val).eval₂ (Int.castRingHom K) theta /
        (denominator P (pairFst w) i.val).eval₂ (Int.castRingHom K) theta := rfl
  rw [hd]
  exact H

theorem zero_iff (P : Readers) (w : List Bool) (theta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P (pairFst w)).eval₂ (Int.castRingHom K) theta = 0) :
    (polynomial P w).eval₂ (Int.castRingHom K) theta = 0 ↔
      (BoundedFullCriticalSamples.equations P (pairFst w) (row P w)).eval₂ (Int.castRingHom K)
        (BoundedCriticalParameterRoots.decode P (pairFst w) theta) = 0 := by
  have hn : (∏ i : Fin (P.dim (pairFst w) + 4), (denominator P (pairFst w) i.val).eval₂
      (Int.castRingHom K) theta ^ (2 * gridDegree P (pairFst w))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _
      (BoundedCriticalParameterRoots.denominator_ne_zero P (pairFst w) theta ht i))
  rw [eval P w theta ht, mul_eq_zero]
  simp only [hn, false_or]

def Valid (P : Readers) (c : List Bool) (theta : K) : Prop :=
  (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0 ∧
    ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom K)
      (BoundedCriticalParameterRoots.decode P c theta) = 0

abbrev Roots (P : Readers) (c : List Bool) (K : Type*) [Field K] [CharZero K] := {theta : K // Valid P c theta}

theorem zero_packet (P : Readers) (c : List Bool) (j : Fin (P.dim c + 4)) (theta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0) :
    (polynomial P (pair c (BinaryNatCode.encode j.val))).eval₂ (Int.castRingHom K) theta = 0 ↔
      (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom K)
        (BoundedCriticalParameterRoots.decode P c theta) = 0 := by
  generalize hq : pair c (BinaryNatCode.encode j.val) = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd q) = j.val := by rw [← hq, pairSnd_pair]; exact Nat.fromBitsLE_bits _
  subst c
  have hj : row P q = j := by
    apply Fin.ext
    simp only [row, hr]
    exact Nat.min_eq_left (by have := j.isLt; omega)
  simpa only [hj] using zero_iff P q theta ht

theorem valid_iff_filters (P : Readers) (c : List Bool) (theta : K) : Valid P c theta ↔
    (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0 ∧
      ∀ j : Fin (P.dim c + 4), (polynomial P (pair c (BinaryNatCode.encode j.val))).eval₂
        (Int.castRingHom K) theta = 0 := by
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨ht, fun j => ?_⟩
    exact (zero_packet P c j theta ht).mpr (hs j)
  · rintro ⟨ht, hs⟩
    refine ⟨ht, fun j => ?_⟩
    exact (zero_packet P c j theta ht).mp (hs j)

noncomputable def sampleEquiv (P : Readers) (c : List Bool)
    (complete : ∀ x : {x : Fin (P.dim c + 4) → K // ∀ j,
      (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom K) x = 0},
      ∃ theta : K, (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0 ∧
        BoundedCriticalParameterRoots.decode P c theta = x.val) :
    Roots P c K ≃ {x : Fin (P.dim c + 4) → K // ∀ j,
      (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom K) x = 0} := by
  let f := fun t : Roots P c K => (⟨BoundedCriticalParameterRoots.decode P c t.val, t.property.2⟩ :
    {x : Fin (P.dim c + 4) → K // ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom K) x = 0})
  apply Equiv.ofBijective f
  constructor
  · intro t u h
    apply Subtype.ext
    exact BoundedCriticalParameterRoots.decode_injective P c t.val u.val t.property.1 u.property.1
      (congrArg Subtype.val h)
  · intro x
    obtain ⟨theta, ht, hd⟩ := complete x
    refine ⟨⟨theta, ht, ?_⟩, Subtype.ext hd⟩
    rw [hd]
    exact x.property

noncomputable def realEquiv (P : Readers) (c : List Bool) : Roots P c ℝ ≃ BoundedFullCriticalSamples.Samples P c :=
  sampleEquiv P c (fun x => by
    obtain ⟨theta, ht, hx⟩ := BoundedCriticalRationalCoordinates.real_sample_complete P c x
    exact ⟨theta, ht, funext fun i => (hx i).2⟩)

noncomputable def complexEquiv (P : Readers) (c : List Bool) : Roots P c ℂ ≃ BoundedFullComplexSamples.Samples P c :=
  sampleEquiv P c (fun x => by
    obtain ⟨theta, ht, hx⟩ := BoundedCriticalRationalCoordinates.sample_complete P c x
    exact ⟨theta, ht, funext fun i => (hx i).2⟩)

theorem complex_card (P : Readers) (c : List Bool) :
    Nat.card (Roots P c ℂ) ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c :=
  (Nat.card_congr (complexEquiv P c)).trans_le (BoundedFullComplexSamples.finite_samples P c).2

end LeanCanny.Encoding.BoundedCriticalFilters
