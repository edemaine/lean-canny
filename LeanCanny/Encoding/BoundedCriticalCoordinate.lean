/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionFamilyCoefficient
public import LeanCanny.Encoding.BoundedComplexSeparator
public import LeanCanny.Encoding.FixedWidthNatVectorFP

/-! # Native coordinate equations for the actual full critical samples

A binary coordinate index selects a unit weight record. Out-of-range indices
give the zero projection while retaining the same bounds and native readers.
In-range equations annihilate that coordinate of every complex critical sample.
The complex separating projection also has a native coefficient reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalCoordinate
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open Brackets MatrixPower
open scoped Classical BigOperators

noncomputable def record (P : Readers) (q : List Bool) : List Bool :=
  FixedWidthNatVector.encode (P.dim (pairFst q) + 4) (BoundedCriticalSeparator.width P (pairFst q))
    (fun i => if i = Nat.fromBitsLE (pairSnd q) then 1 else 0)

theorem record_FP {P : Readers} (h : P.PolyTime) : record P ∈ FP := by
  let read := fun z => BinaryNatCode.encode
    (if Nat.fromBitsLE (pairSnd z) = Nat.fromBitsLE (pairSnd (pairFst z)) then 1 else 0)
  have hr : read ∈ FP := (BinaryFn.ite
    ((BinaryFn.fromBits pairSnd_mem_FP).eq
      (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)))
    (BinaryFn.const 1) (BinaryFn.const 0)).bits_mem_FP
  exact FixedWidthNatVector.encode_mem_FP _ _ _
    ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 4))
    ((BoundedCriticalSeparator.width_unary h).comp pairFst_mem_FP) read hr
    (fun c i => by simp only [read, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem record_length (P : Readers) (q : List Bool) :
    (record P q).length = (P.dim (pairFst q) + 4) * BoundedCriticalSeparator.width P (pairFst q) :=
  FixedWidthNatVector.length_encode _ _ _

theorem weight (P : Readers) (q : List Bool) (i : Fin (P.dim (pairFst q) + 4)) :
    BoundedCriticalSeparator.weight (P.comp pairFst) (record P) q i.val =
      if i.val = Nat.fromBitsLE (pairSnd q) then 1 else 0 := by
  change Nat.fromBitsLE (((record P q).drop (i.val * BoundedCriticalSeparator.width P (pairFst q))).take
    (BoundedCriticalSeparator.width P (pairFst q))) = _
  apply FixedWidthNatVector.decode_block _ _ _ _ i.isLt
  have hw : 0 < BoundedCriticalSeparator.width P (pairFst q) := by
    unfold BoundedCriticalSeparator.width
    omega
  split_ifs
  · exact Nat.one_lt_two_pow hw.ne'
  · positivity

theorem value_eq (P : Readers) (q : List Bool) (i : Fin (P.dim (pairFst q) + 4))
    (hi : Nat.fromBitsLE (pairSnd q) = i.val) (x : Fin (P.dim (pairFst q) + 4) → ℂ) :
    BoundedFullComplexSamples.value (P.comp pairFst) (record P) q x = x i := by
  change (∑ j : Fin (P.dim (pairFst q) + 4),
    x j * (BoundedCriticalSeparator.weight (P.comp pairFst) (record P) q j.val : ℂ)) = x i
  simp only [weight, hi]
  simp [Fin.val_inj]

noncomputable def polynomial (P : Readers) : List Bool → Polynomial ℤ :=
  BoundedProjectionFamily.polynomial (P.comp pairFst) (record P)

theorem ne_zero (P : Readers) (q : List Bool) : polynomial P q ≠ 0 :=
  BoundedProjectionFamily.ne_zero _ _ _

theorem degree_le (P : Readers) (q : List Bool) :
    (polynomial P q).natDegree ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) :=
  BoundedProjectionFamily.degree_le _ _ _

theorem coefficient_bits (P : Readers) (q : List Bool) (k : ℕ) :
    ((polynomial P q).coeff k).natAbs.size ≤ BoundedCriticalProjection.coefficientBits P (pairFst q) :=
  BoundedProjectionFamily.coefficient_bits _ _ _ _

theorem eval_sample (P : Readers) (q : List Bool) (i : Fin (P.dim (pairFst q) + 4))
    (hi : Nat.fromBitsLE (pairSnd q) = i.val) (x : BoundedFullComplexSamples.Samples (P.comp pairFst) q) :
    (polynomial P q).eval₂ (Int.castRingHom ℂ) (x.val i) = 0 := by
  rw [← value_eq P q i hi x.val]
  exact BoundedProjectionFamily.eval_sample _ _ _ x

theorem equations_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullCriticalSamples.equations (P.comp f) c = BoundedFullCriticalSamples.equations P (f c) := by
  unfold BoundedFullCriticalSamples.equations BoundedFullCriticalSamples.direction
    BoundedFullDirectionQueries.direction FixedWidthQuery.coordinate
  simp only [BoundedFullDirectionChoice.record_comp]
  rfl

theorem eval_coordinate (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4))
    (x : BoundedFullComplexSamples.Samples P c) :
    (polynomial P (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℂ) (x.val i) = 0 := by
  generalize hq : pair c (BinaryNatCode.encode i.val) = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hi : Nat.fromBitsLE (pairSnd q) = i.val := by
    rw [← hq, pairSnd_pair]
    exact Nat.fromBitsLE_bits i.val
  subst c
  let y : BoundedFullComplexSamples.Samples (P.comp pairFst) q :=
    ⟨x.val, by rw [equations_comp]; exact x.property⟩
  exact eval_sample P q i hi y

theorem eval_real_coordinate (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4))
    (x : BoundedFullCriticalSamples.Samples P c) :
    (polynomial P (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (x.val i) = 0 := by
  have he := eval_coordinate P c i (BoundedFullComplexSamples.ofReal P c x)
  have hm : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  apply Complex.ofReal_injective
  change Complex.ofRealHom (_ : ℝ) = Complex.ofRealHom 0
  rw [Polynomial.hom_eval₂, hm, map_zero]
  exact he

noncomputable def coefficient (P : Readers) : List Bool → List Bool :=
  BoundedProjectionFamilyCoefficient.value (P.comp pairFst) (record P)

theorem coefficient_eq (P : Readers) (q : List Bool) : coefficient P q =
    residueBits (((polynomial P (pairFst (pairFst q))).coeff (Nat.fromBitsLE (pairSnd q)) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)) := rfl

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P) :=
  BoundedProjectionFamilyCoefficient.evaluator (h.comp pairFst_mem_FP)
    (SpaceFunction.ofFP _ (record_FP h)) (fun q => ha (pairFst q))

theorem coefficient_packet (P : Readers) (q m : List Bool) (k : ℕ) :
    coefficient P (pair (pair q m) (BinaryNatCode.encode k)) =
      residueBits (((polynomial P q).coeff k : ℤ) : ZMod (Nat.fromBitsLE m + 1)) :=
  BoundedProjectionFamilyCoefficient.value_packet _ _ _ _ _

noncomputable def separatingPolynomial (P : Readers) : List Bool → Polynomial ℤ :=
  BoundedProjectionFamily.polynomial P (BoundedComplexSeparator.record P)

theorem separating_eval_sample (P : Readers) (c : List Bool) (x : BoundedFullComplexSamples.Samples P c) :
    (separatingPolynomial P c).eval₂ (Int.castRingHom ℂ)
      (BoundedFullComplexSamples.value P (BoundedComplexSeparator.record P) c x.val) = 0 :=
  BoundedProjectionFamily.eval_sample _ _ _ _

theorem separating_coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionFamilyCoefficient.value P (BoundedComplexSeparator.record P)) :=
  BoundedProjectionFamilyCoefficient.evaluator h (BoundedComplexSeparator.evaluator h ha) ha

end LeanCanny.Encoding.BoundedCriticalCoordinate
