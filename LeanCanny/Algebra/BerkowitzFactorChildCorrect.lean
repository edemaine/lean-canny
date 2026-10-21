/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzFactorChild

/-!
# Correct results of the factor-entry child

The four decoded fields connect the bitstring selector to the mathematical
coefficient factor. A valid original-matrix access contract supplies the
diagonal and trailing-block entries. These hypotheses concern input access,
not the answer to the requested factor computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.FactorChild
open Complexity
open LeanCanny.Encoding
open MatrixPower
open Matrix

structure CorrectAt (a : Access) (c : List Bool) (m : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod m)) : Prop where
  dimension : a.dimension c = BinaryNatCode.encode n
  modulus : a.modulus c = BinaryNatCode.encode m
  entry : ∀ i j, a.entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
    residueBits (A i j)

structure DecodedAt (a : Access) (p : List Bool) (s t d k : ℕ) : Prop where
  sourceLayer : QueryBits.sourceLayer a.dimension p = BinaryNatCode.encode s
  targetLayer : QueryBits.targetLayer a.dimension p = BinaryNatCode.encode t
  sourceDegree : QueryBits.sourceDegree a.dimension p = BinaryNatCode.encode d
  targetDegree : QueryBits.targetDegree a.dimension p = BinaryNatCode.encode k

theorem decoded_packet (a : Access) (c : List Bool) (n i j : ℕ)
    (hd : a.dimension c = BinaryNatCode.encode n) :
    DecodedAt a (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))
      (i / (n + 1)) (j / (n + 1)) (i % (n + 1)) (j % (n + 1)) :=
  ⟨QueryBits.sourceLayer_packet _ _ _ _ _ hd, QueryBits.targetLayer_packet _ _ _ _ _ hd,
    QueryBits.sourceDegree_packet _ _ _ _ _ hd, QueryBits.targetDegree_packet _ _ _ _ _ hd⟩

theorem remaining_code (a : Access) (p : List Bool) (n s t d k : ℕ)
    (hd : a.dimension (pairFst p) = BinaryNatCode.encode n) (hq : DecodedAt a p s t d k) :
    QueryBits.remaining a.dimension p = BinaryNatCode.encode (n - s - 1) := by
  simp only [QueryBits.remaining, QueryBits.inputDimension, hd, hq.sourceLayer, BinaryNat.sub_pair,
    BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem exponent_code (a : Access) (p : List Bool) (s t d k : ℕ) (hq : DecodedAt a p s t d k) :
    QueryBits.momentExponent a.dimension p = BinaryNatCode.encode (k - (d + 1)) := by
  simp only [QueryBits.momentExponent, hq.sourceDegree, hq.targetDegree, BinaryNat.succ_eq_bits,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selector_code (a : Access) (p : List Bool) (n s t d k : ℕ)
    (hd : a.dimension (pairFst p) = BinaryNatCode.encode n) (hq : DecodedAt a p s t d k) :
    QueryBits.selector a.dimension p = QueryBits.select n s t d k := by
  simp only [QueryBits.selector, QueryBits.select, QueryBits.inputDimension, hd,
    hq.sourceLayer, hq.targetLayer, hq.sourceDegree, hq.targetDegree,
    remaining_code a p n s t d k hd hq, MatrixMoment.EntryBits.succ_code,
    BinaryNatCode.encode_injective.eq_iff, QueryBits.code_value]

theorem time_moment (a : Access) (p : List Bool) (n s t d k : ℕ)
    (hd : a.dimension (pairFst p) = BinaryNatCode.encode n) (hq : DecodedAt a p s t d k)
    (hmode : QueryBits.selector a.dimension p = [true, true]) :
    time a p = MatrixPower.work (n - s - 1 + 2)
      (k - (d + 1) + 2).size (k - (d + 1) + 2) + 1 := by
  simp only [time, hmode, ↓reduceIte, remaining_code a p n s t d k hd hq,
    exponent_code a p s t d k hq, QueryBits.code_value]

noncomputable def value {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (s t d k : ℕ) : R :=
  if s + 1 = t then if hs : s < n then coefficientKernel (principalBlock A s hs) d k else 0 else 0

theorem value_eq_powerMatrix {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin ((n + 1) * (n + 1))) :
    value A i.divNat.val j.divNat.val i.modNat.val j.modNat.val = powerMatrix A i j := by
  rw [powerMatrix_apply_direct]
  by_cases he : i.divNat.val + 1 = j.divNat.val
  · have hs : i.divNat.val < n := by have := j.divNat.isLt; omega
    simp only [value, he, hs, ↓reduceIte, ↓reduceDIte, factorDirect_apply _ A _ hs]
  · simp only [value, he, ↓reduceIte]

theorem run_immediate (a : Access) (p : List Bool)
    (h : QueryBits.selector a.dimension p ≠ [true, true]) :
    output a ((advance a)^[time a p] (start a p)) = fastValue a p := by
  rw [time_immediate a p h]
  simp only [start, h, ↓reduceIte, Function.iterate_zero, id_eq]
  exact immediate_output a p h

theorem run_moment (a : Access) (p : List Bool) (m n s t d k : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a (pairFst p) m A)
    (hq : DecodedAt a p s t d k) (hs : s < n)
    (hmode : QueryBits.selector a.dimension p = [true, true]) :
    output a ((advance a)^[time a p] (start a p)) =
      residueBits (-borderMoment (fun i => principalBlock A s hs 0 i.succ)
        (fun i => principalBlock A s hs i.succ 0)
        ((principalBlock A s hs).submatrix Fin.succ Fin.succ) (k - (d + 1))) := by
  have hd := remaining_code a p n s t d k hb.dimension hq
  have he := exponent_code a p s t d k hq
  have hc := EntryAccess.momentCallbacks_correctAt a.dimension a.entry a.modulus p m n s A hs
    hb.dimension hq.sourceLayer hb.modulus hb.entry
  have htime := time_moment a p n s t d k hb.dimension hq hmode
  have hrun := MatrixMoment.EntryBits.run (EntryAccess.momentAccess a.dimension a.entry)
    (EntryAccess.childModulus a.modulus) (QueryBits.momentExponent a.dimension) p m (n - s - 1)
    (k - (d + 1)) (fun i => principalBlock A s hs 0 i.succ)
    (fun i => principalBlock A s hs i.succ 0)
    ((principalBlock A s hs).submatrix Fin.succ Fin.succ) hc hd he
  rw [htime]
  simp only [start, hmode, ↓reduceIte, advance, callbacks]
  rw [hrun]
  simp only [output, pairFst_pair, hmode, ↓reduceIte]
  exact MatrixMoment.EntryBits.negativeResult_done _ p m (n - s - 1) _ hb.modulus

theorem run_correct (a : Access) (p : List Bool) (m n s t d k : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a (pairFst p) m A)
    (hq : DecodedAt a p s t d k) :
    output a ((advance a)^[time a p] (start a p)) = residueBits (value A s t d k) := by
  have hsel := selector_code a p n s t d k hb.dimension hq
  by_cases hedge : s + 1 = t
  · by_cases hs : s < n
    · by_cases hshift : k + 1 = d
      · have hmode : QueryBits.selector a.dimension p = [true] := by
          rw [hsel]
          simp only [QueryBits.select, hedge, hs, hshift, ↓reduceIte]
        rw [run_immediate a p (by rw [hmode]; decide)]
        simp only [fastValue, hmode, ↓reduceIte, hb.modulus, ArithmeticBits.one_residueBits,
          value, hedge, hs, ↓reduceDIte, coefficientKernel_cases, hshift]
      · by_cases hdiag : k = d
        · have hmode : QueryBits.selector a.dimension p = [false, true] := by
            rw [hsel]
            exact (QueryBits.select_diagonal_iff n s t d k).mpr ⟨hedge, hs, hdiag⟩
          have hentry : a.entry (EntryAccess.diagonalInput a.dimension p) =
              residueBits (A ⟨s, hs⟩ ⟨s, hs⟩) := by
            rw [EntryAccess.diagonalInput_code a.dimension p s hq.sourceLayer]
            exact hb.entry ⟨s, hs⟩ ⟨s, hs⟩
          rw [run_immediate a p (by rw [hmode]; decide)]
          simp [fastValue, hmode, hb.modulus, hentry, ArithmeticBits.negate_residueBits,
            value, hedge, hs, coefficientKernel_cases, hdiag, principalBlock]
        · by_cases hmoment : d < k ∧ k ≤ n - s - 1
          · have hmode : QueryBits.selector a.dimension p = [true, true] := by
              rw [hsel]
              simp only [QueryBits.select, hedge, hs, hshift, hdiag, hmoment.1, hmoment.2, ↓reduceIte]
            rw [run_moment a p m n s t d k A hb hq hs hmode]
            simp only [value, hedge, hs, ↓reduceIte, ↓reduceDIte, coefficientKernel_cases,
              hshift, hdiag, hmoment, and_self]
          · have hmode : QueryBits.selector a.dimension p = [] := by
              rw [hsel]
              simp only [QueryBits.select, hedge, hs, hshift, hdiag, ↓reduceIte]
              by_cases hl : d < k <;> simp_all
            rw [run_immediate a p (by rw [hmode]; decide)]
            simp [fastValue, hmode, value, hedge, hs, coefficientKernel_cases, hshift, hdiag, hmoment,
              residueBits, BinaryNatCode.encode]
    · have hmode : QueryBits.selector a.dimension p = [] := by
        rw [hsel]
        simp only [QueryBits.select, hedge, hs, ↓reduceIte]
      rw [run_immediate a p (by rw [hmode]; decide)]
      simp [fastValue, hmode, value, hedge, hs, residueBits, BinaryNatCode.encode]
  · have hmode : QueryBits.selector a.dimension p = [] := by
      rw [hsel]
      simp only [QueryBits.select, hedge, ↓reduceIte]
    rw [run_immediate a p (by rw [hmode]; decide)]
    simp [fastValue, hmode, value, hedge, residueBits, BinaryNatCode.encode]

theorem run_packet (a : Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a c m A)
    (i j : Fin ((n + 1) * (n + 1))) :
    let p := pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    output a ((advance a)^[time a p] (start a p)) = residueBits (powerMatrix A i j) := by
  dsimp only
  rw [← value_eq_powerMatrix A i j]
  exact run_correct a _ m n i.divNat.val j.divNat.val i.modNat.val j.modNat.val A
    (by simpa only [pairFst_pair] using hb) (decoded_packet a c n i.val j.val hb.dimension)

theorem moment_conditions (a : Access) (p : List Bool) (n s t d k : ℕ)
    (hd : a.dimension (pairFst p) = BinaryNatCode.encode n) (hq : DecodedAt a p s t d k)
    (hmode : QueryBits.selector a.dimension p = [true, true]) :
    s + 1 = t ∧ s < n ∧ d < k ∧ k ≤ n - s - 1 := by
  apply (QueryBits.select_moment_iff n s t d k).mp
  exact (selector_code a p n s t d k hd hq).symm.trans hmode

end LeanCanny.Algebra.Berkowitz.FactorChild
