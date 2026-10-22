/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationLayout
public import LeanCanny.Algebra.MacaulayEntryCorrect

/-! # Certified coefficient readers for partial homogenization

The first block is the new coordinate. A clipped sum checks the selected point
prefix's degree; deleting the first block prepares one original coefficient
query. Unary metadata bounds all controls, and a space-bounded source evaluator
accounts for the only coefficient call.
-/

@[expose] public section

namespace LeanCanny.Algebra.HomogenizationBits
open LeanCanny.Encoding LeanCanny.Computation
open FixedWidthPolynomial
open scoped BigOperators

def read (N W : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.read ((fun c => N c + 1) ∘ pairFst) (W ∘ pairFst) rankTarget

theorem read_mem_FP {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) : read N W ∈ FP :=
  FixedWidthQuery.read_mem_FP ((hN.add (UnaryFn.const 1)).comp pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) rankTarget_mem_FP

def total (N A W D : List Bool → ℕ) (q : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (N (pairFst q) + 1),
    if i < A (pairFst q) + 1 then min (entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i) (D (pairFst q) + 1) else 0

theorem total_unary {N A W D : List Bool → ℕ} (hN : UnaryFn N) (hA : UnaryFn A)
    (hW : UnaryFn W) (hD : UnaryFn D) : UnaryFn (total N A W D) := by
  have hr := mem_FP_comp MacaulayBits.loopQuery_mem_FP (read_mem_FP hN hW)
  have hd := ((hD.add (UnaryFn.const 1)).comp pairFst_mem_FP).comp pairFst_mem_FP
  have hc := UnaryFn.fromBitsLE_min hr hd
  have ha := ((hA.add (UnaryFn.const 1)).comp pairFst_mem_FP).comp pairFst_mem_FP
  have ht := UnaryFn.ite (FPPred.lt UnaryFn.index ha) hc (UnaryFn.const 0)
  have hs := ((hN.add (UnaryFn.const 1)).comp pairFst_mem_FP).sum ht
  refine hs.of_eq (fun q => ?_)
  simp only [MacaulayBits.loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, read, FixedWidthQuery.read_packet, MacaulayBits.fromBits_encode, total]
  apply Finset.sum_congr rfl
  intro i hi
  have hn : i < N (pairFst q) + 1 := Finset.mem_range.mp hi
  simp only [FixedWidthQuery.entry, Function.comp_apply, hn, ite_true, FixedWidthQuery.coordinate,
    rankTarget, BinaryNat.normalize_eq_bits, entry]

theorem total_eq_iff (N A W D : List Bool → ℕ) (q : List Bool) :
    total N A W D q = D (pairFst q) ↔
      HomogenizationLayout.weightedSum (N (pairFst q)) (A (pairFst q)) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)) = D (pairFst q) := by
  have he : total N A W D q = ∑ i ∈ Finset.range (N (pairFst q) + 1),
      min (if i < A (pairFst q) + 1 then entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i else 0) (D (pairFst q) + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he, MacaulayBits.sum_min_eq_iff]
  rfl

def oldQuery (W : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.normalize ((rankTarget q).drop (W (pairFst q))))

theorem oldQuery_mem_FP {W : List Bool → ℕ} (hW : UnaryFn W) : oldQuery W ∈ FP := by
  have hd := drop_mem_FP rankTarget_mem_FP (hW.comp pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP (mem_FP_comp hd BinaryNat.normalize_mem_FP)

theorem oldQuery_packet (W : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    oldQuery W (pair c (BinaryNatCode.encode r)) =
      pair c (BinaryNatCode.encode (Nat.fromBitsLE (r.bits.drop (W c)))) := by
  simp only [oldQuery, rankTarget, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
    MacaulayBits.fromBits_encode]
  rfl

def value (N A W D : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if total N A W D q = D (pairFst q) then reader (oldQuery W q) else []

theorem evaluator {N A W D : List Bool → ℕ} (hN : UnaryFn N) (hA : UnaryFn A)
    (hW : UnaryFn W) (hD : UnaryFn D) {reader : List Bool → List Bool} (E : SpaceFunction reader) :
    SpaceFunction (value N A W D reader) := by
  have hg := FPPred.eq (total_unary hN hA hW hD) (hD.comp pairFst_mem_FP)
  have EC := E.precompose (oldQuery W) (oldQuery_mem_FP hW)
  have ES := SpaceFunction.branch (fun q => decide (total N A W D q = D (pairFst q))) hg.flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem value_packet {σ R : Type*} [Fintype σ] [CommSemiring R]
    (N A W D : List Bool → ℕ) (reader : List Bool → List Bool) (c : List Bool)
    (f : σ ≃ Fin (N c)) (p : MvPolynomial σ R) (enc : R → List Bool) (hz : enc 0 = [])
    (hc : ∀ r, reader (pair c (BinaryNatCode.encode r)) = enc (p.coeff (nativeExponent f (W c) r))) (r : ℕ) :
    value N A W D reader (pair c (BinaryNatCode.encode r)) = enc
      ((WeightedHomogenization.homogenize (HomogenizationLayout.prefixWeight f (A c)) (D c) p).coeff
        (nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r)) := by
  have hg := total_eq_iff N A W D (pair c (BinaryNatCode.encode r))
  simp only [pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode] at hg
  rw [value, pairFst_pair, HomogenizationLayout.coefficient_rank]
  by_cases h : HomogenizationLayout.weightedSum (N c) (A c) (W c) r = D c
  · rw [ite_eq_left (hg.mpr h), ite_eq_left h, oldQuery_packet, hc]
  · rw [ite_eq_right (fun hh => h (hg.mp hh)), ite_eq_right h, hz]

/-- Ordinary homogenization uses the full layout, with no application-specific
weight conversion. The coefficient encoding need only send zero to `[]`. -/
theorem value_packet_all {σ R : Type*} [Fintype σ] [CommSemiring R]
    (N W D : List Bool → ℕ) (reader : List Bool → List Bool) (c : List Bool)
    (f : σ ≃ Fin (N c)) (p : MvPolynomial σ R) (enc : R → List Bool) (hz : enc 0 = [])
    (hc : ∀ r, reader (pair c (BinaryNatCode.encode r)) =
      enc (p.coeff (nativeExponent f (W c) r))) (r : ℕ) :
    value N N W D reader (pair c (BinaryNatCode.encode r)) = enc
      ((WeightedHomogenization.homogenize (fun _ => 1) (D c) p).coeff
        (nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r)) := by
  simpa only [HomogenizationLayout.prefixWeight_all] using
    value_packet N N W D reader c f p enc hz hc r

/-- Residue readers inherit ordinary integer homogenization correctness. The
modulus is arbitrary; in particular no field or primality hypothesis is needed. -/
theorem residue_packet_all {σ : Type*} [Fintype σ]
    (N W D : List Bool → ℕ) (reader : List Bool → List Bool) (c : List Bool)
    (f : σ ≃ Fin (N c)) (p : MvPolynomial σ ℤ) (m : ℕ)
    (hc : ∀ r, reader (pair c (BinaryNatCode.encode r)) =
      MatrixPower.residueBits ((p.coeff (nativeExponent f (W c) r) : ℤ) : ZMod m)) (r : ℕ) :
    value N N W D reader (pair c (BinaryNatCode.encode r)) = MatrixPower.residueBits
      ((((WeightedHomogenization.homogenize (fun _ => 1) (D c) p).coeff
        (nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r)) : ℤ) : ZMod m) :=
  value_packet_all N W D reader c f p (fun a : ℤ => MatrixPower.residueBits (a : ZMod m))
    (by simp [MatrixPower.residueBits, BinaryNatCode.encode]) hc r

end LeanCanny.Algebra.HomogenizationBits
