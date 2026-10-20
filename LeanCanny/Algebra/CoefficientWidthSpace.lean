/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationSpace

/-! # Changing exponent widths in certified coefficient queries

An exponent exceeding the source's degree allowance must return zero. Otherwise
repacking preserves every coordinate exactly. The bounded guard is essential:
truncation alone can turn an oversized exponent into a supported monomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoefficientWidthBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open FixedWidthPolynomial

noncomputable def Fits (A W D : List Bool → ℕ) : List Bool → Prop :=
  FixedWidthQuery.Bounded (A ∘ pairFst) (W ∘ pairFst) rankTarget (D ∘ pairFst)

instance (A W D : List Bool → ℕ) (q : List Bool) : Decidable (Fits A W D q) :=
  inferInstanceAs (Decidable (∀ i < A (pairFst q), FixedWidthQuery.coordinate (W ∘ pairFst) rankTarget q i ≤ D (pairFst q)))

theorem fits_fppred {A W D : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) (hD : UnaryFn D) : FPPred (Fits A W D) :=
  FixedWidthQuery.bounded_fppred (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) (hD.comp pairFst_mem_FP) rankTarget_mem_FP

def packed (A W V : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.repack (A ∘ pairFst) (W ∘ pairFst) (A ∘ pairFst) (V ∘ pairFst) rankTarget

theorem packed_mem_FP {A W V : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) : packed A W V ∈ FP :=
  FixedWidthQuery.repack_mem_FP (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (hA.comp pairFst_mem_FP) (hV.comp pairFst_mem_FP) rankTarget_mem_FP

def sourceQuery (A W V : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.normalize (packed A W V q))

theorem sourceQuery_mem_FP {A W V : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) :
    sourceQuery A W V ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp (packed_mem_FP hA hW hV) BinaryNat.normalize_mem_FP)

theorem fits_packet (A W D : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    Fits A W D (pair c (BinaryNatCode.encode r)) ↔ ∀ i < A c, entry (W c) r i ≤ D c := by
  simp only [Fits, FixedWidthQuery.Bounded, Function.comp_apply, pairFst_pair, FixedWidthQuery.coordinate,
    rankTarget, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, entry]

theorem packed_packet (A W V : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    packed A W V (pair c (BinaryNatCode.encode r)) = FixedWidthNatVector.encode (A c) (V c)
      (fun i => if i < A c then entry (W c) r i else 0) := by
  simp only [packed, FixedWidthQuery.repack, Function.comp_apply, pairFst_pair]
  apply congrArg (FixedWidthNatVector.encode (A c) (V c))
  funext i
  simp only [FixedWidthQuery.entry, Function.comp_apply, pairFst_pair, FixedWidthQuery.coordinate,
    rankTarget, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, entry]

theorem sourceQuery_packet (A W V : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    sourceQuery A W V (pair c (BinaryNatCode.encode r)) =
      pair c (BinaryNatCode.encode (Nat.fromBitsLE (packed A W V (pair c (BinaryNatCode.encode r))))) := by
  simp only [sourceQuery, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem native_packed {σ : Type*} [Fintype σ] (A W V D : List Bool → ℕ) (c : List Bool)
    (f : σ ≃ Fin (A c)) (r : ℕ) (hf : Fits A W D (pair c (BinaryNatCode.encode r))) (hV : D c < 2 ^ V c) :
    nativeExponent f (V c) (Nat.fromBitsLE (packed A W V (pair c (BinaryNatCode.encode r)))) = nativeExponent f (W c) r := by
  rw [packed_packet]
  ext i
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm]
  have hi := (f i).isLt
  have hb : (if (f i).val < A c then entry (W c) r (f i).val else 0) < 2 ^ V c := by
    rw [ite_eq_left hi]
    exact ((fits_packet A W D c r).mp hf (f i).val hi).trans_lt hV
  rw [MacaulayBits.entry_encoded_vector _ _ _ (f i).val hi hb, ite_eq_left hi]


theorem exists_native_rank {σ : Type*} [Fintype σ] (A W : ℕ) (f : σ ≃ Fin A) (m : σ →₀ ℕ)
    (hm : ∀ i, m i < 2 ^ W) : ∃ r, nativeExponent f W r = m := by
  let e := m.mapDomain f
  have he : ∀ i, e i < 2 ^ W := by
    intro i
    simpa only [e, Finsupp.mapDomain_equiv_apply] using hm (f.symm i)
  let r := FixedWidthPolynomial.index A W e he
  refine ⟨r.val, ?_⟩
  apply Finsupp.mapDomain_injective f.injective
  rw [nativeExponent_map, FixedWidthPolynomial.entry_vector]
  exact FixedWidthPolynomial.vector_index A W e he

def value (A W V D : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Fits A W D q then reader (sourceQuery A W V q) else []

noncomputable def evaluator {A W V D : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : UnaryFn D)
    {reader : List Bool → List Bool} (E : SpaceFunction reader) : SpaceFunction (value A W V D reader) := by
  have EC := E.precompose (sourceQuery A W V) (sourceQuery_mem_FP hA hW hV)
  have ES := SpaceFunction.branch (fun q => decide (Fits A W D q)) (fits_fppred hA hW hD).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem value_packet {σ R : Type*} [Fintype σ] [CommSemiring R] (A W V D : List Bool → ℕ)
    (reader : List Bool → List Bool) (c : List Bool) (f : σ ≃ Fin (A c)) (p : MvPolynomial σ R)
    (enc : R → List Bool) (hz : enc 0 = []) (hV : D c < 2 ^ V c)
    (hp : ∀ m ∈ p.support, ∀ i, m i ≤ D c)
    (hc : ∀ r, reader (pair c (BinaryNatCode.encode r)) = enc (p.coeff (nativeExponent f (V c) r))) (r : ℕ) :
    value A W V D reader (pair c (BinaryNatCode.encode r)) = enc (p.coeff (nativeExponent f (W c) r)) := by
  rw [value]
  by_cases hf : Fits A W D (pair c (BinaryNatCode.encode r))
  · rw [ite_eq_left hf, sourceQuery_packet, hc, native_packed A W V D c f r hf hV]
  · rw [ite_eq_right hf]
    have hz' : p.coeff (nativeExponent f (W c) r) = 0 := by
      by_contra hn
      apply hf
      apply (fits_packet A W D c r).mpr
      intro i hi
      have he := hp (nativeExponent f (W c) r) (MvPolynomial.mem_support_iff.mpr hn) (f.symm ⟨i, hi⟩)
      simpa only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.apply_symm_apply] using he
    rw [hz', hz]

end LeanCanny.Algebra.CoefficientWidthBits
