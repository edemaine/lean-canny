/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ReciprocalEquation
public import LeanCanny.Algebra.HomogenizationSpace

/-! # Space-certified inverse-coordinate coefficient selection

Fixed-width block zero is the reciprocal coordinate. Original rows require
exponent zero; the reciprocal row requires exponent one for its derivative
term, or the zero monomial for its constant -1. Original coefficient routines
are space-bounded children and are queried after removing the first block.
-/

@[expose] public section

namespace LeanCanny.Algebra.ReciprocalBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open FixedWidthPolynomial

def first (W : List Bool → ℕ) (q : List Bool) : List Bool :=
  BinaryNat.normalize ((rankTarget q).take (W (pairFst q)))

theorem first_mem_FP {W : List Bool → ℕ} (hW : UnaryFn W) : first W ∈ FP :=
  mem_FP_comp (take_mem_FP rankTarget_mem_FP (hW.comp pairFst_mem_FP)) BinaryNat.normalize_mem_FP

theorem first_packet (W : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    first W (pair c (BinaryNatCode.encode r)) = BinaryNatCode.encode (entry (W c) r 0) := by
  simp only [first, rankTarget, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
    MacaulayBits.fromBits_encode, entry, Nat.zero_mul, List.drop_zero]
  rfl

def zero (N W : List Bool → ℕ) (q : List Bool) : Prop :=
  FixedWidthQuery.Bounded ((fun c => N c + 1) ∘ pairFst) (W ∘ pairFst) rankTarget (fun _ => 0) q

instance (N W : List Bool → ℕ) (q : List Bool) : Decidable (zero N W q) :=
  inferInstanceAs (Decidable (∀ i < N (pairFst q) + 1,
    FixedWidthQuery.coordinate (W ∘ pairFst) rankTarget q i ≤ 0))

theorem zero_fppred {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) : FPPred (zero N W) :=
  FixedWidthQuery.bounded_fppred ((hN.add (UnaryFn.const 1)).comp pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) (UnaryFn.const 0) rankTarget_mem_FP

theorem zero_packet_iff {σ : Type*} [Fintype σ] (N W : List Bool → ℕ) (c : List Bool)
    (f : σ ≃ Fin (N c)) (r : ℕ) : zero N W (pair c (BinaryNatCode.encode r)) ↔
      nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r = 0 := by
  have hc (i : ℕ) : FixedWidthQuery.coordinate (W ∘ pairFst) rankTarget
      (pair c (BinaryNatCode.encode r)) i = entry (W c) r i := by
    simp only [FixedWidthQuery.coordinate, rankTarget, Function.comp_apply, pairFst_pair,
      pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, entry]
  simp only [zero, FixedWidthQuery.Bounded, Function.comp_apply, pairFst_pair]
  constructor
  · intro h
    ext i
    have hh := h (HomogenizationLayout.variableEquiv f i).val (HomogenizationLayout.variableEquiv f i).isLt
    rw [hc] at hh
    exact Nat.eq_zero_of_le_zero hh
  · intro h i hi
    rw [hc]
    have hh := congrArg (fun m : Option σ →₀ ℕ => m ((HomogenizationLayout.variableEquiv f).symm ⟨i, hi⟩)) h
    have he : entry (W c) r i = 0 := by
      simpa only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.apply_symm_apply, Finsupp.zero_apply] using hh
    exact he.le

def embeddedValue (W : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if first W q = [] then reader (HomogenizationBits.oldQuery W q) else []

theorem embeddedEvaluator {W : List Bool → ℕ} (hW : UnaryFn W)
    {reader : List Bool → List Bool} (E : SpaceFunction reader) : SpaceFunction (embeddedValue W reader) := by
  have EP := E.precompose (HomogenizationBits.oldQuery W) (HomogenizationBits.oldQuery_mem_FP hW)
  have ES := SpaceFunction.branch (fun q => decide (first W q = []))
    (stringEq_fppred (first_mem_FP hW) (constFn_mem_FP [])).flag_mem_FP EP (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q => by simp only [embeddedValue, decide_eq_true_eq, Function.comp_apply])

def inverseValue (N W : List Bool → ℕ) (reader negativeOne : List Bool → List Bool) (q : List Bool) : List Bool :=
  if first W q = [true] then reader (HomogenizationBits.oldQuery W q)
  else if zero N W q then negativeOne (pairFst q) else []

theorem inverseEvaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    {reader negativeOne : List Bool → List Bool} (E : SpaceFunction reader) (hn : negativeOne ∈ FP) :
    SpaceFunction (inverseValue N W reader negativeOne) := by
  have EP := E.precompose (HomogenizationBits.oldQuery W) (HomogenizationBits.oldQuery_mem_FP hW)
  have EZ := SpaceFunction.branch (fun q => decide (zero N W q)) (zero_fppred hN hW).flag_mem_FP
    (SpaceFunction.ofFP _ (mem_FP_comp pairFst_mem_FP hn)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have ES := SpaceFunction.branch (fun q => decide (first W q = [true]))
    (stringEq_fppred (first_mem_FP hW) (constFn_mem_FP [true])).flag_mem_FP EP EZ
  exact ES.congr (funext fun q => by simp only [inverseValue, decide_eq_true_eq, Function.comp_apply])

theorem first_native_packet {σ : Type*} [Fintype σ] (N W : List Bool → ℕ) (c : List Bool)
    (f : σ ≃ Fin (N c)) (r : ℕ) : first W (pair c (BinaryNatCode.encode r)) =
      BinaryNatCode.encode ((nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r) none) := by
  rw [first_packet]
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, HomogenizationLayout.variableEquiv_none]

theorem embedded_packet {σ R : Type*} [Fintype σ] [CommRing R] (N W : List Bool → ℕ)
    (reader : List Bool → List Bool) (c : List Bool) (f : σ ≃ Fin (N c)) (p : MvPolynomial σ R)
    (enc : R → List Bool) (hz : enc 0 = [])
    (hc : ∀ k, reader (pair c (BinaryNatCode.encode k)) = enc (p.coeff (nativeExponent f (W c) k))) (r : ℕ) :
    embeddedValue W reader (pair c (BinaryNatCode.encode r)) = enc
      ((MvPolynomial.rename some p).coeff (nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r)) := by
  let m := nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r
  have hf : first W (pair c (BinaryNatCode.encode r)) = [] ↔ m none = 0 := by
    rw [first_native_packet N W c f r]
    change BinaryNatCode.encode (m none) = BinaryNatCode.encode 0 ↔ _
    exact BinaryNatCode.encode_injective.eq_iff
  rw [embeddedValue, ReciprocalEquation.coefficient_rename]
  by_cases h : m none = 0
  · rw [ite_eq_left (hf.mpr h), ite_eq_left h, HomogenizationBits.oldQuery_packet, hc,
      HomogenizationLayout.native_some]
  · rw [ite_eq_right (fun hh => h (hf.mp hh)), ite_eq_right h, hz]

theorem inverse_packet {σ R : Type*} [Fintype σ] [CommRing R] (N W : List Bool → ℕ)
    (reader negativeOne : List Bool → List Bool) (c : List Bool) (f : σ ≃ Fin (N c))
    (p : MvPolynomial σ R) (base : σ) (enc : R → List Bool) (hz : enc 0 = []) (hn : negativeOne c = enc (-1))
    (hc : ∀ k, reader (pair c (BinaryNatCode.encode k)) = enc ((MvPolynomial.pderiv base p).coeff (nativeExponent f (W c) k))) (r : ℕ) :
    inverseValue N W reader negativeOne (pair c (BinaryNatCode.encode r)) = enc
      ((ReciprocalEquation.polynomial p base).coeff (nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r)) := by
  let m := nativeExponent (HomogenizationLayout.variableEquiv f) (W c) r
  have hf : first W (pair c (BinaryNatCode.encode r)) = [true] ↔ m none = 1 := by
    rw [first_native_packet N W c f r]
    change BinaryNatCode.encode (m none) = BinaryNatCode.encode 1 ↔ _
    exact BinaryNatCode.encode_injective.eq_iff
  have hzero := zero_packet_iff N W c f r
  rw [inverseValue, ReciprocalEquation.coefficient_branch]
  by_cases h : m none = 1
  · rw [ite_eq_left (hf.mpr h), ite_eq_left h, HomogenizationBits.oldQuery_packet, hc,
      HomogenizationLayout.native_some]
  · rw [ite_eq_right (fun hh => h (hf.mp hh)), ite_eq_right h]
    by_cases he : m = 0
    · rw [ite_eq_left (hzero.mpr he), ite_eq_left he, pairFst_pair, hn]
    · rw [ite_eq_right (fun hh => he (hzero.mp hh)), ite_eq_right he, hz]

end LeanCanny.Algebra.ReciprocalBits
