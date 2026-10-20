/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialCoefficient
public import LeanCanny.Algebra.HomogenizationSpace

/-! # Complete readers for spatially filtered coefficient sources

Queries are `pair (pair context spatialRank) fullRank`. A bounded comparison of
spatial exponent blocks guards one suspended original coefficient call. The
selected rank and all source ranks stay binary throughout the computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.PartialCoefficientBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open FixedWidthPolynomial LeanCanny.Encoding.Brackets
open scoped Classical

noncomputable def EqualPrefix (A W : List Bool → ℕ) (left right : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i < A c, FixedWidthQuery.coordinate W left c i = FixedWidthQuery.coordinate W right c i

instance (A W : List Bool → ℕ) (left right : List Bool → List Bool) (c : List Bool) :
    Decidable (EqualPrefix A W left right c) := inferInstanceAs (Decidable (∀ i < A c, _))

theorem equalPrefix_fppred {A W : List Bool → ℕ} {left right : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hl : left ∈ FP) (hr : right ∈ FP) : FPPred (EqualPrefix A W left right) := by
  have hleft := mem_FP_comp MacaulayBits.loopQuery_mem_FP (FixedWidthQuery.read_mem_FP hA hW hl)
  have hright := mem_FP_comp MacaulayBits.loopQuery_mem_FP (FixedWidthQuery.read_mem_FP hA hW hr)
  apply (FPPred.forall_lt hA (stringEq_fppred hleft hright)).of_iff
  intro c
  simp only [Function.comp_apply, MacaulayBits.loopQuery, pairFst_pair, pairSnd_pair,
    List.length_replicate, FixedWidthQuery.read_packet]
  constructor
  · intro h i hi
    have hh := BinaryNatCode.encode_injective (h i hi)
    simpa only [FixedWidthQuery.entry, hi, ite_true] using hh
  · intro h i hi
    apply congrArg BinaryNatCode.encode
    simpa only [FixedWidthQuery.entry, hi, ite_true] using h i hi

def originalContext (q : List Bool) : List Bool := pairFst (pairFst q)
def spatialRank (q : List Bool) : List Bool := BinaryNat.normalize (pairSnd (pairFst q))
def sourceQuery (q : List Bool) : List Bool := pair (originalContext q) (pairSnd q)

theorem originalContext_mem_FP : originalContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

theorem spatialRank_mem_FP : spatialRank ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := mem_FP_pair originalContext_mem_FP pairSnd_mem_FP

noncomputable def Matches (A W : List Bool → ℕ) : List Bool → Prop :=
  EqualPrefix (A ∘ originalContext) (W ∘ originalContext) rankTarget spatialRank

instance (A W : List Bool → ℕ) (q : List Bool) : Decidable (Matches A W q) :=
  inferInstanceAs (Decidable (EqualPrefix _ _ _ _ q))

theorem matches_fppred {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : FPPred (Matches A W) :=
  equalPrefix_fppred (hA.comp originalContext_mem_FP) (hW.comp originalContext_mem_FP)
    rankTarget_mem_FP spatialRank_mem_FP

theorem matches_packet {σ τ : Type*} [Fintype σ] [Fintype τ] (A W : List Bool → ℕ) (c : List Bool)
    {N : ℕ} (f : Sum σ τ ≃ Fin N) (g : σ ≃ Fin (A c))
    (hl : ∀ i, (f (.inl i)).val = (g i).val) (s r : ℕ) :
    Matches A W (pair (pair c (BinaryNatCode.encode s)) (BinaryNatCode.encode r)) ↔
      PartialCoefficient.leftExponent (nativeExponent f (W c) r) = nativeExponent g (W c) s := by
  simp only [Matches, EqualPrefix, originalContext, FixedWidthQuery.coordinate, Function.comp_apply,
    rankTarget, spatialRank, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  constructor
  · intro h
    ext i
    simp only [PartialCoefficient.leftExponent_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, hl, entry]
    exact h (g i).val (g i).isLt
  · intro h i hi
    have hh := congrArg (fun e => e (g.symm ⟨i, hi⟩)) h
    simpa only [PartialCoefficient.leftExponent_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
      hl, Equiv.apply_symm_apply, entry] using hh


theorem matches_context {σ τ : Type*} [Fintype σ] [Fintype τ] (A W : List Bool → ℕ) (c : List Bool)
    {N : ℕ} (f : Sum σ τ ≃ Fin N) (g : σ ≃ Fin (A (pairFst c)))
    (hl : ∀ i, (f (.inl i)).val = (g i).val) (r : ℕ) :
    Matches A W (pair c (BinaryNatCode.encode r)) ↔
      PartialCoefficient.leftExponent (nativeExponent f (W (pairFst c)) r) =
        nativeExponent g (W (pairFst c)) (Nat.fromBitsLE (pairSnd c)) := by
  simp only [Matches, EqualPrefix, originalContext, FixedWidthQuery.coordinate, Function.comp_apply,
    rankTarget, spatialRank, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  constructor
  · intro h
    ext i
    simp only [PartialCoefficient.leftExponent_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, hl, entry]
    exact h (g i).val (g i).isLt
  · intro h i hi
    have hh := congrArg (fun e => e (g.symm ⟨i, hi⟩)) h
    simpa only [PartialCoefficient.leftExponent_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
      hl, Equiv.apply_symm_apply, entry] using hh

def value (A W : List Bool → ℕ) (reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Matches A W q then reader (sourceQuery q) else []

noncomputable def evaluator {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    {reader : List Bool → List Bool} (E : SpaceFunction reader) : SpaceFunction (value A W reader) := by
  have EC := E.precompose sourceQuery sourceQuery_mem_FP
  have ES := SpaceFunction.branch (fun q => decide (Matches A W q)) (matches_fppred hA hW).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem value_packet {σ τ R : Type*} [Fintype σ] [Fintype τ] [CommRing R]
    (A W : List Bool → ℕ) (reader : List Bool → List Bool) (c : List Bool) {N : ℕ}
    (f : Sum σ τ ≃ Fin N) (g : σ ≃ Fin (A c)) (hl : ∀ i, (f (.inl i)).val = (g i).val)
    (p : MvPolynomial (Sum σ τ) R) (enc : R → List Bool) (hz : enc 0 = [])
    (hc : ∀ r, reader (pair c (BinaryNatCode.encode r)) = enc (p.coeff (nativeExponent f (W c) r))) (s r : ℕ) :
    value A W reader (pair (pair c (BinaryNatCode.encode s)) (BinaryNatCode.encode r)) = enc
      (if PartialCoefficient.leftExponent (nativeExponent f (W c) r) = nativeExponent g (W c) s
        then p.coeff (nativeExponent f (W c) r) else 0) := by
  have hm := matches_packet A W c f g hl s r
  rw [value]
  by_cases h : PartialCoefficient.leftExponent (nativeExponent f (W c) r) = nativeExponent g (W c) s
  · rw [ite_eq_left (hm.mpr h), ite_eq_left h]
    simp only [sourceQuery, originalContext, pairFst_pair, pairSnd_pair, hc]
  · rw [ite_eq_right (fun hh => h (hm.mp hh)), ite_eq_right h, hz]

end LeanCanny.Algebra.PartialCoefficientBits
