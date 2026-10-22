/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveQueryReaders
public import LeanCanny.Computation.PolyTimeRange

/-! # Native FP coefficients of sparse coercive query terms -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSparseReaders
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveQueryReaders
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

noncomputable def Matches (input target : List Bool → List Bool) (parameter power selected : List Bool → ℕ)
    (c : List Bool) : Prop := ∀ j < dimension (input c) + 1,
  FixedWidthQuery.coordinate (CoercivePowerReaders.width ∘ input) target c j =
    if j = 0 then parameter c else if j = selected c + 1 then power c else 0

theorem matches_fppred {input target : List Bool → List Bool} {parameter power selected : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hp : UnaryFn parameter) (hN : UnaryFn power) (hs : UnaryFn selected) :
    FPPred (Matches input target parameter power selected) := by
  have hw := (CoercivePowerReaders.width_unary.comp hi).lift
  have hread := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hw)) hw
  have hpat := UnaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) hp.lift
    (UnaryFn.ite (FPPred.eq UnaryFn.index ((hs.add (UnaryFn.const 1)).lift)) hN.lift (UnaryFn.const 0))
  have hcmp := (BinaryNat.le_fppred hread (bits_mem_FP hpat)).and (BinaryNat.le_fppred (bits_mem_FP hpat) hread)
  have heq : FPPred (fun q => FixedWidthQuery.coordinate (CoercivePowerReaders.width ∘ input) target
      (pairFst q) (pairSnd q).length =
      if (pairSnd q).length = 0 then parameter (pairFst q)
      else if (pairSnd q).length = selected (pairFst q) + 1 then power (pairFst q) else 0) := by
    apply hcmp.of_iff
    intro q
    simp only [Function.comp_apply, Nat.fromBitsLE_bits, FixedWidthQuery.coordinate]
    exact le_antisymm_iff.symm
  apply (FPPred.forall_lt ((dimension_unary.comp hi).add (UnaryFn.const 1)) heq).of_iff
  intro c
  simp only [Matches, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem matches_iff (input target : List Bool → List Bool) (parameter power selected : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hs : selected c = i.val) :
    Matches input target parameter power selected c ↔
      queryExponent input target c = Finsupp.single 0 (parameter c) + Finsupp.single i.succ (power c) := by
  have hsingle (j : Fin (dimension (input c) + 1)) :
      (Finsupp.single (0 : Fin (dimension (input c) + 1)) (parameter c) + Finsupp.single i.succ (power c)) j =
        if j.val = 0 then parameter c else if j.val = i.val + 1 then power c else 0 := by
    simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
    split_ifs <;> omega
  constructor
  · intro h
    ext j
    rw [hsingle]
    simpa only [queryExponent, Finsupp.coe_equivFunOnFinite_symm, hs] using h j.val j.isLt
  · intro h j hj
    have hh := congrArg (fun e : Fin (dimension (input c) + 1) →₀ ℕ => e ⟨j, hj⟩) h
    rw [hsingle] at hh
    simpa only [queryExponent, Finsupp.coe_equivFunOnFinite_symm, hs] using hh

/-- Natural sparse coefficients, with one term per point coordinate. -/
noncomputable def penaltyCoefficient (input target : List Bool → List Bool) (c : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (dimension (input c)),
    if Matches input target (fun _ => 0) (fun c => 2 * degreeAllowance (input c) + 2) (fun _ => i) c then 1 else 0

theorem penaltyCoefficient_unary {input target : List Bool → List Bool} (hi : input ∈ FP) (ht : target ∈ FP) :
    UnaryFn (penaltyCoefficient input target) := by
  have hm := matches_fppred (mem_FP_comp pairFst_mem_FP hi) (mem_FP_comp pairFst_mem_FP ht)
    (UnaryFn.const 0) (((UnaryFn.const 2).mul (degreeAllowance_unary.comp (mem_FP_comp pairFst_mem_FP hi))).add (UnaryFn.const 2))
    UnaryFn.index
  have h := (dimension_unary.comp hi).sum (UnaryFn.ite hm (UnaryFn.const 1) (UnaryFn.const 0))
  apply h.of_eq
  intro c
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matches, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, FixedWidthQuery.coordinate]

theorem penaltyCoefficient_eq (input target : List Bool → List Bool) (c : List Bool) :
    (penaltyCoefficient input target c : ℤ) =
      (CoerciveQuerySystem.penalty (n := dimension (input c)) (degreeAllowance (input c))).coeff
        (queryExponent input target c) := by
  rw [penaltyCoefficient, Nat.cast_sum, CoerciveQuerySystem.penalty, MvPolynomial.coeff_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  rw [matches_iff input target _ _ _ c i rfl]
  simp only [Finsupp.single_zero, zero_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [eq_comm]

noncomputable def penaltyValue (input target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((penaltyCoefficient input target c : ℕ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem penaltyValue_FP {input target modulus : List Bool → List Bool}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : penaltyValue input target modulus ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (bits_mem_FP (penaltyCoefficient_unary hi ht))
    (mem_FP_comp hm BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    penaltyValue, residueBits, ZMod.val_natCast, BinaryNatCode.encode]

theorem penalty_value_eq (input target modulus : List Bool → List Bool) (c : List Bool) :
    penaltyValue input target modulus c = residueBits
      (((CoerciveQuerySystem.penalty (n := dimension (input c)) (degreeAllowance (input c))).coeff
        (queryExponent input target c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [← penaltyCoefficient_eq]
  simp only [penaltyValue, Int.cast_natCast]

noncomputable def monomialValue (input target modulus : List Bool → List Bool)
    (parameter power selected factor : List Bool → ℕ) (c : List Bool) : List Bool :=
  residueBits ((if Matches input target parameter power selected c then factor c else 0 : ℕ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem monomialValue_FP {input target modulus : List Bool → List Bool}
    {parameter power selected factor : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (hp : UnaryFn parameter) (hN : UnaryFn power) (hs : UnaryFn selected) (hf : UnaryFn factor) :
    monomialValue input target modulus parameter power selected factor ∈ FP := by
  have hnat := UnaryFn.ite (matches_fppred hi ht hp hN hs) hf (UnaryFn.const 0)
  have h := mem_FP_comp (mem_FP_pair (bits_mem_FP hnat)
    (mem_FP_comp hm BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
    monomialValue, residueBits, ZMod.val_natCast, BinaryNatCode.encode]

theorem monomial_value_eq (input target modulus : List Bool → List Bool)
    (parameter power selected factor : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hs : selected c = i.val) :
    monomialValue input target modulus parameter power selected factor c = residueBits
      (((MvPolynomial.monomial (Finsupp.single 0 (parameter c) + Finsupp.single i.succ (power c))
          (factor c : ℤ)).coeff (queryExponent input target c) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [MvPolynomial.coeff_monomial]
  unfold monomialValue
  rw [matches_iff input target parameter power selected c i hs]
  split_ifs <;> simp_all [eq_comm]

theorem matches_parameter_iff (input target : List Bool → List Bool) (parameter : List Bool → ℕ)
    (c : List Bool) : Matches input target parameter (fun _ => 0) (fun _ => 0) c ↔
      queryExponent input target c = Finsupp.single 0 (parameter c) := by
  constructor
  · intro h
    ext j
    have hh := h j.val j.isLt
    simpa only [queryExponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, ite_self, eq_comm] using hh
  · intro h j hj
    have hh := congrArg (fun e : Fin (dimension (input c) + 1) →₀ ℕ => e ⟨j, hj⟩) h
    simpa only [queryExponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, ite_self, eq_comm] using hh

end LeanCanny.ETR.CoerciveSparseReaders
