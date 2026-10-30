/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQueryProductSpace
public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Canonical modular readers for indexed integer polynomial products

The factor count stays binary, and the original indexed coefficient routine
may use polynomial space. Empty products and arbitrary raw coefficient
indices use the same streamed polynomial product backend.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialFamilyProductBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree)
open scoped Classical BigOperators

noncomputable def polynomial (p : List Bool → ℤ[X]) (N : List Bool → ℕ) (c : List Bool) : ℤ[X] :=
  ∏ i ∈ Finset.range (N c), p (pair c (BinaryNatCode.encode i))

def factorQuery (r : List Bool) : List Bool :=
  pair (pair (pair (context (pairFst r)) (pairFst (pairSnd r))) (pairSnd (pairSnd r))) (pairSnd (pairFst r))

theorem factorQuery_FP : factorQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP RationalSubstitution.IntegerBits.context_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hk := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc hi) hk) hm

def reindexQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (context q)) (selectedDegree q)) (pairSnd q)

theorem reindexQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : reindexQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hf)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem reindexEvaluator {p : List Bool → ℤ[X]} (P : SpaceFunction (PrimitivePairBits.coefficient p))
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    SpaceFunction (PrimitivePairBits.coefficient (p ∘ f)) := by
  refine (P.precompose (reindexQuery f) (reindexQuery_FP hf)).congr (funext fun q => ?_)
  simp only [Function.comp_apply, reindexQuery, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair]

set_option maxHeartbeats 200000 in
theorem evaluator (p : List Bool → ℤ[X]) (N : List Bool → ℕ) (hN : BinaryFn N)
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p N)) := by
  let count := fun q => BinaryNatCode.encode (N (context q))
  let Q := fun q i => (p (pair (context q) (BinaryNatCode.encode i))).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
  have hQ (q : List Bool) (i k : ℕ) :
      (PrimitivePairBits.coefficient p ∘ factorQuery)
        (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
        residueBits ((Q q i).coeff k) := by
    change RationalSubstitution.IntegerBits.coefficientResidue
      ((p (context (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))))).coeff
        (Nat.fromBitsLE (selectedDegree (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))))))
      (RationalSubstitution.IntegerBits.mValue (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))) = _
    have hc : context (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))) =
        pair (context q) (BinaryNatCode.encode i) := by
      simp only [factorQuery, context, pairFst_pair, pairSnd_pair]
    have hk : Nat.fromBitsLE (selectedDegree (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))) = k := by
      simp only [factorQuery, selectedDegree, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have hm : RationalSubstitution.IntegerBits.mValue (factorQuery (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))) =
        Nat.fromBitsLE (pairSnd q) + 1 := by
      simp only [factorQuery, RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair]
    calc
      _ = RationalSubstitution.IntegerBits.coefficientResidue
          ((p (pair (context q) (BinaryNatCode.encode i))).coeff k) (Nat.fromBitsLE (pairSnd q) + 1) :=
        congrArg₂ RationalSubstitution.IntegerBits.coefficientResidue (by rw [hc, hk]) hm
      _ = _ := by dsimp only [Q]; rw [Polynomial.coeff_map]; rfl
  have E := RootSignQueries.queryProductEvaluator (P.precompose factorQuery factorQuery_FP)
    count (fun _ => [true]) pairSnd selectedDegree
    (BinaryFn.bits_mem_FP (hN.comp RationalSubstitution.IntegerBits.context_mem_FP))
    (constFn_mem_FP [true]) pairSnd_mem_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP
    (fun _ _ => (⟨1, by decide⟩ : Fin 3)) Q (by intro _ _ _; rfl) (fun q i _ k => hQ q i k)
  refine E.congr (funext fun q => ?_)
  simp only [RootSignQueries.queryProductValue, count, BinaryNatCode.encode, Nat.fromBitsLE_bits, pow_one, Q]
  rw [← Polynomial.map_prod, Polynomial.coeff_map]
  change residueBits ((Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    ((polynomial p N (context q)).coeff (Nat.fromBitsLE (selectedDegree q)))) = _
  rfl

theorem ne_zero (p : List Bool → ℤ[X]) (N : List Bool → ℕ)
    (hp : ∀ c, p c ≠ 0) (c : List Bool) : polynomial p N c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _i _ => hp _)

theorem degree_le (p : List Bool → ℤ[X]) (N D : List Bool → ℕ)
    (hd : ∀ c i, (p (pair c (BinaryNatCode.encode i))).natDegree ≤ D c) (c : List Bool) :
    (polynomial p N c).natDegree ≤ N c * D c := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  exact (Finset.sum_le_sum (fun i _ => hd c i)).trans_eq (by simp)

theorem mass_le (p : List Bool → ℤ[X]) (N b : List Bool → ℕ)
    (hm : ∀ c i, coefficientMass (p (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c) (c : List Bool) :
    coefficientMass (polynomial p N c) ≤ 2 ^ (N c * b c) := by
  apply (coefficientMass_prod_le _ _).trans
  calc
    (∏ i ∈ Finset.range (N c), coefficientMass (p (pair c (BinaryNatCode.encode i)))) ≤
        ∏ _i ∈ Finset.range (N c), 2 ^ b c := Finset.prod_le_prod (fun i _ => hm c i)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

noncomputable def budget (N b : List Bool → ℕ) (c : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (N c), b (pair c (BinaryNatCode.encode i))

theorem budget_binary {N b : List Bool → ℕ} (hN : UnaryFn N) (hb : BinaryFn b) : BinaryFn (budget N b) := by
  let f := fun r => pair (pairFst r) (BinaryNatCode.encode (pairSnd r).length)
  have hf : f ∈ FP := mem_FP_pair pairFst_mem_FP (bits_mem_FP UnaryFn.index)
  exact (BinaryFn.sum hN (hb.comp hf)).of_eq (fun c => by
    simp only [Function.comp_apply, f, budget, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem degree_le_budget (p : List Bool → ℤ[X]) (N D : List Bool → ℕ)
    (hd : ∀ r, (p r).natDegree ≤ D r) (c : List Bool) :
    (polynomial p N c).natDegree ≤ budget N D c :=
  (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun _i _ => hd _))

theorem mass_le_budget (p : List Bool → ℤ[X]) (N b : List Bool → ℕ)
    (hm : ∀ r, coefficientMass (p r) ≤ 2 ^ b r) (c : List Bool) :
    coefficientMass (polynomial p N c) ≤ 2 ^ budget N b c := by
  apply (coefficientMass_prod_le _ _).trans
  exact (Finset.prod_le_prod (fun _i _ => hm _)).trans_eq (by
    unfold budget
    rw [Finset.prod_pow_eq_pow_sum])

end LeanCanny.Algebra.PolynomialFamilyProductBits
