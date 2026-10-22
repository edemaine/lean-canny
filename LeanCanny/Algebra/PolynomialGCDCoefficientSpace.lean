/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientFormSpace
public import LeanCanny.Algebra.PolynomialGCDDegreeSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-! # GCD coefficients with a space-computed subresultant order

The GCD degree is retained in a prepared coefficient request. The subsequent
determinant evaluator sees only FP projections of that request. Queries use the
same context/modulus/index format as the original integer coefficient readers.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialGCDBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open PrincipalCoefficientBits (integerResidue)
attribute [local irreducible] BinaryNat.normalize

def context (q : List Bool) : List Bool := pairFst (pairFst q)

theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def prepare (z : List Bool) : List Bool :=
  pair (pair (context (pairFst z)) (pair (pairSnd z) (BinaryNat.normalize (pairSnd (pairFst z)))))
    (BinaryNat.normalize (pairSnd (pairFst (pairFst z))))

theorem prepare_FP : prepare ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP context_FP
  have hk := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have hm := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hc (mem_FP_pair pairSnd_mem_FP hk)) hm

noncomputable def orderValue (F : Resultant.Family) (d : List Bool → ℕ) (q : List Bool) : List Bool :=
  integerResidue ((PrincipalSubresultant.coefficientForm (F.left (context q)) (F.right (context q))
    (F.leftDegree (context q)) (F.rightDegree (context q)) (d (context q))).coeff (Nat.fromBitsLE (pairSnd q)))
    (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)

theorem withOrderEvaluator {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.leftCoefficient) (Q : SpaceFunction a.bits.rightCoefficient)
    (d : List Bool → ℕ) (D : SpaceFunction (fun c => BinaryNatCode.encode (d c)))
    (hd : ∀ c, d c ≤ min (F.leftDegree c) (F.rightDegree c)) : SpaceFunction (orderValue F d) := by
  have R := ((D.precompose context context_FP).withInput.postcompose prepare prepare_FP).chain
    (CoefficientFormBits.evaluator a ha P Q)
  refine R.congr (funext fun q => ?_)
  simp only [Function.comp_apply, prepare, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
  have h := CoefficientFormBits.packet F (context q) (d (context q))
    (Nat.fromBitsLE (pairSnd q)) (Nat.fromBitsLE (pairSnd (pairFst q))) (hd (context q))
  change CoefficientFormBits.value F _ = _ at h
  exact h

noncomputable def value (F : Resultant.Family) (q : List Bool) : List Bool :=
  integerResidue ((representative (F.left (context q)) (F.right (context q))).coeff (Nat.fromBitsLE (pairSnd q)))
    (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)

theorem representativeEvaluator {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.leftCoefficient) (Q : SpaceFunction a.bits.rightCoefficient)
    (hm : ∀ c, F.leftDegree c = (F.left c).natDegree) (hn : ∀ c, F.rightDegree c = (F.right c).natDegree)
    (hq : ∀ c, F.right c ≠ 0) (hlt : ∀ c, (F.right c).natDegree < (F.left c).natDegree) :
    SpaceFunction (value F) := by
  have hd (c : List Bool) : degree (F.left c) (F.right c) ≤ min (F.leftDegree c) (F.rightDegree c) := by
    have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hq' : (F.right c).map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr (hq c)
    have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right
      ((F.left c).map (Int.castRingHom ℚ)) ((F.right c).map (Int.castRingHom ℚ))) hq'
    have hn' : degree (F.left c) (F.right c) ≤ (F.right c).natDegree := by
      simpa only [degree, natDegree_map_eq_of_injective hi] using h
    exact Nat.le_min.mpr ⟨by rw [hm]; exact hn'.trans (hlt c).le, by rw [hn]; exact hn'⟩
  have E := withOrderEvaluator a ha P Q (fun c => degree (F.left c) (F.right c))
    (degreeEvaluator a ha P Q hm hn hq hlt) hd
  exact E.congr (funext fun q => by simp only [orderValue, value, representative, hm, hn])

end LeanCanny.Algebra.PolynomialGCDBits
