/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGCDData
public import LeanCanny.Algebra.PrincipalCoefficientSpace
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Computation.PSPACEClosure

/-! # Computing the degree of an integer-polynomial GCD over the rationals

Scan principal subresultants in descending order and retain the last nonzero
index. Only binary indices and original coefficient readers are needed. The
coefficient readers may use arbitrary time in polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

theorem zeroDecider {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) : SpaceDecider {r | coefficient F r = 0} := by
  apply IntegerZeroBits.zeroDecider (residueEvaluator a ha P Q) (budgetCode a) (budgetCode_mem_FP a ha)
    (coefficient F)
  · intro r
    rw [budgetCode_eq, show Nat.fromBitsLE (BinaryNatCode.encode (budget F r)) = budget F r from Nat.fromBitsLE_bits _]
    exact coefficient_size F r
  · intro r m hm
    rw [residueValue_eq]
    simp only [pairFst_pair, modulus, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rfl

theorem nonzeroDecider {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) : SpaceDecider {r | coefficient F r ≠ 0} := by
  have E := (zeroDecider a ha P Q).flagEvaluator
  refine E.decider (fun b => !(b[0]?.getD false)) ?_ ?_
  · simpa using (FPPred.getBit id_mem_FP (UnaryFn.const 0)).not.flag_mem_FP
  · intro r
    simp only [List.getElem?_cons_zero, Option.getD_some, Bool.not_eq_true', decide_eq_false_iff_not]
    rfl

end LeanCanny.Algebra.PrincipalCoefficientBits

namespace LeanCanny.Algebra.PolynomialGCDBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation PrincipalSubresultant
open scoped Classical
attribute [local irreducible] BinaryNat.sub

def reverseQuery {F : Resultant.Family} (a : Resultant.Access F) (r : List Bool) : List Bool :=
  pair (pairFst r) (BinaryNat.sub (pair (a.bits.rightDegree (pairFst r)) (pairSnd r)))

theorem reverseQuery_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    reverseQuery a ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP ha.rightDegree) pairSnd_mem_FP) BinaryNat.sub_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem reverseQuery_packet {F : Resultant.Family} (a : Resultant.Access F) (c : List Bool) (k : ℕ) :
    reverseQuery a (pair c (BinaryNatCode.encode k)) = pair c (BinaryNatCode.encode (F.rightDegree c - k)) := by
  simp only [reverseQuery, pairFst_pair, pairSnd_pair, a.rightDegree,
    BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def reverseLanguage {F : Resultant.Family} (a : Resultant.Access F) : Language :=
  {r | PrincipalCoefficientBits.coefficient F (reverseQuery a r) ≠ 0}

noncomputable def scanDegree {F : Resultant.Family} (a : Resultant.Access F) (c : List Bool) : ℕ :=
  F.rightDegree c - (BoundedChoice.search (reverseLanguage a) c (F.rightDegree c + 1) - 1)

theorem coefficient_nonzero_iff {F : Resultant.Family} (c : List Bool) (k : ℕ)
    (hk : k ≤ min (F.leftDegree c) (F.rightDegree c)) :
    PrincipalCoefficientBits.coefficient F (pair c (BinaryNatCode.encode k)) ≠ 0 ↔
      psc ((F.left c).map (Int.castRingHom ℚ)) ((F.right c).map (Int.castRingHom ℚ))
        (F.leftDegree c) (F.rightDegree c) k ≠ 0 := by
  change signedPsc (F.left (pairFst (pair c (BinaryNatCode.encode k))))
    (F.right (pairFst (pair c (BinaryNatCode.encode k)))) (F.leftDegree (pairFst (pair c (BinaryNatCode.encode k))))
    (F.rightDegree (pairFst (pair c (BinaryNatCode.encode k))))
    (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k)))) ≠ 0 ↔ _
  rw [pairFst_pair, pairSnd_pair, show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k,
    signedPsc_of_le _ _ hk, psc_map_map]
  have hs : (-1 : ℤ) ^ (F.leftDegree c - k).choose 2 ≠ 0 := pow_ne_zero _ (by decide)
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [Ne, Ne, map_eq_zero_iff _ hi, mul_eq_zero]
  tauto

theorem scanDegree_eq {F : Resultant.Family} (a : Resultant.Access F) (c : List Bool)
    (hm : F.leftDegree c = (F.left c).natDegree) (hn : F.rightDegree c = (F.right c).natDegree)
    (hq : F.right c ≠ 0) (hlt : (F.right c).natDegree < (F.left c).natDegree) :
    scanDegree a c = degree (F.left c) (F.right c) := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hq' : (F.right c).map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hq
  have hlt' : ((F.right c).map (Int.castRingHom ℚ)).natDegree < ((F.left c).map (Int.castRingHom ℚ)).natDegree := by
    simpa only [natDegree_map_eq_of_injective hi] using hlt
  obtain ⟨_, hnonzero, hzero⟩ := gcd_data _ _ hq' hlt'
  have hd : degree (F.left c) (F.right c) ≤ F.rightDegree c := by
    have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right
      ((F.left c).map (Int.castRingHom ℚ)) ((F.right c).map (Int.castRingHom ℚ))) hq'
    simpa only [degree, natDegree_map_eq_of_injective hi, hn] using h
  have hpacket (j : ℕ) (hj : j ≤ F.rightDegree c) :
      pair c (BinaryNatCode.encode j) ∈ reverseLanguage a ↔
        psc ((F.left c).map (Int.castRingHom ℚ)) ((F.right c).map (Int.castRingHom ℚ))
          (F.left c).natDegree (F.right c).natDegree (F.rightDegree c - j) ≠ 0 := by
    change PrincipalCoefficientBits.coefficient F (reverseQuery a (pair c (BinaryNatCode.encode j))) ≠ 0 ↔ _
    rw [reverseQuery_packet, coefficient_nonzero_iff c _ (by omega), hm, hn]
  have hlast := BoundedChoice.search_of_last (reverseLanguage a) c (F.rightDegree c + 1)
    (F.rightDegree c - degree (F.left c) (F.right c)) (by omega)
    ((hpacket _ (by omega)).mpr (by
      have he : F.rightDegree c - (F.rightDegree c - degree (F.left c) (F.right c)) = degree (F.left c) (F.right c) := by omega
      rw [he]
      simpa only [degree, natDegree_map_eq_of_injective hi] using hnonzero)) (by
        intro j hj hjn hmemb
        have hz := hzero (F.rightDegree c - j) (by change F.rightDegree c - j < degree (F.left c) (F.right c); omega)
        have hmemb' := (hpacket j (by omega)).mp hmemb
        exact hmemb' (by simpa only [natDegree_map_eq_of_injective hi] using hz))
  simp only [scanDegree, hlast, Nat.add_sub_cancel]
  omega

def finish {F : Resultant.Family} (a : Resultant.Access F) (z : List Bool) : List Bool :=
  BinaryNat.sub (pair (a.bits.rightDegree (pairFst z)) (pairSnd z))

theorem finish_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) : finish a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP ha.rightDegree) pairSnd_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem scanDegreeEvaluator {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.leftCoefficient) (Q : SpaceFunction a.bits.rightCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (scanDegree a c)) := by
  have D := (PrincipalCoefficientBits.nonzeroDecider a ha P Q).precompose (reverseQuery a) (reverseQuery_FP a ha)
  have E := BoundedChoice.evaluator D (BinaryNat.succ ∘ a.bits.rightDegree)
    (mem_FP_comp ha.rightDegree BinaryNat.succ_mem_FP)
  have R := E.withInput.postcompose (finish a) (finish_FP a ha)
  refine R.congr (funext fun c => ?_)
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, a.rightDegree,
    BinaryNat.succ_eq_bits, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem degreeEvaluator {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.leftCoefficient) (Q : SpaceFunction a.bits.rightCoefficient)
    (hm : ∀ c, F.leftDegree c = (F.left c).natDegree) (hn : ∀ c, F.rightDegree c = (F.right c).natDegree)
    (hq : ∀ c, F.right c ≠ 0) (hlt : ∀ c, (F.right c).natDegree < (F.left c).natDegree) :
    SpaceFunction (fun c => BinaryNatCode.encode (degree (F.left c) (F.right c))) :=
  (scanDegreeEvaluator a ha P Q).congr (funext fun c => congrArg BinaryNatCode.encode
    (scanDegree_eq a c (hm c) (hn c) (hq c) (hlt c)))

end LeanCanny.Algebra.PolynomialGCDBits
