/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalCoefficientAccess

/-! # Signed integer principal coefficients from original coefficient readers

Inside the principal range, a modular determinant and binary parity correction
give the signed coefficient. Above the range, the two retained leading
coefficients and zero are selected explicitly. Uniform residues and a derived
bit budget then give a complete three-way integer sign evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalCoefficientBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower PrincipalSubresultant

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def order (q : List Bool) : List Bool := pairSnd (pairFst q)
def modulus (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1

theorem origin_mem_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem order_mem_FP : order ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def gap {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (a.bits.leftDegree (origin q)) (order q))
def positiveWeight {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Prop :=
  SignStatisticBits.evenWord (SignStatisticBits.chooseTwo (gap a q))
instance {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Decidable (positiveWeight a q) :=
  inferInstanceAs (Decidable (SignStatisticBits.evenWord (SignStatisticBits.chooseTwo (gap a q))))

theorem gap_mem_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) : gap a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp origin_mem_FP ha.leftDegree) order_mem_FP) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := gap a) h ?_
  intro q
  simp only [gap, Function.comp_apply]
theorem positiveWeight_fppred {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    FPPred (positiveWeight a) := by
  have hg := gap_mem_FP a ha
  have hc := mem_FP_comp hg SignStatisticBits.chooseTwo_mem_FP
  have h := SignStatisticBits.evenWord_fppred.comp hc
  refine h.of_iff (fun q => ?_)
  simp only [positiveWeight, Function.comp_apply]

def normalizeSign {F : Resultant.Family} (a : Resultant.Access F) (z : List Bool) : List Bool :=
  if positiveWeight a (pairFst z) then pairSnd z
  else ArithmeticBits.negate (pair (BinaryNat.succ (pairSnd (pairFst z))) (pairSnd z))

theorem normalizeSign_mem_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    normalizeSign a ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  have h := ((positiveWeight_fppred a ha).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP hn
  refine mem_FP_of_eq (g := normalizeSign a) h ?_
  intro z
  simp only [normalizeSign, Function.comp_apply]

theorem normalizeSign_pair {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) (z : ℤ) :
    normalizeSign a (pair q (integerResidue z (modulus q))) = integerResidue
      ((-1 : ℤ) ^ (F.leftDegree (origin q) - Nat.fromBitsLE (order q)).choose 2 * z) (modulus q) := by
  let k := (F.leftDegree (origin q) - Nat.fromBitsLE (order q)).choose 2
  have he : positiveWeight a q ↔ Even k := by
    simp only [positiveWeight, gap, a.leftDegree, BinaryNat.sub_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, SignStatisticBits.chooseTwo_code, SignStatisticBits.evenWord_iff]
    rfl
  have hm : BinaryNat.succ (pairSnd q) = BinaryNatCode.encode (modulus q) := by
    rw [BinaryNat.succ_eq_bits]
    rfl
  have hn : modulus q ≠ 0 := by dsimp [modulus]; omega
  let : NeZero (modulus q) := ⟨hn⟩
  simp only [normalizeSign, pairFst_pair, pairSnd_pair, he, hm]
  change (if Even k then integerResidue z (modulus q) else
    ArithmeticBits.negate (pair (BinaryNatCode.encode (modulus q)) (integerResidue z (modulus q)))) =
      integerResidue ((-1 : ℤ) ^ k * z) (modulus q)
  by_cases hk : Even k
  · simp only [hk, ↓reduceIte, hk.neg_one_pow, one_mul]
  · rw [ite_eq_right hk]
    change ArithmeticBits.negate (pair (BinaryNatCode.encode (modulus q)) (residueBits (z : ZMod (modulus q)))) = _
    rw [ArithmeticBits.negate_residueBits]
    simp only [neg_one_pow_eq_ite, hk, ↓reduceIte, neg_one_mul, integerResidue, Int.cast_neg]

theorem minor_value (F : Resultant.Family) (q : List Bool) :
    (minorFamily F).integer.modular.value q =
      integerResidue (((minorFamily F).integer.matrix (pairFst q)).det) (modulus q) := by
  change residueBits (((minorFamily F).integer.matrix (pairFst q)).map
    (Int.castRingHom (ZMod (modulus q)))).det = _
  exact congrArg residueBits ((Int.castRingHom (ZMod (modulus q))).map_det
    ((minorFamily F).integer.matrix (pairFst q))).symm

/-- A scalar wrapper permits rewriting the order without transporting matrix instances. -/
noncomputable def minorDet (p f : ℤ[X]) (m n k : ℕ) : ℤ :=
  (Subresultant.minor p f m n k k).det

def within {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Prop :=
  Nat.fromBitsLE (order q) ≤ Nat.fromBitsLE (a.bits.leftDegree (origin q)) ∧
    Nat.fromBitsLE (order q) ≤ Nat.fromBitsLE (a.bits.rightDegree (origin q))
instance {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Decidable (within a q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem within_fppred {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    FPPred (within a) :=
  (BinaryNat.le_fppred order_mem_FP (mem_FP_comp origin_mem_FP ha.leftDegree)).and
    (BinaryNat.le_fppred order_mem_FP (mem_FP_comp origin_mem_FP ha.rightDegree))

def directQuery (q : List Bool) : List Bool :=
  pair (pair (origin q) (pairSnd q)) (BinaryNat.normalize (order q))
theorem directQuery_mem_FP : directQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair origin_mem_FP pairSnd_mem_FP) (mem_FP_comp order_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def residueValue {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : List Bool :=
  if within a q then normalizeSign a (pair q ((minorFamily F).integer.modular.value q))
  else if Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.leftDegree (origin q)) then a.bits.leftCoefficient (directQuery q)
  else if Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.rightDegree (origin q)) then a.bits.rightCoefficient (directQuery q)
  else []

theorem residueValue_eq {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) :
    residueValue a q = integerResidue (coefficient F (pairFst q)) (modulus q) := by
  have hw : within a q ↔ Nat.fromBitsLE (order q) ≤
      min (F.leftDegree (origin q)) (F.rightDegree (origin q)) := by
    simp only [within, a.leftDegree, a.rightDegree, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.le_min]
  have hl : a.bits.leftCoefficient (directQuery q) =
      integerResidue ((F.left (origin q)).coeff (Nat.fromBitsLE (order q))) (modulus q) := by
    have h := a.leftCoefficient (pair (origin q) (pairSnd q)) (Nat.fromBitsLE (order q))
    change _ = integerResidue ((F.left (pairFst (pair (origin q) (pairSnd q)))).coeff
      (Nat.fromBitsLE (order q))) (Nat.fromBitsLE (pairSnd (pair (origin q) (pairSnd q))) + 1) at h
    rw [pairFst_pair, pairSnd_pair] at h
    simpa only [directQuery, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, modulus] using h
  have hr : a.bits.rightCoefficient (directQuery q) =
      integerResidue ((F.right (origin q)).coeff (Nat.fromBitsLE (order q))) (modulus q) := by
    have h := a.rightCoefficient (pair (origin q) (pairSnd q)) (Nat.fromBitsLE (order q))
    change _ = integerResidue ((F.right (pairFst (pair (origin q) (pairSnd q)))).coeff
      (Nat.fromBitsLE (order q))) (Nat.fromBitsLE (pairSnd (pair (origin q) (pairSnd q))) + 1) at h
    rw [pairFst_pair, pairSnd_pair] at h
    simpa only [directQuery, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, modulus] using h
  by_cases hv : within a q
  · have hk := hw.mp hv
    rw [residueValue, ite_eq_left hv, minor_value, normalizeSign_pair]
    have hm : min (Nat.fromBitsLE (order q))
        (min (F.leftDegree (origin q)) (F.rightDegree (origin q))) = Nat.fromBitsLE (order q) :=
      Nat.min_eq_left hk
    change integerResidue ((-1 : ℤ) ^ (F.leftDegree (origin q) - Nat.fromBitsLE (order q)).choose 2 *
      minorDet (F.left (origin q)) (F.right (origin q)) (F.leftDegree (origin q)) (F.rightDegree (origin q))
        (min (Nat.fromBitsLE (order q)) (min (F.leftDegree (origin q)) (F.rightDegree (origin q)))))
      (modulus q) = integerResidue
        (signedPsc (F.left (origin q)) (F.right (origin q)) (F.leftDegree (origin q)) (F.rightDegree (origin q))
          (Nat.fromBitsLE (order q))) (modulus q)
    rw [hm, signedPsc_eq_minor _ _ _ _ _ hk]
    rfl
  · have hk : min (F.leftDegree (origin q)) (F.rightDegree (origin q)) < Nat.fromBitsLE (order q) := by
      have := (hw.not).mp hv
      omega
    rw [residueValue, ite_eq_right hv]
    simp only [a.leftDegree, a.rightDegree, BinaryNatCode.encode, Nat.fromBitsLE_bits, hl, hr]
    change (if Nat.fromBitsLE (order q) = F.leftDegree (origin q) then _ else _) = integerResidue
      (signedPsc (F.left (origin q)) (F.right (origin q)) (F.leftDegree (origin q)) (F.rightDegree (origin q))
        (Nat.fromBitsLE (order q))) (modulus q)
    rw [signedPsc_of_lt _ _ hk]
    split_ifs with hm hn
    · rw [hm]
    · rw [hn]
    · simp only [integerResidue, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode,
        show Nat.bits 0 = [] from rfl]

theorem residueEvaluator {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) : SpaceFunction (residueValue a) := by
  let M := (minorResidueEvaluator a ha P Q).withInput.postcompose (normalizeSign a) (normalizeSign_mem_FP a ha)
  let L := P.precompose directQuery directQuery_mem_FP
  let R := Q.precompose directQuery directQuery_mem_FP
  have hleft : FPPred (fun q => Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.leftDegree (origin q))) :=
    BinaryNat.eq_fppred order_mem_FP (mem_FP_comp origin_mem_FP ha.leftDegree)
  have hright : FPPred (fun q => Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.rightDegree (origin q))) :=
    BinaryNat.eq_fppred order_mem_FP (mem_FP_comp origin_mem_FP ha.rightDegree)
  let E := SpaceFunction.branch (fun q => decide (within a q)) (within_fppred a ha).flag_mem_FP M
    (SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.leftDegree (origin q))))
      hleft.flag_mem_FP L
      (SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (order q) = Nat.fromBitsLE (a.bits.rightDegree (origin q))))
        hright.flag_mem_FP R (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))))
  refine E.congr (funext fun q => ?_)
  simp only [residueValue, Function.comp_apply, decide_eq_true_eq]

def budgetCode {F : Resultant.Family} (a : Resultant.Access F) (r : List Bool) : List Bool :=
  BinaryNat.add (pair (SylvesterBits.budget a.bits (pairFst r))
    (BinaryNat.succ (a.bits.coefficientBits (pairFst r))))

theorem budgetCode_mem_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    budgetCode a ∈ FP := by
  have hb := mem_FP_comp pairFst_mem_FP (SylvesterBits.budget_mem_FP_of_controls a.bits ha)
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP ha.coefficientBits) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hb hc) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := budgetCode a) h ?_
  intro r
  simp only [budgetCode, Function.comp_apply]

theorem budgetCode_eq {F : Resultant.Family} (a : Resultant.Access F) (r : List Bool) :
    budgetCode a r = BinaryNatCode.encode (budget F r) := by
  rw [budgetCode, SylvesterBits.budget_code a.bits (pairFst r) _ _ _
    (a.leftDegree _) (a.rightDegree _) (a.coefficientBits _)]
  simp only [a.coefficientBits, BinaryNat.succ_eq_bits, BinaryNat.add_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, budget, Resultant.Family.integer]
  congr 1

theorem signEvaluator {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) :
    SpaceFunction (fun r => InfinitesimalSign.tag (coefficient F r)) := by
  apply IntegerSignumBits.evaluator (residueEvaluator a ha P Q) (budgetCode a) (budgetCode_mem_FP a ha)
    (coefficient F)
  · intro r
    rw [budgetCode_eq, show Nat.fromBitsLE (BinaryNatCode.encode (budget F r)) = budget F r from Nat.fromBitsLE_bits _]
    exact coefficient_size F r
  · intro r m hm
    rw [residueValue_eq]
    simp only [pairFst_pair, modulus, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rfl

end LeanCanny.Algebra.PrincipalCoefficientBits
