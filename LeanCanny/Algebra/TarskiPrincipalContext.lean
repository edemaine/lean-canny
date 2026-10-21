/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TarskiDegreeContext
public import LeanCanny.Algebra.PrincipalCoefficientQuery

/-! # Principal queries with a computed seed degree

The seed degree is retained as a binary word. Fixed-bound principal coefficients
are defined on arbitrary metadata, while the composed computation supplies the
actual seed degree. Both source routines come from the original head and query.
-/

@[expose] public section

namespace LeanCanny.Algebra.TarskiPrincipalContext
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open IntegerTarskiSeedBits
open PrincipalSubresultant

def seedBoundCode (F : Family) (c : List Bool) : List Bool :=
  TarskiSeedBits.seedBudgetCode (F.degree c) (F.queryBound c) (F.headMass c) (F.queryMass c)

theorem seedBoundCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : seedBoundCode F ∈ FP := by
  have h := TarskiSeedBits.seedBudgetCode_mem_FP hF.degree hF.queryBound hF.headMass hF.queryMass
  exact h

noncomputable def family (F : Family) : Resultant.Family where
  left y := F.head (pairFst y)
  right y := F.reduced (pairFst y)
  leftDegree y := Nat.fromBitsLE (F.degree (pairFst y))
  rightDegree y := Nat.fromBitsLE (pairSnd y)
  coefficientBits y := Nat.fromBitsLE (F.headMass (pairFst y)) + Nat.fromBitsLE (seedBoundCode F (pairFst y))
  left_bound y i := ((coeff_natAbs_le_coefficientMass _ _).trans (F.head_mass (pairFst y))).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  right_bound y i := by
    have hs := TarskiSeedBits.seed_coeff_size_le (F.head (pairFst y)) (F.query (pairFst y))
      (F.degree (pairFst y)) (F.queryBound (pairFst y)) (F.headMass (pairFst y)) (F.queryMass (pairFst y))
      (F.head_degree _) (F.head_mass _) (F.query_mass _) i
    exact (Nat.size_le.mp hs).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst p))) (BinaryNat.normalize (pairSnd p)))
    (BinaryNat.normalize (pairSnd (pairFst p)))

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hc hi) hm

theorem sourceQuery_packet (q : List Bool) (i : ℕ) :
    sourceQuery (pair q (BinaryNatCode.encode i)) =
      pair (pair (pairFst (pairFst q)) (BinaryNatCode.encode i))
        (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) := by
  simp only [sourceQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]

noncomputable def access {F : Family} (a : Access F) : Resultant.Access (family F) where
  bits := {
    leftDegree := BinaryNat.normalize ∘ F.degree ∘ pairFst
    rightDegree := BinaryNat.normalize ∘ pairSnd
    coefficientBits y := BinaryNat.add (pair (F.headMass (pairFst y)) (seedBoundCode F (pairFst y)))
    leftCoefficient := a.headCoefficient ∘ sourceQuery
    rightCoefficient := F.residue ∘ sourceQuery }
  leftDegree y := BinaryNat.normalize_eq_bits _
  rightDegree y := BinaryNat.normalize_eq_bits _
  coefficientBits y := by simp only [BinaryNat.add_pair, family, BinaryNatCode.encode]
  leftCoefficient := by
    intro q i
    change a.headCoefficient (sourceQuery (pair q (BinaryNatCode.encode i))) =
      integerResidue ((F.head (pairFst (pairFst q))).coeff i) (Nat.fromBitsLE (pairSnd q) + 1)
    rw [sourceQuery_packet]
    have h := a.head_eq (pairFst (pairFst q)) i (Nat.fromBitsLE (pairSnd q) + 1) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  rightCoefficient := by
    intro q i
    change F.residue (sourceQuery (pair q (BinaryNatCode.encode i))) =
      integerResidue ((F.reduced (pairFst (pairFst q))).coeff i) (Nat.fromBitsLE (pairSnd q) + 1)
    rw [sourceQuery_packet]
    simp only [Family.residue, Family.coefficient, mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem controls {F : Family} (a : Access F) (hF : ControlsPolyTime F) :
    (access a).bits.ControlsPolyTime := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP hF.degree) BinaryNat.normalize_mem_FP
  have hn := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hb := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hF.headMass)
    (mem_FP_comp pairFst_mem_FP (seedBoundCode_mem_FP F hF))) BinaryNat.add_mem_FP
  constructor
  · simpa only [access, Function.comp_def] using hm
  · simpa only [access] using hn
  · refine mem_FP_of_eq (g := (access a).bits.coefficientBits) hb ?_
    intro y
    simp only [access, Function.comp_apply]

theorem leftEvaluator {F : Family} (a : Access F) (P : SpaceFunction a.headCoefficient) :
    SpaceFunction (access a).bits.leftCoefficient := by
  simpa only [access] using P.precompose sourceQuery sourceQuery_mem_FP

theorem rightEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (access a).bits.rightCoefficient := by
  simpa only [access] using (a.residueEvaluator hF P Q).precompose sourceQuery sourceQuery_mem_FP

noncomputable def value (F : Family) (y : List Bool) : ℤ :=
  permanencesMinusVariations ((List.range ((family F).leftDegree y + 1)).reverse.map
    (signedPsc ((family F).left y) ((family F).right y) ((family F).leftDegree y) ((family F).rightDegree y)))

theorem evaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (fun y => SignStatisticBits.integerCode (value F y)) :=
  PrincipalCoefficientBits.queryEvaluator (access a) (controls a hF)
    (leftEvaluator a P) (rightEvaluator a hF P Q)

theorem value_prepared (F : Family) (c : List Bool) :
    value F (pair c (BinaryNatCode.encode (F.reduced c).natDegree)) =
      PseudoRemainder.principalQuery (F.head c) (F.query c) (Nat.fromBitsLE (F.degree c))
        (Nat.fromBitsLE (F.degree c) + Nat.fromBitsLE (F.queryBound c)) := by
  simp only [value, family, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    PseudoRemainder.principalQuery, Family.reduced]

/-- Compute and retain the actual seed degree before evaluating its principal
query. Only the original two uniform coefficient routines are external. -/
theorem principalEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode
      (PseudoRemainder.principalQuery (F.head c) (F.query c) (Nat.fromBitsLE (F.degree c))
        (Nat.fromBitsLE (F.degree c) + Nat.fromBitsLE (F.queryBound c)))) := by
  let S := (a.seedDegreeEvaluator hF P Q).withInput
  let E := S.chain (evaluator a hF P Q)
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, value_prepared]

end LeanCanny.Algebra.TarskiPrincipalContext
