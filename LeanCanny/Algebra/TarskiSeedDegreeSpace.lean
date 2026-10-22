/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerTarskiSeedSpace
public import LeanCanny.Algebra.PolynomialDegreeSpace

/-! # Actual degrees of the original head and computed integer seed

Both scans use coefficient-sign routines with full space certificates. Their
outputs can be retained as binary metadata for subsequent determinant queries.
The offset scan also distinguishes a zero head from a nonzero constant head.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerTarskiSeedBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

noncomputable def Family.originalCoefficient (F : Family) (r : List Bool) : ℤ :=
  (F.head (pairFst r)).coeff (Nat.fromBitsLE (pairSnd r))

def normalizeIndex (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNat.normalize (pairSnd (pairFst q)))) (pairSnd q)

theorem normalizeIndex_mem_FP : normalizeIndex ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair (mem_FP_pair hc hi) pairSnd_mem_FP
  refine mem_FP_of_eq (g := normalizeIndex) h ?_
  intro q
  simp only [normalizeIndex, Function.comp_apply]

theorem zero_tag_iff (z : ℤ) :
    (if z = 0 then ([] : List Bool) else if z < 0 then [true] else [false, true]) = [] ↔ z = 0 := by
  by_cases hz : z = 0 <;> by_cases hn : z < 0 <;> simp [hz, hn]

namespace Access

theorem headSignEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) :
    SpaceFunction (fun r => if F.originalCoefficient r = 0 then [] else
      if F.originalCoefficient r < 0 then [true] else [false, true]) := by
  let R := P.precompose normalizeIndex normalizeIndex_mem_FP
  let budget := fun r => BinaryNat.succ (F.headMass (pairFst r))
  have hb := mem_FP_comp (mem_FP_comp pairFst_mem_FP hF.headMass) BinaryNat.succ_mem_FP
  apply IntegerSignumBits.evaluator R budget hb F.originalCoefficient
  · intro r
    have h := (coeff_natAbs_le_coefficientMass (F.head (pairFst r)) (Nat.fromBitsLE (pairSnd r))).trans
      (F.head_mass (pairFst r))
    simpa only [Family.originalCoefficient, budget, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
      Nat.size_pow] using Nat.size_le_size h
  · intro r m hm
    simp only [Function.comp_apply, normalizeIndex, pairFst_pair, pairSnd_pair,
      BinaryNat.normalize_eq_bits]
    exact a.head_eq (pairFst r) (Nat.fromBitsLE (pairSnd r)) m hm

theorem head_tag_zero (F : Family) (c : List Bool) (i : ℕ) :
    (if F.originalCoefficient (pair c (BinaryNatCode.encode i)) = 0 then ([] : List Bool) else
      if F.originalCoefficient (pair c (BinaryNatCode.encode i)) < 0 then [true] else [false, true]) = [] ↔
      (F.head c).coeff i = 0 := by
  rw [zero_tag_iff]
  simp only [Family.originalCoefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem headOffsetEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (if F.head c = 0 then 0 else (F.head c).natDegree + 1)) :=
  PolynomialDegreeBits.offsetEvaluator (headSignEvaluator a hF P) F.degree hF.degree F.head F.head_degree
    (head_tag_zero F)

theorem headDegreeEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (F.head c).natDegree) :=
  PolynomialDegreeBits.degreeEvaluator (headSignEvaluator a hF P) F.degree hF.degree F.head F.head_degree
    (head_tag_zero F)

theorem seedDegreeEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (F.reduced c).natDegree) := by
  apply PolynomialDegreeBits.degreeEvaluator (signEvaluator a hF P Q) F.degree hF.degree F.reduced
  · intro c
    exact (PseudoRemainder.seed_natDegree_lt (F.head c) (F.query c) _ _ (F.degree_pos c) (F.input_degree c)).le
  · intro c i
    rw [zero_tag_iff]
    simp only [Family.coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end Access
end LeanCanny.Algebra.IntegerTarskiSeedBits
