/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzMomentSpace

/-!
# Factor entries with space-bounded original matrix access

FP selection combines one, a negative diagonal entry, a negative scalar moment,
and zero. The selected child retains its query for modular negation. Correctness
is connected to the previously verified factor-child reference computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.ModularAccess

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

def negative (a : FactorChild.Access) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (a.modulus (pairFst (pairFst z))) (pairSnd z))

theorem negative_mem_FP (a : FactorChild.Access) (hm : a.modulus ∈ FP) : negative a ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have h := mem_FP_comp (mem_FP_pair hc pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negative a) h ?_
  intro z
  simp only [Function.comp_apply, negative]

theorem negative_pair {F : ModularFamily} (a : ModularAccess F) (p : List Bool)
    (x : ZMod (F.modulus (pairFst p))) : negative a.access (pair p (residueBits x)) = residueBits (-x) := by
  let : NeZero (F.modulus (pairFst p)) := ⟨F.modulus_ne_zero (pairFst p)⟩
  simp only [negative, pairFst_pair, pairSnd_pair, (a.correct (pairFst p)).modulus]
  exact ArithmeticBits.negate_residueBits _ x

def oneWord (a : FactorChild.Access) (p : List Bool) : List Bool := ArithmeticBits.one (a.modulus (pairFst p))

theorem oneWord_mem_FP (a : FactorChild.Access) (hm : a.modulus ∈ FP) : oneWord a ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) ArithmeticBits.one_mem_FP
  exact h

def mode (a : FactorChild.Access) (tag p : List Bool) : Bool := decide (QueryBits.selector a.dimension p = tag)

theorem mode_mem_FP (a : FactorChild.Access) (hd : a.dimension ∈ FP) (tag : List Bool) :
    (fun p => [mode a tag p]) ∈ FP :=
  (stringEq_fppred (QueryBits.selector_mem_FP hd) (constFn_mem_FP tag)).flag_mem_FP

noncomputable def factorValue {F : ModularFamily} (a : ModularAccess F) (p : List Bool) : List Bool :=
  if QueryBits.selector a.access.dimension p = [true] then oneWord a.access p
  else if QueryBits.selector a.access.dimension p = [false, true] then
    negative a.access (pair p (a.access.entry (EntryAccess.diagonalInput a.access.dimension p)))
  else if QueryBits.selector a.access.dimension p = [true, true] then
    negative a.access (pair p ((momentFamily F).value p))
  else []

theorem factorEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.access.entry) : SpaceFunction (factorValue a) := by
  have hn := negative_mem_FP a.access ha.modulus
  have ED := ((E.precompose (EntryAccess.diagonalInput a.access.dimension)
    (EntryAccess.diagonalInput_mem_FP ha.dimension)).withInput).postcompose (negative a.access) hn
  have EM := ((momentEvaluator a ha E).withInput).postcompose (negative a.access) hn
  have EZ := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have EO := SpaceFunction.ofFP (oneWord a.access) (oneWord_mem_FP a.access ha.modulus)
  have RM := SpaceFunction.branch (mode a.access [true, true]) (mode_mem_FP a.access ha.dimension _) EM EZ
  have RD := SpaceFunction.branch (mode a.access [false, true]) (mode_mem_FP a.access ha.dimension _) ED RM
  have R := SpaceFunction.branch (mode a.access [true]) (mode_mem_FP a.access ha.dimension _) EO RD
  refine R.congr ?_
  funext p
  simp only [factorValue, mode, Function.comp_apply, decide_eq_true_eq]

theorem decoded_raw {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    FactorChild.DecodedAt a.access p (stage F p)
      (Nat.fromBitsLE (QueryBits.colIndex p) / (F.dimension (pairFst p) + 1))
      (Nat.fromBitsLE (QueryBits.rowIndex p) % (F.dimension (pairFst p) + 1))
      (Nat.fromBitsLE (QueryBits.colIndex p) % (F.dimension (pairFst p) + 1)) := by
  constructor
  · exact sourceLayer_code a p
  · rw [QueryBits.targetLayer_eq_code]
    simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value]
  · rw [QueryBits.sourceDegree_eq_code]
    simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value]
  · rw [QueryBits.targetDegree_eq_code]
    simp only [QueryBits.inputDimension, (a.correct (pairFst p)).dimension, QueryBits.code_value]

theorem factorValue_eq_reference {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    factorValue a p = FactorChild.output a.access
      ((FactorChild.advance a.access)^[FactorChild.time a.access p] (FactorChild.start a.access p)) := by
  let : NeZero (F.modulus (pairFst p)) := ⟨F.modulus_ne_zero (pairFst p)⟩
  by_cases hm : QueryBits.selector a.access.dimension p = [true, true]
  · have hq := decoded_raw a p
    have hs := (FactorChild.moment_conditions a.access p (F.dimension (pairFst p)) _ _ _ _
      (a.correct (pairFst p)).dimension hq hm).2.1
    have h1 : QueryBits.selector a.access.dimension p ≠ [true] := by rw [hm]; decide
    have h2 : QueryBits.selector a.access.dimension p ≠ [false, true] := by rw [hm]; decide
    rw [factorValue, ite_eq_right h1, ite_eq_right h2, ite_eq_left hm]
    rw [moment_value_eq p hs, negative_pair]
    have h := FactorChild.run_moment a.access p (F.modulus (pairFst p)) (F.dimension (pairFst p))
      _ _ _ _ (F.matrix (pairFst p)) (a.correct (pairFst p)) hq hs hm
    simpa only [momentDegree] using h.symm
  · rw [FactorChild.run_immediate a.access p hm]
    simp only [factorValue, hm, ↓reduceIte, FactorChild.fastValue, negative, oneWord, pairFst_pair, pairSnd_pair]

theorem factorValue_packet {F : ModularFamily} (a : ModularAccess F) (c : List Bool)
    (i j : Fin ((F.dimension c + 1) * (F.dimension c + 1))) :
    factorValue a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (powerMatrix (F.matrix c) i j) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  rw [factorValue_eq_reference]
  exact FactorChild.run_packet a.access c (F.modulus c) (F.dimension c) (F.matrix c) (a.correct c) i j

end LeanCanny.Algebra.Berkowitz.ModularAccess
