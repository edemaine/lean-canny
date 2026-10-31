/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionControl
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native streamed entries of the pure-power reduction matrix

Normal source columns read their common integer diagonal coefficient.
Other degree-valid columns read and negate one shifted lower coefficient.
All exponent controls run in FP, even for binary spatial degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.PurePowerReductionBits

open LeanCanny.Encoding LeanCanny.Computation

def differenceAt (L : Layout) (p : List Bool) (i : ℕ) : ℕ := colAt L p i - remainderAt L p i

def differenceRead (L : Layout) (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (colRead L q) (remainderRead L q))

theorem differenceRead_mem_FP {L : Layout} (h : L.PolyTime) : differenceRead L ∈ FP :=
  mem_FP_comp (mem_FP_pair (colRead_mem_FP h) (remainderRead_mem_FP h)) BinaryNat.sub_mem_FP

theorem differenceRead_packet (L : Layout) (p : List Bool) (i : ℕ) :
    differenceRead L (pair p (BinaryNatCode.encode i)) = BinaryNatCode.encode (differenceAt L p i) := by
  simp only [differenceRead, colRead, FixedWidthQuery.read_packet, remainderRead_packet,
    BinaryNat.sub_pair, fromBits_encode, differenceAt, colAt]
  rfl

def differenceWord (L : Layout) (p : List Bool) : List Bool :=
  FixedWidthNatVector.encode (L.arity (context p)) (L.width (context p)) (differenceAt L p)

theorem differenceWord_mem_FP {L : Layout} (h : L.PolyTime) : differenceWord L ∈ FP :=
  FixedWidthNatVector.encode_of_coordinate (h.arity.comp context_mem_FP) (h.width.comp context_mem_FP)
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
    (FixedWidthNatVector.coordinate_of_reader (differenceRead_mem_FP h) (differenceRead_packet L))

def admissible (L : Layout) (p : List Bool) : Prop :=
  ∀ i < L.arity (context p), remainderAt L p i ≤ colAt L p i

instance (L : Layout) (p : List Bool) : Decidable (admissible L p) :=
  inferInstanceAs (Decidable (∀ i < L.arity (context p), remainderAt L p i ≤ colAt L p i))

theorem admissible_fppred {L : Layout} (h : L.PolyTime) : FPPred (admissible L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (remainderRead_mem_FP h)
  have hc := mem_FP_comp loopQuery_mem_FP (colRead_mem_FP h)
  have hf := (BinaryNat.le_fppred hr hc).forall_lt (h.arity.comp context_mem_FP)
  apply hf.of_iff
  intro p
  simp only [loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    remainderRead_packet, colRead, FixedWidthQuery.read_packet, fromBits_encode, admissible, colAt]

def sourceQuery (L : Layout) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNatCode.encode (pivot L p)) (BinaryNat.normalize (differenceWord L p)))

theorem sourceQuery_mem_FP {L : Layout} (h : L.PolyTime) : sourceQuery L ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (bits_mem_FP (pivot_unary h))
    (mem_FP_comp (differenceWord_mem_FP h) BinaryNat.normalize_mem_FP))

def sameIndex (p : List Bool) : Prop := Nat.fromBitsLE (row p) = Nat.fromBitsLE (col p)

instance (p : List Bool) : Decidable (sameIndex p) := inferInstanceAs (Decidable (_ = _))

theorem sameIndex_fppred : FPPred sameIndex :=
  BinaryNat.eq_fppred row_mem_FP col_mem_FP

def normal (L : Layout) (p : List Bool) : Prop :=
  ∀ i < L.arity (context p), rowAt L p i < L.degree (context p) i

instance (L : Layout) (p : List Bool) : Decidable (normal L p) :=
  inferInstanceAs (Decidable (∀ i < _, _))

theorem normal_fppred {L : Layout} (h : L.PolyTime) : FPPred (normal L) := by
  have hr := mem_FP_comp loopQuery_mem_FP (rowRead_mem_FP h)
  have hf := (BinaryNat.lt_fppred hr (degreeLoop_binary h).bits_mem_FP).forall_lt
    (h.arity.comp context_mem_FP)
  apply hf.of_iff
  intro p
  simp only [normal, degreeLoop, loopQuery, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.length_replicate, rowRead, FixedWidthQuery.read_packet, fromBits_encode, rowAt]

def valid (L : Layout) (bound : List Bool → ℕ) (p : List Bool) : Prop :=
  rowTotal L p ≤ bound (context p)

instance (L : Layout) (bound : List Bool → ℕ) (p : List Bool) : Decidable (valid L bound p) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem valid_fppred {L : Layout} (h : L.PolyTime) {bound : List Bool → ℕ} (hb : BinaryFn bound) :
    FPPred (valid L bound) := (rowTotal_binary h).le (hb.comp context_mem_FP)

def negate (p : List Bool) : List Bool :=
  MatrixPower.ArithmeticBits.negate
    (pair (BinaryNat.succ (pairSnd (pairFst (pairFst p)))) (pairSnd p))

attribute [local irreducible] MatrixPower.ArithmeticBits.negate

theorem negate_mem_FP : negate ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    BinaryNat.succ_mem_FP
  exact mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) MatrixPower.ArithmeticBits.negate_mem_FP

def entry (L : Layout) (bound : List Bool → ℕ) (constant coefficient : List Bool → List Bool)
    (p : List Bool) : List Bool :=
  if normal L p then if sameIndex p then constant (pairFst p) else []
  else if valid L bound p then
    if admissible L p then negate (pair p (coefficient (sourceQuery L p))) else []
  else []

theorem entryEvaluator {L : Layout} (h : L.PolyTime) {bound : List Bool → ℕ} (hb : BinaryFn bound)
    {constant coefficient : List Bool → List Bool} (EC : SpaceFunction constant) (EL : SpaceFunction coefficient) :
    SpaceFunction (entry L bound constant coefficient) := by
  have EZ : SpaceFunction (fun _ : List Bool => ([] : List Bool)) := SpaceFunction.ofFP _ (constFn_mem_FP [])
  have ED := SpaceFunction.branch (fun p => decide (sameIndex p)) sameIndex_fppred.flag_mem_FP
    (EC.precompose pairFst pairFst_mem_FP) EZ
  have EN := (EL.precompose (sourceQuery L) (sourceQuery_mem_FP h)).withInput.postcompose negate negate_mem_FP
  have EA := SpaceFunction.branch (fun p => decide (admissible L p)) (admissible_fppred h).flag_mem_FP EN EZ
  have EV := SpaceFunction.branch (fun p => decide (valid L bound p)) (valid_fppred h hb).flag_mem_FP EA EZ
  have ER := SpaceFunction.branch (fun p => decide (normal L p)) (normal_fppred h).flag_mem_FP ED EV
  exact ER.congr (funext fun p => by simp only [entry, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.PurePowerReductionBits
