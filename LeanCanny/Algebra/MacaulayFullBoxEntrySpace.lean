/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxShiftSpace
public import LeanCanny.Algebra.MacaulayFullBoxFinite
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Encoding.BinaryDivFP

/-! # Native entries of the canonical full-box Gram block matrix -/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBoxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.add BinaryNat.mul BinaryNat.sub BinaryNat.divMod
  BinaryNat.succ ArithmeticBits.one ArithmeticBits.negate

/-- Entry packets are c/row/column/(inner degree,outer degree). -/
def uv (q : List Bool) := pairSnd (pairSnd (pairSnd q))
@[program_certificate] lemma uv_FP : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    uv Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by polytime [uv]

def columnsCode (L : Layout) (c : List Bool) := FixedWidthPolynomial.countCode L.arity L.width c
lemma columnsCode_FP {L : Layout} (h : L.Controls) : columnsCode L ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP h.arity h.width

lemma columnsCode_eq (L : Layout) (c : List Bool) :
    columnsCode L c = BinaryNatCode.encode (FixedWidthPolynomial.count (L.arity c) (L.width c)) :=
  FixedWidthPolynomial.countCode_code _ _ c

def sourceCut (L : Layout) (c : List Bool) :=
  BinaryNat.mul (pair (BinaryNatCode.encode (L.arity c)) (columnsCode L c))
def rowCut (L : Layout) (c : List Bool) := BinaryNat.add (pair (sourceCut L c) (columnsCode L c))
lemma sourceCut_FP {L : Layout} (h : L.Controls) : sourceCut L ∈ FP :=
  mem_FP_comp (mem_FP_pair (bits_mem_FP h.arity) (columnsCode_FP h)) BinaryNat.mul_mem_FP
lemma rowCut_FP {L : Layout} (h : L.Controls) : rowCut L ∈ FP :=
  mem_FP_comp (mem_FP_pair (sourceCut_FP h) (columnsCode_FP h)) BinaryNat.add_mem_FP

lemma sourceCut_eq (L : Layout) (c : List Bool) :
    sourceCut L c = BinaryNatCode.encode (L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c)) := by
  simp only [sourceCut, columnsCode_eq, BinaryNat.mul_pair, MacaulayBits.fromBits_encode]
  rfl
lemma rowCut_eq (L : Layout) (c : List Bool) :
    rowCut L c = BinaryNatCode.encode ((L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c)) := by
  simp only [rowCut, sourceCut_eq, columnsCode_eq, BinaryNat.add_pair, MacaulayBits.fromBits_encode]
  congr 1
  ring

private lemma binaryEq_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred (fun q => Nat.fromBitsLE (a q) = Nat.fromBitsLE (b q)) :=
  ((BinaryNat.le_fppred ha hb).and (BinaryNat.le_fppred hb ha)).of_iff (fun _ => by omega)

private lemma zero_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    FPPred (fun q => Nat.fromBitsLE (a q) = 0) :=
  (BinaryNat.le_fppred ha (constFn_mem_FP [])).of_iff (fun _ => by change _ ≤ 0 ↔ _; omega)

def unit (modulus : List Bool → List Bool) (q : List Bool) :=
  if Nat.fromBitsLE (pairFst (uv q)) = 0 ∧ Nat.fromBitsLE (pairSnd (uv q)) = 0 then
    ArithmeticBits.one (BinaryNat.succ (modulus (ctx q))) else []

lemma unit_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : unit modulus ∈ FP := by
  have hu := mem_FP_comp (mem_FP_comp ctx_FP hm) BinaryNat.succ_mem_FP
  have ho := mem_FP_comp hu ArithmeticBits.one_mem_FP
  have ha := zero_FP (mem_FP_comp uv_FP pairFst_mem_FP)
  have hb := zero_FP (mem_FP_comp uv_FP pairSnd_mem_FP)
  exact mem_FP_of_eq ((ha.and hb).ite_mem_FP ho (constFn_mem_FP [])) (fun _ => rfl)

def rawSourceInput (L : Layout) (q : List Bool) :=
  let ia := BinaryNat.divMod (pair (idx q) (columnsCode L (ctx q)))
  pair (ctx q) (pair (pairFst ia) (pair (pairSnd ia) (pair (shift q) (uv q))))

def rawPaddingInput (L : Layout) (q : List Bool) :=
  pair (ctx q) (pair [] (pair (BinaryNat.sub (pair (idx q) (sourceCut L (ctx q)))) (pair (shift q) (uv q))))

lemma rawSourceInput_FP {L : Layout} (h : L.Controls) : rawSourceInput L ∈ FP := by
  have hc := mem_FP_comp ctx_FP (columnsCode_FP h)
  have hd := mem_FP_comp (mem_FP_pair idx_FP hc) BinaryNat.divMod_mem_FP
  exact mem_FP_of_eq (mem_FP_pair ctx_FP (mem_FP_pair (mem_FP_comp hd pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp hd pairSnd_mem_FP) (mem_FP_pair shift_FP uv_FP)))) (fun _ => rfl)

lemma rawPaddingInput_FP {L : Layout} (h : L.Controls) : rawPaddingInput L ∈ FP := by
  have hc := mem_FP_comp (f := ctx) (g := sourceCut L) ctx_FP (sourceCut_FP h)
  have hd := mem_FP_comp (mem_FP_pair idx_FP hc) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (mem_FP_pair ctx_FP (mem_FP_pair (constFn_mem_FP [])
    (mem_FP_pair hd (mem_FP_pair shift_FP uv_FP)))) (fun _ => rfl)

def isSource (L : Layout) (q : List Bool) : Prop :=
  Nat.fromBitsLE (idx q) < Nat.fromBitsLE (sourceCut L (ctx q))
instance (L : Layout) : DecidablePred (isSource L) := fun _ => inferInstanceAs (Decidable (_ < _))
lemma isSource_FP {L : Layout} (h : L.Controls) : FPPred (isSource L) :=
  BinaryNat.lt_fppred idx_FP (mem_FP_comp (f := ctx) (g := sourceCut L) ctx_FP (sourceCut_FP h))

def isPadding (L : Layout) (q : List Bool) : Prop :=
  total L (rawPaddingInput L q) ≠ L.level (ctx q) ∧
    Nat.fromBitsLE (idx q) - Nat.fromBitsLE (sourceCut L (ctx q)) = Nat.fromBitsLE (shift q)
instance (L : Layout) : DecidablePred (isPadding L) := fun _ => inferInstanceAs (Decidable (_ ∧ _))
lemma isPadding_FP {L : Layout} (h : L.Controls) : FPPred (isPadding L) := by
  have ha := FPPred.eq ((total_unary h).comp (rawPaddingInput_FP h)) (h.level.comp ctx_FP)
  have hc := mem_FP_comp (f := ctx) (g := sourceCut L) ctx_FP (sourceCut_FP h)
  have hd := mem_FP_comp (mem_FP_pair idx_FP hc) BinaryNat.sub_mem_FP
  have hb := binaryEq_FP hd shift_FP
  exact (ha.not.and hb).of_iff (fun q => by simp only [Function.comp_apply, BinaryNat.sub_pair, Nat.fromBitsLE_bits, isPadding])

def rawEntry (L : Layout) (modulus coefficient : List Bool → List Bool) (q : List Bool) :=
  if isSource L q then shifted L coefficient (rawSourceInput L q)
  else if isPadding L q then unit modulus q else []

lemma rawEntryEvaluator {L : Layout} (h : L.Controls)
    {modulus coefficient : List Bool → List Bool} (hm : modulus ∈ FP) (E : SpaceFunction coefficient) :
    SpaceFunction (rawEntry L modulus coefficient) := by
  have ES := (shiftedEvaluator h E).precompose (rawSourceInput L) (rawSourceInput_FP h)
  have EP := SpaceFunction.branch (fun q => decide (isPadding L q)) (isPadding_FP h).flag_mem_FP
    (SpaceFunction.ofFP _ (unit_FP hm)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have EB := SpaceFunction.branch (fun q => decide (isSource L q)) (isSource_FP h).flag_mem_FP ES EP
  exact EB.congr (funext fun q => by simp only [rawEntry, decide_eq_true_eq, Function.comp_apply])

def upperInput (L : Layout) (q : List Bool) :=
  pair (ctx q) (pair (idx q) (pair (BinaryNat.sub (pair (shift q) (rowCut L (ctx q)))) (uv q)))
def lowerInput (L : Layout) (q : List Bool) :=
  pair (ctx q) (pair (shift q) (pair (BinaryNat.sub (pair (idx q) (rowCut L (ctx q)))) (uv q)))
lemma upperInput_FP {L : Layout} (h : L.Controls) : upperInput L ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair shift_FP (mem_FP_comp (f := ctx) (g := rowCut L) ctx_FP (rowCut_FP h))) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (mem_FP_pair ctx_FP (mem_FP_pair idx_FP (mem_FP_pair hd uv_FP))) (fun _ => rfl)
lemma lowerInput_FP {L : Layout} (h : L.Controls) : lowerInput L ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair idx_FP (mem_FP_comp (f := ctx) (g := rowCut L) ctx_FP (rowCut_FP h))) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (mem_FP_pair ctx_FP (mem_FP_pair shift_FP (mem_FP_pair hd uv_FP))) (fun _ => rfl)

def top (L : Layout) (q : List Bool) := Nat.fromBitsLE (idx q) < Nat.fromBitsLE (rowCut L (ctx q))
def left (L : Layout) (q : List Bool) := Nat.fromBitsLE (shift q) < Nat.fromBitsLE (rowCut L (ctx q))
def diagonal (q : List Bool) := Nat.fromBitsLE (idx q) = Nat.fromBitsLE (shift q)
instance (L : Layout) : DecidablePred (top L) := fun _ => inferInstanceAs (Decidable (_ < _))
instance (L : Layout) : DecidablePred (left L) := fun _ => inferInstanceAs (Decidable (_ < _))
instance : DecidablePred diagonal := fun _ => inferInstanceAs (Decidable (_ = _))
lemma top_FP {L : Layout} (h : L.Controls) : FPPred (top L) :=
  BinaryNat.lt_fppred idx_FP (mem_FP_comp (f := ctx) (g := rowCut L) ctx_FP (rowCut_FP h))
lemma left_FP {L : Layout} (h : L.Controls) : FPPred (left L) :=
  BinaryNat.lt_fppred shift_FP (mem_FP_comp (f := ctx) (g := rowCut L) ctx_FP (rowCut_FP h))
lemma diagonal_FP : FPPred diagonal := binaryEq_FP idx_FP shift_FP

def negateEntry (modulus entry : List Bool → List Bool) (q : List Bool) :=
  ArithmeticBits.negate (pair (BinaryNat.succ (modulus (ctx q))) (entry q))
lemma negateEntryEvaluator {modulus entry : List Bool → List Bool} (hm : modulus ∈ FP)
    (E : SpaceFunction entry) : SpaceFunction (negateEntry modulus entry) := by
  let prepare := fun q => pair (BinaryNat.succ (modulus (ctx (pairFst q)))) (pairSnd q)
  have hm' := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hctx := mem_FP_comp ctx_FP hm'
  have hlift := mem_FP_comp pairFst_mem_FP hctx
  have hp : prepare ∈ FP := mem_FP_of_eq (mem_FP_pair hlift pairSnd_mem_FP) (fun _ => rfl)
  exact (E.withInput.postcompose (ArithmeticBits.negate ∘ prepare)
    (mem_FP_comp hp ArithmeticBits.negate_mem_FP)).congr
      (by funext q; simp only [Function.comp_apply, prepare, pairFst_pair, pairSnd_pair, negateEntry])

def blockEntry (L : Layout) (modulus coefficient : List Bool → List Bool) (q : List Bool) :=
  if top L q then
    if left L q then (if diagonal q then unit modulus q else [])
    else rawEntry L modulus coefficient (upperInput L q)
  else if left L q then negateEntry modulus (rawEntry L modulus coefficient ∘ lowerInput L) q else []

lemma blockEntryEvaluator {L : Layout} (h : L.Controls)
    {modulus coefficient : List Bool → List Bool} (hm : modulus ∈ FP) (E : SpaceFunction coefficient) :
    SpaceFunction (blockEntry L modulus coefficient) := by
  have ER := rawEntryEvaluator h hm E
  have EU := ER.precompose (upperInput L) (upperInput_FP h)
  have EL := ER.precompose (lowerInput L) (lowerInput_FP h)
  have EN := negateEntryEvaluator hm EL
  have E0 := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have EI := SpaceFunction.branch (fun q => decide (diagonal q)) diagonal_FP.flag_mem_FP
    (SpaceFunction.ofFP _ (unit_FP hm)) E0
  have ET := SpaceFunction.branch (fun q => decide (left L q)) (left_FP h).flag_mem_FP EI EU
  have EB := SpaceFunction.branch (fun q => decide (left L q)) (left_FP h).flag_mem_FP EN E0
  have EA := SpaceFunction.branch (fun q => decide (top L q)) (top_FP h).flag_mem_FP ET EB
  exact EA.congr (funext fun q => by simp only [blockEntry, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.MacaulayFullBoxBits
