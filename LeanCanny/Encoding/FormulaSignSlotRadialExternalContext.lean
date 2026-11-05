/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratum
public import LeanCanny.Encoding.ImplicitSourceGramGrid
/-! # External own-grid providers retain the old spatial source

The old candidate label is an independent component target. It is never
identified with the own external grid word stored in the metadata.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def metadata (ctx : List Bool) := pairSnd ctx
def external (ctx : List Bool) : Prop := pairFst (metadata ctx)=[true]
def gridContext (ctx : List Bool) := pairFst (pairSnd (metadata ctx))
def sideCode (ctx : List Bool) := pairFst (pairSnd (pairSnd (metadata ctx)))
def side (ctx : List Bool) : Bool := decide (sideCode ctx=[true])
def sideNat (ctx : List Bool) := if sideCode ctx=[true] then 1 else 0
def ownWord (ctx : List Bool) := pairSnd (pairSnd (pairSnd (metadata ctx)))
def original (ctx : List Bool) := pairFst (pairFst ctx)
noncomputable def number (ctx : List Bool) := CanonicalAuxiliaryCandidateCover.dimension (original ctx)
def slot (ctx : List Bool) (i : ℕ) := 4*i+sideNat ctx
def slotQuery (q : List Bool) := pair (gridContext (pairFst q))
  (BinaryNatCode.encode (slot (pairFst q) (Nat.fromBitsLE (pairSnd q))))

noncomputable def packet (H : List Bool) (K : ℕ) (Gamma oldLabel : List Bool) (s : Bool) (w : List Bool) :=
  pair (pair (FormulaSignSlotRadialJointLayout.source s H) oldLabel)
    (pair [true] (pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) (pair [s] w)))

theorem gridContext_FP : gridContext ∈ FP := by polytime [gridContext,metadata]
theorem sideCode_FP : sideCode ∈ FP := by polytime [sideCode,metadata]
theorem ownWord_FP : ownWord ∈ FP := by polytime [ownWord,metadata]
theorem original_FP : original ∈ FP := by polytime [original]
theorem external_FP : FPPred external := stringEq_fppred
  (by polytime [metadata]) (constFn_mem_FP [true])
theorem sideNat_binary : BinaryFn sideNat := BinaryFn.ite
  (stringEq_fppred sideCode_FP (constFn_mem_FP [true])) (BinaryFn.const 1) (BinaryFn.const 0)
theorem number_unary : UnaryFn number := CanonicalAuxiliaryCandidateCover.dimension_unary.comp original_FP
theorem slotQuery_FP : slotQuery ∈ FP := mem_FP_pair
  (mem_FP_comp (f := pairFst) (g := gridContext) pairFst_mem_FP gridContext_FP)
  (((BinaryFn.const 4).mul (BinaryFn.fromBits pairSnd_mem_FP)).add (sideNat_binary.comp pairFst_mem_FP)).bits_mem_FP

theorem external_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    external (packet H K Gamma label s w) := by
  simp only [external,metadata,packet,pairSnd_pair,pairFst_pair]
theorem original_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    original (packet H K Gamma label s w)=FormulaSignSlotRadialJointLayout.source s H := by
  simp only [original,packet,pairFst_pair]
theorem gridContext_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    gridContext (packet H K Gamma label s w)=pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma := by
  simp only [gridContext,metadata,packet,pairFst_pair,pairSnd_pair]
theorem ownWord_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    ownWord (packet H K Gamma label s w)=w := by
  simp only [ownWord,metadata,packet,pairSnd_pair]
theorem sideNat_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    sideNat (packet H K Gamma label s w)=if s then 1 else 0 := by
  cases s <;> simp [sideNat,sideCode,metadata,packet]
theorem number_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) :
    number (packet H K Gamma label s w)=FormulaSignSlotRadialJointLayout.circleCount s H := by
  rw [number,original_packet]
  rfl
theorem slot_packet (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool) (i : ℕ) :
    slot (packet H K Gamma label s w) i=FormulaSignSlotRadialJointLayout.column (if s then 1 else 0) i := by
  rw [slot,sideNat_packet]
  rfl

theorem slot_lt (H : List Bool) (s : Bool) (i : Fin (FormulaSignSlotRadialJointLayout.circleCount s H)) :
    FormulaSignSlotRadialJointLayout.column (if s then 1 else 0) i.val<
      FormulaSignSlotRadialJointLayout.dimension H+1 := by
  exact (FormulaSignSlotRadialJointLayout.column_lt H _ _ (by cases s <;> decide)
    (i.isLt.trans_le (FormulaSignSlotRadialJointLayout.circle_lt_slots s H))).trans (Nat.lt_succ_self _)

end LeanCanny.Encoding.FormulaSignSlotRadialExternalContext
