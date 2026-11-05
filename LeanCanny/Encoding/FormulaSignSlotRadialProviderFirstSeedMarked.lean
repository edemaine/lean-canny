/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedScan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedLanguage
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical
/-! # Constructed seed words preserve the genuine marked endpoint -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem env_congr (BB : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents BB.parameters BB.plan BB.data TT)
    (c d w z : List Bool) (hc : c=d) (hw : w=z)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) c w)
    (hd : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) d z) :
    IntegralFramedPhysicalBankTerm.env BB TT hr c w hv=IntegralFramedPhysicalBankTerm.env BB TT hr d z hd := by
  cases hc
  cases hw
  rfl

private theorem valid_congr (S : SquareSampleInput.Inputs) (c d w z : List Bool) (hc : c=d) (hw : w=z) :
    SquareSampleCompleteVertices.Valid S c w→SquareSampleCompleteVertices.Valid S d z := by
  cases hc
  cases hw
  exact id

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
open FormulaSignSlotRadialProviderMarkedGeometry (number radius equation allowance)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source FormulaSignSlotRadialProviderMarkedGeometry.equation
  CanonicalAuxiliaryCandidateCover.equation LeanCanny.ETR.Term.finitePolynomial

theorem WordReceipt.full_valid_packet {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) : FormulaSignSlotRadialProviderAtomic.FullValid (packet c W.word) := by
  have HC : FormulaSignSlotRadialProviderAtomic.context (packet c W.word)=seedContext c := context_packet c W.word
  exact valid_congr FormulaSignSlotRadialProviderAtomic.input (seedContext c)
    (FormulaSignSlotRadialProviderAtomic.context (packet c W.word)) W.word
    (FormulaSignSlotRadialProviderAtomic.word (packet c W.word)) HC.symm (word_packet c W.word).symm W.valid

theorem WordReceipt.values_packet {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) :
    FormulaSignSlotRadialProviderAtomic.MarkedLanguage.values (packet c W.word) W.full_valid_packet=
      FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid := by
  exact env_congr B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context (packet c W.word)) (seedContext c)
    (FormulaSignSlotRadialProviderAtomic.word (packet c W.word)) W.word
    (context_packet c W.word) (word_packet c W.word) W.full_valid_packet W.valid

theorem WordReceipt.marked {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p)
    (hroots : ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0)
    (hr : (BoundedRegularSource.polynomial (equation c) (allowance c) (allowance c) (radius c)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0)
    (hm : (BoundedRegularSource.markPolynomial (equation c) (radius c)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0) :
    FormulaSignSlotRadialProviderAtomic.Marked.Holds (packet c W.word) := by
  have HF : ∀i<number c+8,
      FormulaSignSlotRadialProviderAtomic.MarkedLanguage.values (packet c W.word) W.full_valid_packet i=v i := by
    intro i hi
    rw [W.values_packet]
    exact W.prelude_field i (by rw [count_root];exact hi)
  have HV : (fun i : Fin (number c+4)=>
      FormulaSignSlotRadialProviderAtomic.MarkedLanguage.values (packet c W.word) W.full_valid_packet i.val)=
      fun i=>v i.val := funext (fun i=>HF i.val (by omega))
  apply FormulaSignSlotRadialProviderAtomic.MarkedLanguage.holds_of_equations (packet c W.word) W.full_valid_packet
  · rw [provider_packet]
    intro i hi
    have HI : i<FormulaSignSlotRadialProviderRecordPlan.count (root c) := by rw [count_root];exact hi
    exact (congrArg (fun x : ℝ=>(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) x) (HF i hi)).trans (hroots i HI)
  · rw [provider_packet]
    exact (congrArg (fun x : Fin (number c+4)→ℝ=>
      (BoundedRegularSource.polynomial (equation c) (allowance c) (allowance c) (radius c)).eval₂
        (Int.castRingHom ℝ) x) HV).trans hr
  · rw [provider_packet]
    exact (congrArg (fun x : Fin (number c+4)→ℝ=>
      (BoundedRegularSource.markPolynomial (equation c) (radius c)).eval₂ (Int.castRingHom ℝ) x) HV).trans hm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
