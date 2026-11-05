/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedScan
/-! # The accepted seed point is exactly the constructed critical point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem geometric_congr (BB : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (c d w z : List Bool) (hc : c=d) (hw : w=z)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) c w)
    (hd : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) d z)
    (a b : ℕ) (hab : a=b) :
    HEq (IntegralFramedPhysicalCompanionPoint.geometricPoint BB TT c w hv a)
      (IntegralFramedPhysicalCompanionPoint.geometricPoint BB TT d z hd b) := by
  cases hc
  cases hw
  cases hab
  rfl

private theorem env_congr (BB : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents BB.parameters BB.plan BB.data TT)
    (c d w z : List Bool) (hc : c=d) (hw : w=z)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) c w)
    (hd : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) d z) :
    IntegralFramedPhysicalBankTerm.env BB TT hr c w hv=IntegralFramedPhysicalBankTerm.env BB TT hr d z hd := by
  cases hc
  cases hw
  rfl

private theorem cast_function {m n : ℕ} (he : m=n) (p : Fin n→ℝ) :
    HEq (fun i : Fin m=>p (Fin.cast he i)) p := by cases he;rfl

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source

theorem anchor_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.anchor
    (FormulaSignSlotRadialProviderAtomic.dimension (packet c w))
    (FormulaSignSlotRadialProviderAtomic.initial (packet c w)) (packet c w)=
      FormulaSignSlotRadialProviderRecordPlan.count (root c) := by
  rw [dimension_packet,initial_packet,←count_root]
  have HZ : IntegralMixedRoadmapAtomic.depth (packet c w)=0 := depth_packet c w
  exact IntegralMixedRoadmapAtomic.seed_anchor _ _ _ HZ

theorem nativePoint_heq (c : List Bool) (p : Fin ((P).ambient (root c)+1)→ℝ) : HEq (nativePoint c p) p :=
  cast_function (congrArg (·+1) (native_dimension c)) p

theorem WordReceipt.point_packet {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (hV : FormulaSignSlotRadialProviderAtomic.Valid (packet c W.word)) :
    HEq (FormulaSignSlotRadialProviderAtomic.point (packet c W.word) hV) p := by
  have HC : FormulaSignSlotRadialProviderAtomic.context (packet c W.word)=seedContext c := context_packet c W.word
  have H := geometric_congr B T (FormulaSignSlotRadialProviderAtomic.context (packet c W.word)) (seedContext c)
    (FormulaSignSlotRadialProviderAtomic.word (packet c W.word)) W.word HC (word_packet c W.word)
    (FormulaSignSlotRadialProviderAtomic.full_valid (packet c W.word) hV) W.valid
    (FormulaSignSlotRadialProviderAtomic.anchor (FormulaSignSlotRadialProviderAtomic.dimension (packet c W.word))
      (FormulaSignSlotRadialProviderAtomic.initial (packet c W.word)) (packet c W.word))
    (FormulaSignSlotRadialProviderRecordPlan.count (root c)) (anchor_packet c W.word)
  have HH : HEq (FormulaSignSlotRadialProviderAtomic.point (packet c W.word) hV)
      (FormulaSignSlotRadialProviderAtomic.geometricPoint (seedContext c) W.word W.valid
        (FormulaSignSlotRadialProviderRecordPlan.count (root c))) := H
  have HG : FormulaSignSlotRadialProviderAtomic.geometricPoint (seedContext c) W.word W.valid
      (FormulaSignSlotRadialProviderRecordPlan.count (root c))=nativePoint c p := by
    simpa only [Nat.add_zero] using W.geometric_point 0 (by have HL := seed_count_lower c;omega)
  exact HH.trans ((heq_of_eq HG).trans (nativePoint_heq c p))

theorem WordReceipt.field_packet {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (hV : FormulaSignSlotRadialProviderAtomic.Valid (packet c W.word))
    (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.count (root c)) :
    FormulaSignSlotRadialProviderAtomic.field (packet c W.word) hV b=v b := by
  have HC : FormulaSignSlotRadialProviderAtomic.context (packet c W.word)=seedContext c := context_packet c W.word
  have H := env_congr B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context (packet c W.word)) (seedContext c)
    (FormulaSignSlotRadialProviderAtomic.word (packet c W.word)) W.word HC (word_packet c W.word)
    (FormulaSignSlotRadialProviderAtomic.full_valid (packet c W.word) hV) W.valid
  exact (congrFun H b).trans (W.prelude_field b hb)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
