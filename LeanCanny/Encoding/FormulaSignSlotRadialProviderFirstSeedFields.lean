/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedMetadata
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # All fields of the same provider seed word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_lists {n S bwidth : ℕ} {Q : SpatialSource n}
    (x : State Q S bwidth 0 (Fin 0)) (cs ds : List (Instruction n bwidth))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd := by cases he;rfl

private theorem field_observation_generic (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (r : List Bool) (hr : pairFst (B.key c)=r)
    (hc : prefixLength B.parameters (B.key c)=(B.plan.rules r).length)
    (u : ℕ→ℝ) (HJ : ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val)
    (b : ℕ) (hb : b<(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count) :
    IntegralFramedPhysicalBankTerm.env B T hT c w hw b=
      (ofCommands (initial B.parameters B.plan r) (B.plan.rules r)
        (by have H := B.plan.room r;omega)).point u
          ((family B.parameters B.plan B.data).birth (B.key c)-1-b) := by
  have HB : b<(family B.parameters B.plan B.data).birth (B.key c) := hb
  rw [IntegralFramedPhysicalBankTerm.env_chronological B T hT c w hw b hb]
  have HP := IntegralFramedPhysicalSquare.point_of_joint_natural B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key B.positive c w hw u HJ
    ⟨(family B.parameters B.plan B.data).birth (B.key c)-1-b,by have H := B.positive c;omega⟩
  refine HP.trans ?_
  apply congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point u _)
  cases hr
  apply observation_lists
  unfold IntegralMixedFramedHistoryFamilyBits.commands
  rw [hc,paddedPast_full]

structure BankWord (BB : IntegralFramedBankQuery.Bank) (cc : List Bool) (u : ℕ→ℝ) where
  word : List Bool
  valid : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) cc word
  width : word.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input BB) cc
  joint : ∀i : Fin (IntegralFramedPhysicalSquare.count BB.parameters BB.plan (BB.key cc)),
    IntegralFramedPhysicalSquare.joint BB.parameters BB.plan BB.data BB.nodes BB.factor BB.seed BB.bounds
      BB.key BB.positive cc word valid i=u i.val

private theorem count_birth (BB : IntegralFramedBankQuery.Bank) (cc : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey BB.parameters BB.plan BB.data (BB.key cc)).count=
      (family BB.parameters BB.plan BB.data).birth (BB.key cc) := rfl

private theorem reverse_selection (d m tail a : ℕ)
    (ha : a<(IntegralMixedChronologicalSeedProgram.selections d m tail).length) :
    ((IntegralMixedChronologicalSeedProgram.selections d m tail).get
      ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩).val.val=
      IntegralMixedRoadmapSeedMetadata.selected d a := by
  have H := IntegralMixedChronologicalSeedProgram.selection_coordinate d m tail
    ⟨(IntegralMixedChronologicalSeedProgram.selections d m tail).length-1-a,by omega⟩
  have HL := IntegralMixedChronologicalSeedProgram.selections_length d m tail
  simp only [List.get_eq_getElem]
  rw [H]
  simp only [HL]
  unfold IntegralMixedRoadmapSeedMetadata.selected
  split_ifs <;> omega

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "BP" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "BD" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source observation IntegralMixedFramedHistoryFamilyBits.family

structure WordReceipt (c : List Bool) (v : ℕ→ℝ) (p : Fin ((P).ambient (root c)+1)→ℝ) where
  tuple : ℕ→ℝ
  roots : (observation c).Roots tuple
  blocks : ∀k : Fin (selections c).length,∀i : Fin ((P).ambient (root c)+1),
    tuple (IntegralMixedFramedPhysicalIndex.arity (older c)+(2*(P).ambient (root c)+4)*((selections c).length-1-k.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap (root c)+1) (2^(P).width (root c))
        ((older c).length+((selections c).length-1-k.val))=p i
  values : ∀i : Fin ((older c).length+(selections c).length),(observation c).point tuple i.val=
    IntegralMixedPointCompanion.values p
      (fun j : Fin (older c).length=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j.val)) (selections c) i
  sample : BankWord B (seedContext c) tuple

abbrev WordReceipt.word {c v p} (W : WordReceipt c v p) := W.sample.word
abbrev WordReceipt.valid {c v p} (W : WordReceipt c v p) := W.sample.valid
abbrev WordReceipt.width {c v p} (W : WordReceipt c v p) := W.sample.width
abbrev WordReceipt.joint {c v p} (W : WordReceipt c v p) := W.sample.joint

theorem exists_word (c : List Bool) (v : ℕ→ℝ)
    (hv : ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0)
    (p : Fin ((P).ambient (root c)+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).low
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).leading
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i.val≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).low
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).leading
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root c)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    Nonempty (WordReceipt c v p) := by
  obtain ⟨u,hu,hB,hV⟩ := exists_tuple c v hv p hp hg
  obtain ⟨w,hw,hl,hj⟩ := sample_tuple c u hu
  exact ⟨⟨u,hu,hB,hV,⟨w,hw,hl,hj⟩⟩⟩

theorem selections_count (c : List Bool) : (selections c).length=IntegralMixedCausalRecordPlanBits.count (root c) :=
  (codes_length c).symm.trans (codes_count c)
theorem full_birth (c : List Bool) :
    (family BP BD (B).data).birth ((B).key (seedContext c))=(older c).length+(selections c).length := by
  have H := FormulaSignSlotRadialProviderRecordPlan.bank_count (seedContext c)
  rw [seedContext,pairFst_pair] at H
  have HL := congrArg₂ (fun a b : ℕ=>a+b) (older_length c).symm (selections_count c).symm
  exact (count_birth B (seedContext c)).symm.trans (H.trans HL)

theorem WordReceipt.field_observation {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (b : ℕ) (hb : b<(older c).length+(selections c).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid b=
      (observation c).point W.tuple ((older c).length+(selections c).length-1-b) := by
  have HC : b<(IntegralMixedFramedBankSnapshotBits.atKey BP BD (B).data ((B).key (seedContext c))).count := by
    rw [count_birth,full_birth]
    exact hb
  have HH := field_observation_generic B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (seedContext c) W.word W.valid (root c) (seed_key_root c) (full_prefix c) W.tuple W.joint b HC
  rw [full_birth] at HH
  exact HH.trans (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>
    O.point W.tuple ((older c).length+(selections c).length-1-b)) (sampling_observation c))

theorem WordReceipt.field_values {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (b : ℕ) (hb : b<(older c).length+(selections c).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid b=
      IntegralMixedPointCompanion.values p
        (fun j : Fin (older c).length=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j.val))
        (selections c) ⟨(older c).length+(selections c).length-1-b,by omega⟩ :=
  (W.field_observation b hb).trans (W.values ⟨_,by omega⟩)

theorem WordReceipt.prelude_field {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.count (root c)) :
    FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid b=v b := by
  have HL : b<(older c).length := by rw [older_length];exact hb
  have HH := W.field_values b (by omega)
  let j : Fin (older c).length := ⟨(older c).length-1-b,by omega⟩
  have HE : (older c).length+(selections c).length-1-b=(selections c).length+j.val := by dsimp only [j];omega
  simp only [HE] at HH
  have HG := IntegralMixedPointCompanion.values_old p
    (fun k : Fin (older c).length=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-k.val)) (selections c) j
  refine HH.trans (HG.trans ?_)
  apply congrArg v
  have HN := older_length c
  dsimp only [j]
  omega

theorem WordReceipt.critical_field {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (a : ℕ) (ha : a<IntegralMixedCausalRecordPlanBits.count (root c)) :
    FormulaSignSlotRadialProviderAtomic.bankField (seedContext c) W.word W.valid
      (FormulaSignSlotRadialProviderRecordPlan.count (root c)+a)=
      p ⟨IntegralMixedRoadmapSeedMetadata.selected ((P).ambient (root c)) a,IntegralMixedRoadmapSeedMetadata.selected_lt _ _⟩ := by
  have HA : a<(selections c).length := by rw [selections_count];exact ha
  have HH := W.field_values ((older c).length+a) (by omega)
  have HE : (older c).length+(selections c).length-1-((older c).length+a)=(selections c).length-1-a := by omega
  simp only [HE] at HH
  rw [←older_length]
  let k : Fin (selections c).length := ⟨(selections c).length-1-a,by omega⟩
  have HG := IntegralMixedPointCompanion.values_get p
    (fun j : Fin (older c).length=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j.val)) (selections c) k
  refine HH.trans (HG.trans ?_)
  apply congrArg p
  apply Fin.ext
  dsimp only [k]
  unfold selections at HA ⊢
  exact reverse_selection _ _ _ a HA

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
