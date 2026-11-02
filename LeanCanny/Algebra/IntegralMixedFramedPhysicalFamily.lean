/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeaders
public import LeanCanny.Algebra.IntegralMixedFullPhysicalFamily

/-! # Physical and virtual critical metadata over the same changing-source bank

Physical births use their actual creating critical rule. Other instructions
use the existing offset-zero default. All numeric metadata comes from the
same represented command headers; original scalar coefficient costs remain
separate from these syntactic controls.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedCommandHeaderBits (Header)
open scoped Classical

noncomputable def rule (P : Parameters) (D : Plan P) (key : List Bool) :
    IntegralMixedHistory.CriticalRule (P.ambient (pairFst key)) :=
  match (instruction P D key).command with
  | .critical r => r
  | _ => IntegralMixedFullPhysicalBits.defaultRule _

noncomputable def family (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : IntegralMixedPhysicalCriticalBits.Family where
  ambient := (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient
  cap := (IntegralMixedFramedHistoryFamilyBits.family P D H).cap
  width := (IntegralMixedFramedHistoryFamilyBits.family P D H).width
  birth := (IntegralMixedFramedHistoryFamilyBits.family P D H).birth
  physical := (IntegralMixedFramedHistoryFamilyBits.family P D H).physical
  spatial := (IntegralMixedFramedHistoryFamilyBits.family P D H).spatial
  state := (IntegralMixedFramedHistoryFamilyBits.family P D H).state
  birth_bound := (IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound
  rule := rule P D

theorem physical_state (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (family P D H).state key = (IntegralMixedFramedHistoryFamilyBits.family P D H).state key := rfl

theorem canonical (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    IntegralMixedHistory.Canonical ((family P D H).state key) :=
  IntegralMixedFramedHistoryFamilyBits.family_canonical P D H key

theorem rule_critical (P : Parameters) (D : Plan P) (key : List Bool)
    (r : IntegralMixedHistory.CriticalRule (P.ambient (pairFst key)))
    (hc : (instruction P D key).command = .critical r) : rule P D key = r := by
  unfold rule
  rw [hc]

private theorem offset_header (P : Parameters) (D : Plan P) (key : List Bool) :
    (rule P D key).offset.val =
      if (IntegralMixedCommandHeaderBits.command (instruction P D key).command).context = 1
      then (IntegralMixedCommandHeaderBits.command (instruction P D key).command).offset else 0 := by
  unfold rule
  cases hc : (instruction P D key).command with
  | integer => rfl
  | critical => rfl
  | cut r k => cases k <;> rfl

private theorem objective_header (P : Parameters) (D : Plan P) (key : List Bool) :
    (rule P D key).objective =
      if (IntegralMixedCommandHeaderBits.command (instruction P D key).command).context = 1
      then (IntegralMixedCommandHeaderBits.command (instruction P D key).command).objective else 0 := by
  unfold rule
  cases hc : (instruction P D key).command with
  | integer => rfl
  | critical => rfl
  | cut r k => cases k <;> rfl

theorem offset_unary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    UnaryFn (fun key => (rule P D key).offset.val) := by
  have HS := IntegralMixedHeaderTablesBits.producer_readers P a T ht
  have HO := BinaryFn.ite (HS.context.eq (BinaryFn.const 1)) HS.offset (BinaryFn.const 0)
  have HB : BinaryFn (fun key => (rule P D key).offset.val) := HO.of_eq (fun key => by
    rw [IntegralMixedFramedHeaderBits.producer_eq P D H T hr key]
    exact (offset_header P D key).symm)
  have HU := UnaryFn.fromBitsLE_min HB.bits_mem_FP (a.ambient.comp pairFst_mem_FP)
  refine HU.of_eq (fun key => ?_)
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (Nat.le_of_lt_succ (rule P D key).offset.isLt)

theorem objective_binary (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    BinaryFn (fun key => (rule P D key).objective) := by
  have HS := IntegralMixedHeaderTablesBits.producer_readers P a T ht
  have HO := BinaryFn.ite (HS.context.eq (BinaryFn.const 1)) HS.objective (BinaryFn.const 0)
  exact HO.of_eq (fun key => by
    rw [IntegralMixedFramedHeaderBits.producer_eq P D H T hr key]
    exact (objective_header P D key).symm)

theorem inputMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    IntegralMixedPhysicalQueryBits.InputMetadata (family P D H) where
  ambient := a.ambient.comp pairFst_mem_FP
  birth := (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq
    (fun key => (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)
  width := a.width.comp pairFst_mem_FP
  offset := offset_unary P a D H T ht hr
  degree := by
    have HD : BinaryFn (fun key => P.degree (pairFst key)) := a.degree.comp pairFst_mem_FP
    exact HD.of_eq (fun key => (H.degree_eq key).symm)
  objective := objective_binary P a D H T ht hr

theorem virtualInputMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H) where
  ambient := a.ambient.comp pairFst_mem_FP
  birth := (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq
    (fun key => (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)
  width := a.width.comp pairFst_mem_FP
  offset := IntegralMixedFramedHeaderBits.offset_unary P a D H T ht hr
  degree := by
    have HD : BinaryFn (fun key => P.degree (pairFst key)) := a.degree.comp pairFst_mem_FP
    exact HD.of_eq (fun key => (H.degree_eq key).symm)
  objective := IntegralMixedFramedHeaderBits.objective_binary P a D H T ht hr

theorem geometry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralMixedPhysicalCaps.RootGeometry P (family P D H) where
  ambient q := by
    change P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) ≤ _
    rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair]
  degree q := by
    have HE := H.degree_eq (IntegralMixedPhysicalTaskBits.saved P q)
    have HR : pairFst (IntegralMixedPhysicalTaskBits.saved P q) = RankedHistoryTask.root q := pairFst_pair _ _
    exact (HE.trans (congrArg P.degree HR)).le
  sourceWidth q := by
    have HE := H.sourceWidth (IntegralMixedPhysicalTaskBits.saved P q)
    have HR : pairFst (IntegralMixedPhysicalTaskBits.saved P q) = RankedHistoryTask.root q := pairFst_pair _ _
    exact HE.trans_eq (congrArg P.sourceWidth HR)
  width q := by
    change P.width (pairFst (IntegralMixedPhysicalTaskBits.saved P q)) = _
    rw [IntegralMixedPhysicalTaskBits.saved, pairFst_pair]
  birth q := by
    rw [show (family P D H).birth (IntegralMixedPhysicalTaskBits.saved P q) =
      IntegralMixedFullHistoryFamilyBits.prefixLength P (IntegralMixedPhysicalTaskBits.saved P q) from
        IntegralMixedFramedHistoryFamilyBits.family_birth P D H _]
    simp only [IntegralMixedFullHistoryFamilyBits.prefixLength, IntegralMixedPhysicalTaskBits.saved,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (min_le_right _ _)

theorem source_polynomial (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hc : get P .slot13 q % ((family P D H).ambient (IntegralMixedPhysicalTaskBits.saved P q) -
        (rule P D (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1) =
      (rule P D (IntegralMixedPhysicalTaskBits.saved P q)).coordinate %
        ((family P D H).ambient (IntegralMixedPhysicalTaskBits.saved P q) -
          (rule P D (IntegralMixedPhysicalTaskBits.saved P q)).offset.val + 1)) :
    (IntegralMixedPhysicalTaskBits.source P (family P D H)).annihilator q =
      IntegralMixedHistory.criticalPolynomial ((family P D H).state (IntegralMixedPhysicalTaskBits.saved P q))
        ((family P D H).birth_bound (IntegralMixedPhysicalTaskBits.saved P q))
        (rule P D (IntegralMixedPhysicalTaskBits.saved P q)) := by
  apply IntegralMixedPhysicalCriticalBits.critical_polynomial
  exact hc

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBits
