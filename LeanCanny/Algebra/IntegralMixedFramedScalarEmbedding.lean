/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot
/-! # A native injection of raw scalar digits into the actual full tuple

The map selects raw scalar columns. Bank weights are applied later by the
existing representative, so powered quotients are never injected as variables.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedScalarEmbedding
open IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryScript (Instruction Index)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedBankSnapshotBits (atKey)
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical

private theorem old_injective {n B : ℕ} {P : SpatialSource n} {ι : Type} (c : Command P B) :
    Function.Injective (old c : ι→NextIndex ι c) :=by
  cases c <;> intro a b H <;> cases H <;> rfl

private theorem fresh_ne_old {n B : ℕ} {P : SpatialSource n} {ι : Type} (c : Command P B) (i : ι) :
    fresh c≠old c i :=by cases c <;> intro H <;> cases H

theorem scalarSlot_injective {n B : ℕ} (cs : List (Instruction n B)) : Function.Injective (scalarSlot cs) :=by
  induction cs with
  | nil =>intro i;exact Fin.elim0 i
  | cons c cs ih =>
    intro i j H
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero =>rfl
      | succ j =>exact (fresh_ne_old c.command (scalarSlot cs j) H).elim
    | succ i =>
      induction j using Fin.cases with
      | zero =>exact (fresh_ne_old c.command (scalarSlot cs i) H.symm).elim
      | succ j =>exact congrArg Fin.succ (ih ((old_injective c.command) H))

noncomputable def scalarMap (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : Fin (atKey P D H key).count→Fin (arity (commands P D key)) :=
  enumerate (commands P D key) ∘ ((family P D H).state key).sampler.scalar

theorem scalarMap_injective (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) : Function.Injective (scalarMap P D H key) :=by
  apply (enumerate (commands P D key)).injective.comp
  rw [family_scalar]
  exact scalarSlot_injective _

def index (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool→List Bool) (q : List Bool) :=
  BinaryNatCode.encode (scalarColumn P T (pair (key (pairFst q)) (pairSnd q)))

theorem index_FP (P : Parameters) (a : Access P) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedHeaderTablesBits.Access T) (key : List Bool→List Bool) (hk : key∈FP) : index P T key∈FP :=
  (BinaryFn.ofUnary ((scalarColumn_unary P a T hT).comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) pairSnd_mem_FP))).bits_mem_FP

theorem index_map (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool→List Bool) (c : List Bool) (i : Fin (atKey P D H (key c)).count) :
    index P T key (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (scalarMap P D H (key c) i).val :=by
  unfold index
  simp only [pairFst_pair,pairSnd_pair]
  exact congrArg BinaryNatCode.encode (scalarColumn_actual P D H T hr (key c) i)

end LeanCanny.Algebra.IntegralMixedFramedScalarEmbedding
