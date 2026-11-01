/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptSelectedFP
public import LeanCanny.Algebra.IntegralCriticalScriptHeight

/-! # Common denominators at actual creating sources

Chronological primitive selector metadata identifies each selected older
scale. The native truncated denominator pass and modular product compute
the common denominator of the creating polynomial, without an algebraic
coefficient or retained-height evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalFlatCompanionBits
set_option backward.isDefEq.respectTransparency false

variable (F : IntegralCriticalScriptGeneratorBits.Queries)

noncomputable def selector (c : List Bool) (i : ℕ) : ℕ :=
  IntegralCriticalScriptFP.selector (metadata F) c (older (F.rules c) (F.selected c)).length i

theorem selector_eq (c : List Bool) (i : Fin (F.ambient c + 1)) :
    selector F c i.val = (chosen (F.rules c) (F.selected c)).selected i := by
  have HC : (F.rules c).reverse[(older (F.rules c) (F.selected c)).length]? =
      some (chosen (F.rules c) (F.selected c)) := IntegralCriticalScriptSelectedFP.commandAt_creating F c
  unfold selector IntegralCriticalScriptFP.selector IntegralCriticalScriptFP.commandAt metadata
  rw [HC]
  dsimp only
  rw [dite_eq_left i.isLt]

theorem selector_binary (h : IntegralCriticalScriptGeneratorBits.Controls F)
    (a : IntegralCriticalScriptFP.Access (metadata F)) :
    BinaryFn (fun p => selector F (pairFst p) (Nat.fromBitsLE (pairSnd p))) := by
  have HQ := mem_FP_pair
    (mem_FP_comp pairFst_mem_FP (IntegralCriticalScriptSelectedFP.packet_FP F h)) pairSnd_mem_FP
  apply BinaryFn.of_eq (a.selector.comp HQ)
  intro p
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
    IntegralCriticalScriptSelectedFP.cursor_packet]
  have HP : pairFst (IntegralCriticalScriptSelectedFP.packet F (pairFst p)) = pairFst p := by
    simp only [IntegralCriticalScriptSelectedFP.packet, BoundedFold.packet, pairFst_pair]
  rw [HP]
  rfl

noncomputable def queries : IntegralCriticalScriptHeightBits.Queries where
  cap := F.cap
  width := F.width
  ambient := F.ambient
  sourceWidth := F.sourceWidth
  degreeBound := F.degreeBound
  height := F.height
  rules := F.rules
  length_le := F.length_le
  scalar_bound := F.scalar_bound
  prefixLength c := (older (F.rules c) (F.selected c)).length
  selector := selector F
  coordinate _ := 0
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero
  row _c := ⟨0, pow_pos (Nat.two_pow_pos _) _⟩
  col _c := ⟨0, pow_pos (Nat.two_pow_pos _) _⟩

theorem controls (h : IntegralCriticalScriptGeneratorBits.Controls F)
    (a : IntegralCriticalScriptFP.Access (metadata F)) : IntegralCriticalScriptHeightBits.Controls (queries F) where
  ambient := h.ambient
  prefixLength := BinaryFn.ofUnary (IntegralCriticalScriptGeneratorBits.arity_unary F h)
  selector := selector_binary F h a
  coordinate := BinaryFn.const 0
  modulus := h.modulus
  row := BinaryFn.const 0
  col := BinaryFn.const 0

theorem denominator_FP (h : IntegralCriticalScriptGeneratorBits.Controls F)
    (a : IntegralCriticalScriptFP.Access (metadata F)) :
    (fun c => residueBits (CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient c + 1) => IntegralCriticalScriptHeightBits.scales (queries F) c i.val) : ZMod (F.modulus c))) ∈ FP :=
  IntegralCriticalScriptHeightBits.denominator_FP (queries F) (controls F h a)
    (IntegralCriticalScriptFP.access (metadata F) a)

noncomputable def atSource (c : List Bool) : IntegralHistoryCriticalBits.Family :=
  IntegralCriticalScript.family
    (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (older (F.rules c) (F.selected c)).length)
    (by rw [IntegralCriticalScriptQueryBits.past_older]; exact older_bound _ (F.length_le c) _)
    (chosen (F.rules c) (F.selected c))

theorem atSource_eq (c : List Bool) : atSource F c = IntegralCriticalScriptGeneratorBits.birthSource F c :=
  IntegralCriticalScriptQueryBits.birthFamily_stateAt _ _ _ _

theorem scale_eq (c : List Bool) (i : Fin (F.ambient c + 1)) :
    IntegralCriticalScriptHeightBits.scales (queries F) c i.val = ((atSource F c).data []).scales i := by
  change (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (older (F.rules c) (F.selected c)).length).bank.selectedDenominator
    (IntegralCriticalScriptHeightBits.select (queries F) c i.val) =
    (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (older (F.rules c) (F.selected c)).length).bank.selectedDenominator
      ((chosen (F.rules c) (F.selected c)).select (past (F.rules c) (older (F.rules c) (F.selected c)).length).length i)
  let pick (z : ℕ) : Option (Fin (past (F.rules c) (older (F.rules c) (F.selected c)).length).length) :=
    if hz : z < (past (F.rules c) (older (F.rules c) (F.selected c)).length).length then some ⟨z, hz⟩ else none
  exact congrArg (fun z => (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c)
    (older (F.rules c) (F.selected c)).length).bank.selectedDenominator (pick z)) (selector_eq F c i)

theorem denominator_eq (c : List Bool) :
    CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient c + 1) => IntegralCriticalScriptHeightBits.scales (queries F) c i.val) =
      (IntegralHistoryCriticalBits.original (IntegralCriticalScriptGeneratorBits.birthSource F c)).denominator [] := by
  have HE : CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient c + 1) => IntegralCriticalScriptHeightBits.scales (queries F) c i.val) =
      (IntegralHistoryCriticalBits.original (atSource F c)).denominator [] := by
    change CoordinateFrozenCriticalElimination.denominator _ = CoordinateFrozenCriticalElimination.denominator _
    congr 1
    funext i
    exact scale_eq F c i
  exact HE.trans (congrArg (fun V : IntegralHistoryCriticalBits.Family => (IntegralHistoryCriticalBits.original V).denominator []) (atSource_eq F c))

theorem source_denominator_FP (h : IntegralCriticalScriptGeneratorBits.Controls F)
    (a : IntegralCriticalScriptFP.Access (metadata F)) :
    (fun c => residueBits ((IntegralHistoryCriticalBits.original
      (IntegralCriticalScriptGeneratorBits.birthSource F c)).denominator [] : ZMod (F.modulus c))) ∈ FP :=
  mem_FP_of_eq (denominator_FP F h a) (fun c => congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) (denominator_eq F c))

theorem queried_denominator_FP (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptGeneratorBits.Controls F) (a : IntegralCriticalScriptFP.Access (metadata F)) :
    (fun c => residueBits ((IntegralCriticalScriptQueryBits.generatorSource F q).denominator c : ZMod (F.modulus c))) ∈ FP :=
  mem_FP_of_eq (source_denominator_FP F h a) (fun _ => rfl)

end LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
