/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingFields
/-! # Native common denominator of a total actual creating source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def denominatorQueries (F : Scripts) : IntegralCriticalScriptHeightBits.Queries :=
  { IntegralCriticalFlatClearedHeightBits.queries F with
    prefixLength := IntegralCriticalHistoryTask.birth F.toParameters
    row _ := ⟨0, pow_pos (Nat.two_pow_pos _) _⟩
    col _ := ⟨0, pow_pos (Nat.two_pow_pos _) _⟩ }

theorem denominatorControls (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : IntegralCriticalScriptHeightBits.Controls (denominatorQueries F) :=
  { IntegralCriticalFlatClearedHeightBits.controls F a n with
    prefixLength := BinaryFn.ofUnary (birth_unary F a)
    row := BinaryFn.const 0
    col := BinaryFn.const 0 }

theorem scales_creating (F : Scripts) (q : List Bool) (h : valid F q) (i : Fin (F.ambient (root q) + 1)) :
    IntegralCriticalScriptHeightBits.scales (denominatorQueries F) q i.val =
      ((IntegralCriticalScriptDenominatorFP.atSource (IntegralCriticalFlatHeightBits.generatorQueries F (fun _ => q) (fun _ => h)) q).data []).scales i := by
  let G := IntegralCriticalFlatHeightBits.generatorQueries F (fun _ => q) (fun _ => h)
  have HG : (older (G.rules q) (G.selected q)).length = IntegralCriticalHistoryTask.birth F.toParameters q :=
    IntegralCriticalFlatHeightBits.creating_older_length F q h
  have HE := IntegralCriticalScriptDenominatorFP.scale_eq G q i
  have HX : IntegralCriticalScriptDenominatorFP.selector G q i.val = IntegralCriticalFlatClearedHeightBits.selector F q i.val := by
    unfold IntegralCriticalScriptDenominatorFP.selector IntegralCriticalFlatClearedHeightBits.selector
    rw [HG]
    unfold IntegralCriticalScriptFP.selector IntegralCriticalScriptFP.commandAt
    dsimp only [IntegralCriticalFlatCompanionBits.metadata, IntegralCriticalFlatClearedHeightBits.metadata,
      G, IntegralCriticalFlatHeightBits.generatorQueries]
    cases (F.rules (root q)).reverse[IntegralCriticalHistoryTask.birth F.toParameters q]? <;> rfl
  let read (j z : ℕ) : ℤ := (stateAt (F.rules (root q)) (F.length_le (root q)) (F.scalar_bound (root q)) j).bank.selectedDenominator
    (if hz : z < (past (F.rules (root q)) j).length then some ⟨z, hz⟩ else none)
  have HS : IntegralCriticalScriptHeightBits.scales (denominatorQueries F) q i.val =
      IntegralCriticalScriptHeightBits.scales (IntegralCriticalScriptDenominatorFP.queries G) q i.val := by
    change read (IntegralCriticalHistoryTask.birth F.toParameters q) (IntegralCriticalFlatClearedHeightBits.selector F q i.val) =
      read (older (G.rules q) (G.selected q)).length (IntegralCriticalScriptDenominatorFP.selector G q i.val)
    rw [HG, HX]
  exact HS.trans HE

theorem euler_denominator_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    (euler F).denominator q = CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient (root q) + 1) => IntegralCriticalScriptHeightBits.scales (denominatorQueries F) q i.val) := by
  let G := IntegralCriticalFlatHeightBits.generatorQueries F (fun _ => q) (fun _ => h)
  have HE : CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient (root q) + 1) => IntegralCriticalScriptHeightBits.scales (denominatorQueries F) q i.val) =
      (IntegralHistoryCriticalBits.original (IntegralCriticalScriptDenominatorFP.atSource G q)).denominator [] := by
    change CoordinateFrozenCriticalElimination.denominator _ = CoordinateFrozenCriticalElimination.denominator _
    congr 1
    funext i
    exact scales_creating F q h i
  have HS : IntegralCriticalScriptDenominatorFP.atSource G q = IntegralCriticalFlatHeightBits.creatingFamily F q h :=
    (IntegralCriticalScriptDenominatorFP.atSource_eq G q).trans
      (IntegralCriticalFlatHeightBits.generator_birthSource F (fun _ => q) (fun _ => h) q)
  rw [HS] at HE
  change (IntegralHistoryCriticalBits.original (atFamily F q)).denominator [] = _
  rw [atFamily_valid F q h]
  exact HE.symm

theorem euler_denominator_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : (euler F).denominator q = 1 := by
  change (IntegralHistoryCriticalBits.original (atFamily F q)).denominator [] = 1
  rw [atFamily_invalid F q h]
  decide

attribute [local irreducible] atFamily euler

theorem denominator_FP (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) :
    (fun q => residueBits ((euler F).denominator q : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) ∈ FP := by
  have HR := IntegralCriticalScriptHeightBits.denominator_FP (denominatorQueries F) (denominatorControls F a n)
    (IntegralCriticalScriptFP.access (IntegralCriticalFlatClearedHeightBits.metadata F) n)
  have HO := ModularScalarFP.natCast (IntegralCriticalHistoryTask.modulus_binary _ a.toAccess) (fun _ => 1) (BinaryFn.const 1)
  have HP := (valid_FP F a).ite_mem_FP HR HO
  refine mem_FP_of_eq HP (fun q => ?_)
  by_cases h : valid F q
  · simp only [ite_eq_left h]
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)))
      (euler_denominator_valid F q h).symm
  · simp only [ite_eq_right h]
    rw [euler_denominator_invalid F q h]
    simp only [Nat.cast_one, Int.cast_one]

end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
