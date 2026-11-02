/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQuerySpace
public import LeanCanny.Algebra.IntegralIntegerCompanionSpace
public import LeanCanny.ETR.IntegerUnivariateTermSource
/-! # Native default-X companions beyond the active framed births

The original plan leaves two terminal slots. Creating instructions outside
the native active-birth guard are therefore the literal default integer X.
Its companion has a direct native evaluator at every caller modulus, using
the actual old scalar basis and without evaluating that basis.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionDefaultBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open IntegralMixedFramedCompanionQueryBits (root sourceBirth callerModulus)
open scoped Classical

theorem instruction_default (P : Parameters) (D : Plan P) (key : List Bool)
    (hb : P.cap (pairFst key)≤prefixLength P key) :
    instruction P D key=IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key) := by
  have HR := D.room (pairFst key)
  have HL : (D.rules (pairFst key)).reverse.length≤prefixLength P key := by rw [List.length_reverse]; omega
  unfold instruction IntegralMixedFramedHistoryScript.chronological
  rw [List.getElem?_eq_none HL]
  rfl

noncomputable def family (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    PaddedIntegralGeneratorFinBits.Family where
  arity q := (IntegralMixedFramedCompanionBits.source P D H).arity (PaddedIntegralGeneratorSource.base q)
  width q := (IntegralMixedFramedCompanionBits.source P D H).width (PaddedIntegralGeneratorSource.base q)
  carrier q := (IntegralMixedFramedCompanionBits.source P D H).carrier (PaddedIntegralGeneratorSource.base q)
  ring q := (IntegralMixedFramedCompanionBits.source P D H).ring (PaddedIntegralGeneratorSource.base q)
  nontrivial q := (IntegralMixedFramedCompanionBits.source P D H).nontrivial (PaddedIntegralGeneratorSource.base q)
  basis q := (IntegralMixedFramedCompanionBits.source P D H).basis (PaddedIntegralGeneratorSource.base q)
  polynomial q := by
    letI := (IntegralMixedFramedCompanionBits.source P D H).ring (PaddedIntegralGeneratorSource.base q)
    exact Polynomial.X
  degree _ := 1
  modulus := callerModulus
  modulus_ne_zero _ := by unfold callerModulus; omega
  row := PaddedIntegralGeneratorSource.index (IntegralMixedFramedCompanionBits.source P D H) PaddedIntegralGeneratorSource.row
  col := PaddedIntegralGeneratorSource.index (IntegralMixedFramedCompanionBits.source P D H) PaddedIntegralGeneratorSource.col

theorem original_coefficient : SpaceFunction (PrimitivePairBits.coefficient (fun _ => (Polynomial.X : Polynomial ℤ))) := by
  have E := ETR.IntegerUnivariateTermSource.coefficient_evaluator
    (fun _ => (ETR.Term.var 0).toData.toBits) (constFn_mem_FP _)
  exact E.congr (funext fun q => by
    simp only [PrimitivePairBits.coefficient,ETR.IntegerUnivariateTermSource.polynomial,
      ETR.TermView.term_toBits,ETR.Term.eval])

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    SpaceFunction (family P D H).value := by
  apply IntegralIntegerCompanionBits.evaluator (family P D H) (fun _ => Polynomial.X)
    (fun q => by
      let _ := (family P D H).ring q
      exact (Polynomial.map_X (Int.castRingHom ((family P D H).carrier q))).symm) (fun _ => Polynomial.natDegree_X.symm)
    (show IntegralIntegerCompanionBits.Controls (family P D H) from {
      width := a.width.comp IntegralMixedFramedCompanionQueryBits.root_FP
      modulus := IntegralMixedFramedCompanionQueryBits.callerModulus_binary
      row := by
        apply (IntegralMixedFramedCompanionQueryBits.rowIndex_binary P a).of_eq
        intro q
        change IntegralMixedFramedCompanionQueryBits.rowIndex P q=
          Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)%
            count ((IntegralMixedFramedCompanionBits.source P D H).arity (PaddedIntegralGeneratorSource.base q)+1)
              ((IntegralMixedFramedCompanionBits.source P D H).width (PaddedIntegralGeneratorSource.base q))
        rw [IntegralMixedFramedCompanionBits.source_arity,IntegralMixedFramedCompanionBits.source_width]
        rfl
      col := by
        apply (IntegralMixedFramedCompanionQueryBits.colIndex_binary P a).of_eq
        intro q
        change IntegralMixedFramedCompanionQueryBits.colIndex P q=
          Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)%
            count ((IntegralMixedFramedCompanionBits.source P D H).arity (PaddedIntegralGeneratorSource.base q)+1)
              ((IntegralMixedFramedCompanionBits.source P D H).width (PaddedIntegralGeneratorSource.base q))
        rw [IntegralMixedFramedCompanionBits.source_arity,IntegralMixedFramedCompanionBits.source_width]
        rfl })
    (fun _ => BinaryNatCode.encode 1) (SpaceFunction.ofFP _ (constFn_mem_FP _)) (fun _ => rfl)
    original_coefficient

private theorem command_default {n B : ℕ} {I J : IntegralMixedFramedHistoryScript.Instruction n B}
    (h : I=J) (hJ : J.command=IntegralMixedFullHistoryScript.defaultCommand) :
    I.command=IntegralMixedFullHistoryScript.defaultCommand := by
  cases h
  exact hJ

attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix
  PaddedIntegralGeneratorFinBits.Family.matrix

theorem value_source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hb : P.cap (root q)≤sourceBirth P q) :
    (family P D H).value q=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HC := instruction_default P D (PaddedIntegralGeneratorSource.base q) hb
  have HX := command_default HC (by rfl)
  have HP : (IntegralMixedFramedCompanionBits.source P D H).polynomial (PaddedIntegralGeneratorSource.base q)=
      (family P D H).polynomial q := by
    change IntegralMixedFullHistoryScript.polynomial _ _ (instruction P D _).command=Polynomial.X
    rw [HX]
    simp only [IntegralMixedFullHistoryScript.defaultCommand,
      IntegralMixedFullHistoryScript.polynomial,Polynomial.map_X]
  have HD : (IntegralMixedFramedCompanionBits.source P D H).degree (PaddedIntegralGeneratorSource.base q)=
      (family P D H).degree q := by
    change IntegralMixedFullHistoryScript.degree _ _ (instruction P D _).command=1
    rw [HX]
    exact Polynomial.natDegree_X
  have HM : (IntegralMixedFramedCompanionBits.source P D H).matrix (PaddedIntegralGeneratorSource.base q)=
      (family P D H).matrix q := by
    unfold PaddedIntegralGeneratorSource.Source.matrix PaddedIntegralGeneratorFinBits.Family.matrix
    rw [HP,HD]
    rfl
  unfold PaddedIntegralGeneratorSource.value PaddedIntegralGeneratorFinBits.Family.value
  rw [HM]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCompanionDefaultBits
