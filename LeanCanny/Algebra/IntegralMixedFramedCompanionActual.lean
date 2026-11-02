/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerActual
/-! # Native companions agree with the literal creating framed polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedFramedProducerBits (physicalFamily virtualFamily)
open scoped Classical
attribute [local irreducible] PaddedIntegralGeneratorFinBits.Family.matrix
  PaddedIntegralGeneratorSource.Source.matrix

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
local notation "K" => IntegralMixedVirtualTaskBits.saved P q
local notation "V" => virtualFamily P D H
local notation "F" => physicalFamily P D H
local notation "S" => IntegralMixedFramedCompanionBits.source P D H

private theorem source_polynomial : (S).polynomial K=
    IntegralMixedFullHistoryScript.polynomial ((V).state K) ((V).birth_bound K) (instruction P D K).command := rfl
private theorem source_degree : (S).degree K=
    IntegralMixedFullHistoryScript.degree ((V).state K) ((V).birth_bound K) (instruction P D K).command := rfl

private theorem integer_matrix (p : Polynomial ℤ) (hp : p≠0)
    (hd : p.natDegree≤2^P.width (pairFst K))
    (hc : (instruction P D K).command=.integer p hp hd) :
    (IntegralMixedIntegerFamilyBits.family P V (IntegralMixedFramedIntegerBits.polynomial P D)).matrix q=(S).matrix K := by
  rw [IntegralMixedFramedCompanionBits.source_matrix]
  unfold PaddedIntegralGeneratorFinBits.Family.matrix
  change IntegralMixedFramedCompanionBits.matrixAt P D H K
    ((IntegralMixedFramedIntegerBits.polynomial P D K).map (Int.castRingHom _))
    (IntegralMixedFramedIntegerBits.polynomial P D K).natDegree=_
  rw [IntegralMixedFramedIntegerBits.polynomial_actual P D K p hp hd hc]
  rw [source_polynomial P D H q,source_degree P D H q,hc]
  rfl

private theorem physical_matrix (r : IntegralMixedHistory.CriticalRule (P.ambient (pairFst K)))
    (hc : (instruction P D K).command=.critical r)
    (hcoord : get P .slot13 q=(instruction P D K).command.coordinate) :
    (IntegralMixedPhysicalCompanionBits.family P F).matrix q=(S).matrix K := by
  have HR : (F).rule (IntegralMixedPhysicalTaskBits.saved P q)=r :=
    IntegralMixedFramedPhysicalBits.rule_critical P D K r hc
  have HC : ((IntegralMixedPhysicalTaskBits.indices P F).coordinate q).val=
      ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).coordinate %
        ((F).ambient (IntegralMixedPhysicalTaskBits.saved P q)-
          ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val+1) := by
    change get P .slot13 q%((F).ambient (IntegralMixedPhysicalTaskBits.saved P q)-
      ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val+1)=
      ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).coordinate %
        ((F).ambient (IntegralMixedPhysicalTaskBits.saved P q)-
          ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val+1)
    rw [HR,hcoord,hc]
    exact Nat.mod_mod _ _
  have HP := IntegralMixedPhysicalCompanionBits.actual_polynomial P F q HC
  rw [HR] at HP
  have HD : (IntegralMixedPhysicalCompanionBits.family P F).degree q=(S).degree K := by
    change PurePowerReductionBounds.dimension
      ((F).ambient (IntegralMixedPhysicalTaskBits.saved P q)-
        ((F).rule (IntegralMixedPhysicalTaskBits.saved P q)).offset.val+1)
      ((F).spatial (IntegralMixedPhysicalTaskBits.saved P q)).degree=_
    rw [HR]
    rw [source_degree P D H q,hc]
    rfl
  have HP' : (IntegralMixedPhysicalCompanionBits.family P F).polynomial q=(S).polynomial K := by
    rw [source_polynomial P D H q,hc]
    exact HP
  rw [IntegralMixedFramedCompanionBits.source_matrix]
  unfold PaddedIntegralGeneratorFinBits.Family.matrix
  change IntegralMixedFramedCompanionBits.matrixAt P D H K
    ((IntegralMixedPhysicalCompanionBits.family P F).polynomial q)
    ((IntegralMixedPhysicalCompanionBits.family P F).degree q)=_
  exact congrArg₂ (IntegralMixedFramedCompanionBits.matrixAt P D H K) HP' HD

private theorem cut_matrix (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst K)))
    (k : IntegralMixedRelativeCuts.Kind (instruction P D K).source r) (d : ℕ)
    (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst K)+1) (instruction P D K).source.degree)
    (hd : d≤2^P.width (pairFst K)) (hc : (instruction P D K).command=.cut r k d ha hd) :
    (IntegralMixedNormalizedCompanionBits.family P V).matrix q=(S).matrix K := by
  have HS : IntegralMixedFramedHistoryFamilyBits.selection P D H K=⟨r,k,d,ha⟩ := by
    unfold IntegralMixedFramedHistoryFamilyBits.selection
    rw [hc]
  have HP : (IntegralMixedNormalizedCompanionBits.family P V).polynomial q=(S).polynomial K := by
    change IntegralMixedHistory.normalizedScalarPolynomial ((V).state K)
      (IntegralMixedCutMatrix.raw ((V).state K) ((V).birth_bound K)
        (IntegralMixedFramedHistoryFamilyBits.selection P D H K).rule
        (IntegralMixedFramedHistoryFamilyBits.selection P D H K).kind
        (IntegralMixedFramedHistoryFamilyBits.selection P D H K).degree)
      (IntegralMixedFramedHistoryFamilyBits.selection P D H K).degree=_
    rw [HS]
    rw [source_polynomial P D H q,hc]
    rfl
  have HD : (IntegralMixedNormalizedCompanionBits.family P V).degree q=(S).degree K := by
    change (IntegralMixedFramedHistoryFamilyBits.selection P D H K).degree=_
    rw [HS]
    rw [source_degree P D H q,hc]
    rfl
  rw [IntegralMixedFramedCompanionBits.source_matrix]
  unfold PaddedIntegralGeneratorFinBits.Family.matrix
  change IntegralMixedFramedCompanionBits.matrixAt P D H K
    ((IntegralMixedNormalizedCompanionBits.family P V).polynomial q)
    ((IntegralMixedNormalizedCompanionBits.family P V).degree q)=_
  exact congrArg₂ (IntegralMixedFramedCompanionBits.matrixAt P D H K) HP HD

private theorem integer_value (p : Polynomial ℤ) (hp : p≠0) (hd : p.natDegree≤2^P.width (pairFst K))
    (hc : (instruction P D K).command=.integer p hp hd) :
    IntegralMixedIntegerFamilyBits.companionValue P V (IntegralMixedFramedIntegerBits.polynomial P D) q=
      IntegralMixedFramedCompanionBits.value P D H q := by
  unfold IntegralMixedIntegerFamilyBits.companionValue PaddedIntegralGeneratorFinBits.Family.value IntegralMixedFramedCompanionBits.value
  rw [integer_matrix P D H q p hp hd hc]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
  congr 1

private theorem physical_value (r : IntegralMixedHistory.CriticalRule (P.ambient (pairFst K)))
    (hc : (instruction P D K).command=.critical r)
    (hcoord : get P .slot13 q=(instruction P D K).command.coordinate) :
    IntegralMixedPhysicalCompanionBits.companionValue P F q=IntegralMixedFramedCompanionBits.value P D H q := by
  unfold IntegralMixedPhysicalCompanionBits.companionValue PaddedIntegralGeneratorFinBits.Family.value IntegralMixedFramedCompanionBits.value
  rw [physical_matrix P D H q r hc hcoord]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
  congr 1

private theorem cut_value (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst K)))
    (k : IntegralMixedRelativeCuts.Kind (instruction P D K).source r) (d : ℕ)
    (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst K)+1) (instruction P D K).source.degree)
    (hd : d≤2^P.width (pairFst K)) (hc : (instruction P D K).command=.cut r k d ha hd) :
    IntegralMixedNormalizedCompanionBits.companionValue P V q=IntegralMixedFramedCompanionBits.value P D H q := by
  unfold IntegralMixedNormalizedCompanionBits.companionValue PaddedIntegralGeneratorFinBits.Family.value IntegralMixedFramedCompanionBits.value
  rw [cut_matrix P D H q r k d ha hd hc]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
  congr 1

attribute [local irreducible] IntegralMixedIntegerFamilyBits.companionValue
  IntegralMixedPhysicalCompanionBits.companionValue IntegralMixedNormalizedCompanionBits.companionValue
  IntegralMixedFramedCompanionBits.value

theorem companion_actual
    (hx : get P .slot15 q=(instruction P D K).command.context)
    (hcoord : get P .slot13 q=(instruction P D K).command.coordinate) :
    companion P D H q=IntegralMixedFramedCompanionBits.value P D H q := by
  cases hc : (instruction P D K).command with
  | integer p hp hd =>
    have HX : get P .slot15 q=0 := by simpa only [hc,IntegralMixedFullHistoryScript.Command.context] using hx
    rw [companion,ite_eq_left HX]
    exact integer_value P D H q p hp hd hc
  | critical r =>
    have HX : get P .slot15 q=1 := by simpa only [hc,IntegralMixedFullHistoryScript.Command.context] using hx
    rw [companion,ite_eq_right (by omega : ¬get P .slot15 q=0),ite_eq_left HX]
    exact physical_value P D H q r hc hcoord
  | cut r k d ha hd =>
    have HX : 2≤get P .slot15 q := by
      rw [hx,hc]
      cases k <;> norm_num [IntegralMixedFullHistoryScript.Command.context]
    rw [companion,ite_eq_right (by omega : ¬get P .slot15 q=0),ite_eq_right (by omega : ¬get P .slot15 q=1)]
    exact cut_value P D H q r k d ha hd hc

end LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
