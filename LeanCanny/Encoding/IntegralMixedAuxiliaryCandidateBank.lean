/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankQueryLegacy
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateCoordinateRoot
public import LeanCanny.Algebra.IntegralMixedDenominatorNative

/-! # Actual original candidates instantiate the native bank-query interface

A native context writer selects the whole original candidate and retained
index. The same source, advice, prefix and joint label are preserved. Modulo
clamping only totalizes malformed indices; valid indices are unchanged.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliaryCandidateCoordinate (sourceContext inputSyntax)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.degreeCharge
  IntegralMixedAuxiliaryParameters.augmented

noncomputable abbrev parameters (n : List Bool→ℕ) (t : List Bool→Term) :=
  IntegralMixedAuxiliaryParameters.parameters (dimension n) (term t)
noncomputable def originalSyntax {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    IntegralMixedFramedNativeBits.Syntax (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) := inputSyntax hn ht ha

attribute [local irreducible] planAt dataAt

attribute [local irreducible] sourceContext IntegralMixedAuxiliaryCandidate.source pair

noncomputable def key (n : List Bool→ℕ) (t : List Bool→Term) (c : List Bool) :=
  IntegralMixedFramedCoordinateCharacteristicBits.key (sourceContext n t c)
theorem key_eq (n : List Bool→ℕ) (t : List Bool→Term) (c : List Bool) :
    key n t c=IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id
      (IntegralMixedAuxiliaryCandidate.source n t (pairFst c)) := by
  simp only [key,IntegralMixedFramedCoordinateCharacteristicBits.key,sourceContext,pairFst_pair]

theorem key_FP {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) : key n t∈FP :=
  mem_FP_comp (f := sourceContext n t) (g := pairFst)
    (IntegralMixedAuxiliaryCandidateCoordinate.sourceContext_FP hn ht) pairFst_mem_FP

noncomputable def count {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (c : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (key n t c)).count

theorem count_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (c : List Bool) :
    count hn ht ha c=n (pairFst (pairFst c))+1 := by
  change IntegralMixedFramedCoordinateCharacteristicBits.count (parameters n t) (planAt hn ht ha) (dataAt hn ht ha)
    (sourceContext n t c)=_
  exact IntegralMixedAuxiliaryCandidateCoordinate.context_count hn ht ha c

theorem count_unary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : UnaryFn (count hn ht ha) :=
  ((hn.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 1)).of_eq
    (fun c=>(count_eq hn ht ha c).symm)

theorem positive {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (c : List Bool) :
    0<count hn ht ha c := by rw [count_eq]; omega

noncomputable def index {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) (c : List Bool) :=
  Nat.fromBitsLE (pairSnd c)%count hn ht ha c

theorem index_unary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) : UnaryFn (index hn ht ha) :=
  IntegralMixedDenominatorScriptBits.binary_bounded_unary
    ((BinaryFn.fromBits pairSnd_mem_FP).mod (BinaryFn.ofUnary (count_unary hn ht ha)))
    (count_unary hn ht ha) (fun c=>(Nat.mod_lt _ (positive hn ht ha c)).le)

noncomputable def bank {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (f : List Bool→List Bool) : IntegralFramedBankQuery.Bank where
  parameters:=parameters n t
  plan:=planAt hn ht ha
  data:=dataAt hn ht ha
  nodes _:=1
  factor:=IntegralMixedAuxiliarySchedule.factor (dimension n) (term t)
  seed:=IntegralMixedAuxiliarySchedule.seed (dimension n) (term t)
  bounds:=IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha
  key c:=key n t (f c)
  positive c:=positive hn ht ha (f c)
  coordinate c:=⟨index hn ht ha (f c),Nat.mod_lt _ (positive hn ht ha (f c))⟩


theorem coordinate_valid {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (f : List Bool→List Bool) (c : List Bool) (hi : Nat.fromBitsLE (pairSnd (f c))<count hn ht ha (f c)) :
    ((bank hn ht ha f).coordinate c).val=Nat.fromBitsLE (pairSnd (f c)) := Nat.mod_eq_of_lt hi

theorem evaluator {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {f : List Bool→List Bool} (hf : f∈FP) (Q : IntegerPolynomialRootQueriesBits.Source)
    (hQ : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (IntegralFramedBankQuery.value (bank hn ht ha f) Q) := by
  have HK : (fun c=>key n t (f c))∈FP:=mem_FP_comp (f := f) (g := key n t) hf (key_FP hn ht)
  have HI : UnaryFn (fun c=>index hn ht ha (f c)):=(index_unary hn ht ha).comp hf
  exact IntegralFramedBankQueryLegacy.evaluator (bank hn ht ha f)
    (IntegralMixedAuxiliaryParameters.access (dimension_unary hn) (term_FP ht)) (originalSyntax hn ht ha)
    (IntegralMixedAuxiliaryCandidateBounds.family_inputs hn ht ha)
    (fun root=>(IntegralMixedAuxiliaryEmptyPlan.description (dimension_unary hn) (term_FP ht)
      (fun q=>ha (pairFst q))).factor_positive root)
    (fun _=>by change 1≤1; exact le_rfl) (BinaryFn.const 1)
    (IntegralMixedAuxiliarySchedule.factor_binary (dimension_unary hn) (term_FP ht))
    (IntegralMixedAuxiliarySchedule.seed_binary (dimension_unary hn) (term_FP ht))
    HK HI Q hQ

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidateBank
