/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankPolynomial
public import LeanCanny.Encoding.CoefficientMarkedRecordRows
/-! # Retained-coordinate polynomial specialization at actual saved family keys -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBankActual
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem polynomial_transport {a b S T B C m k : ℕ} {P : SpatialSource a} {Q : SpatialSource b}
    {I J : Type} (x : State P S B m I) (y : State Q T C k J)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eI : I = J) (he : HEq x y) :
    HEq (fun i => IntegralMixedBankCoordinatePolynomial.polynomial x i)
      (fun i => IntegralMixedBankCoordinatePolynomial.polynomial y i) := by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRowLayout.commands

theorem native_family (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :
    HEq (fun i => IntegralMixedBankCoordinatePolynomial.polynomial
      (CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)) i)
      (fun i => IntegralMixedBankCoordinatePolynomial.polynomial
        ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)).state
          (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) i) := by
  let x := CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)
  let y := (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).state
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
  have HL := (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk aux).symm
  exact polynomial_transport x y
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux)
    (congrArg Layout.index HL)
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk aux)

/-- Every formal retained-coordinate polynomial maps to the actual saved family. -/
theorem specializes_family (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (fun i => (CoefficientMarkedRecordBankPolynomial.polynomial hn ht ha ctx k i).map
      (evalRingHom ((2 : ℤ) ^ R ctx)))
      (fun i => IntegralMixedBankCoordinatePolynomial.polynomial
        ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)).state
          (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) i) := by
  have H := funext (CoefficientMarkedRecordBankPolynomial.specializes hn ht ha ctx R k hk hR)
  exact (heq_of_eq H).trans (native_family hn ht ha ctx R k hk aux)

end LeanCanny.Encoding.CoefficientMarkedRecordBankActual
