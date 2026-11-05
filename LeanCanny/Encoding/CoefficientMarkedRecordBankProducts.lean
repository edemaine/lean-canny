/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientHeightBankNaturalProducts
public import LeanCanny.Encoding.CoefficientMarkedRecordBankActual
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot
/-! # Constructed bank products specialize at actual saved prefixes

Every prefix and auxiliary context is literal. No sampler word, chosen
homomorphism, or supplied bank compatibility is needed in the conclusions.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def stateProducts {n S B m : ℕ} {P : SpatialSource n} {I : Type}
    (x : State P S B m I) : ℤ × (ℕ → ℤ) :=
  ⟨(CoefficientHeightBank.ofState x).commonDenominator, (CoefficientHeightBank.ofState x).totalCofactor⟩

private theorem stateProducts_transport {a b S T B C m k : ℕ} {P : SpatialSource a} {Q : SpatialSource b}
    {I J : Type} (x : State P S B m I) (y : State Q T C k J)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eI : I = J) (he : HEq x y) :
    stateProducts x = stateProducts y := by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  rfl

/-- Explicit saved snapshots are unchanged by resource planning. -/
theorem snapshot_planned (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key =
      IntegralMixedFramedBankSnapshotBits.atKey P D H key := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev symbolicPrefix (ctx : List Bool) (k : ℕ) :=
  CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k)

noncomputable def common (ctx : List Bool) (k : ℕ) : ℤ[X] := (symbolicPrefix hn ht ha ctx k).bank.commonDenominator
noncomputable def cofactor (ctx : List Bool) (k i : ℕ) : ℤ[X] := (symbolicPrefix hn ht ha ctx k).bank.totalCofactor i

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRowLayout.commands

private theorem native_products (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) :
    stateProducts (CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)) =
      stateProducts ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).state
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) := by
  have HL := (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk aux).symm
  exact stateProducts_transport _ _
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux)
    (congrArg Layout.index HL)
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk aux)

theorem products_specialize (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    ((common hn ht ha ctx k).eval ((2 : ℤ) ^ R ctx), fun i => (cofactor hn ht ha ctx k i).eval ((2 : ℤ) ^ R ctx)) =
      ((IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).common,
       (IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).cofactor) := by
  obtain ⟨ψ, _, HB, _, _⟩ :=
    CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR
  let x := CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)
  have HC : (common hn ht ha ctx k).eval ((2 : ℤ) ^ R ctx) =
      (CoefficientHeightBank.ofState x).commonDenominator := HB.commonDenominator
  have HF : (fun i => (cofactor hn ht ha ctx k i).eval ((2 : ℤ) ^ R ctx)) =
      (CoefficientHeightBank.ofState x).totalCofactor := _root_.funext (fun i => HB.totalCofactor i)
  have HP : ((common hn ht ha ctx k).eval ((2 : ℤ) ^ R ctx),
      fun i => (cofactor hn ht ha ctx k i).eval ((2 : ℤ) ^ R ctx)) = stateProducts x := Prod.ext HC HF
  exact HP.trans (native_products hn ht ha ctx R k hk aux)

theorem common_specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    (common hn ht ha ctx k).eval ((2 : ℤ) ^ R ctx) =
      (IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).common :=
  congrArg Prod.fst (products_specialize hn ht ha ctx R k hk aux hR)

theorem cofactor_specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (i : ℕ) :
    (cofactor hn ht ha ctx k i).eval ((2 : ℤ) ^ R ctx) =
      (IntegralMixedFramedBankSnapshotBits.atKey (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).cofactor i :=
  congrFun (congrArg Prod.snd (products_specialize hn ht ha ctx R k hk aux hR)) i

end LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
