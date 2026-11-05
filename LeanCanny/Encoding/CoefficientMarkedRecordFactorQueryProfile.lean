/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRuleSelection
public import LeanCanny.Encoding.CoefficientMarkedRecordQueryKindProfile
public import LeanCanny.Encoding.CoefficientMarkedRecordFactorQuery
/-! # Native coefficient growth for alternative untruncated factor queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryProfile
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFramedPhysicalLayoutCongruence
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem matrix_transport {a b S T B C m k : ℕ} {P : SpatialSource a} {Q : SpatialSource b} {I J : Type}
    (x : State P S B m I) (y : State Q T C k J) (hx : m ≤ S) (hy : k ≤ T)
    (r : IntegralMixedCriticalSweep.Rule a) (s : IntegralMixedCriticalSweep.Rule b)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eI : I = J)
    (he : HEq x y) (hr : HEq r s) (K : IntegralMixedRelativeCuts.Kind P r) :
    ∃ L : IntegralMixedRelativeCuts.Kind Q s, ∀ tau i j,
      IntegralCriticalTotalSnapshotBits.integerEntry (IntegralMixedCutMatrix.coefficientMatrix x hx r K tau) i j =
        IntegralCriticalTotalSnapshotBits.integerEntry (IntegralMixedCutMatrix.coefficientMatrix y hy s L tau) i j := by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  cases eq_of_heq hr
  exact ⟨K, fun _ _ _ => rfl⟩

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem family_natural (R : List Bool → ℕ) (key : List Bool)
    (K : IntegralMixedRelativeCuts.Kind ((actualFamily hn ht ha R).spatial key) ((actualFamily hn ht ha R).rule key))
    (tau i j : ℕ) :
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((actualFamily hn ht ha R).state key)
        ((actualFamily hn ht ha R).birth_bound key) ((actualFamily hn ht ha R).rule key) K tau) i j).natAbs ≤
      2 ^ (rawSlope hn ht ha (pairFst key) * R (pairFst key) + rawOffset hn ht ha (pairFst key)) := by
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs with hi hj
  · exact CoefficientMarkedRecordQueryKindProfile.coefficient_bound hn ht ha R key K tau ⟨i, hi⟩ ⟨j, hj⟩
  all_goals exact Nat.zero_le _

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan

theorem native_kind_bound (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
    let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    ∀ K : IntegralMixedRelativeCuts.Kind (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R)
      (c.rule (commonDenominator x) (commonDenominator_ne_zero x)), ∀ tau i j,
      (IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix x (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
          (c.rule (commonDenominator x) (commonDenominator_ne_zero x)) K tau) i j).natAbs ≤
        2 ^ (rawSlope hn ht ha ctx * R ctx + rawOffset hn ht ha ctx) := by
  dsimp only
  intro K tau i j
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k []
  let G := actualFamily hn ht ha R
  let y := G.state key
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  have HL := (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk.le []).symm
  obtain ⟨L, HE⟩ := matrix_transport x y (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le)
    (G.birth_bound key) (c.rule (commonDenominator x) (commonDenominator_ne_zero x)) (G.rule key)
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k [])
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k [])
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k [])
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le [])
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k []) (congrArg Layout.index HL)
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk.le [])
    (CoefficientMarkedRecordRuleSelection.rule_heq hn ht ha ctx R k hk hc []) K
  rw [HE tau i j]
  simpa only [key, CoefficientMarkedRecordRowLayout.key_root] using family_natural hn ht ha R key L tau i j

/-- Every coefficient of every alternative untruncated numeric-choice query is bounded. -/
theorem coefficient_bound (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (choice tau i j : ℕ) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
        ((CoefficientMarkedRecordFactorQuery.native hn ht ha ctx R k hk.le choice).coeff tau)) i j).natAbs ≤
        2 ^ (rawSlope hn ht ha ctx * R ctx + rawOffset hn ht ha ctx) := by
  dsimp only
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  exact native_kind_bound hn ht ha ctx R k hk hc
    ((CoefficientMixedFactorSpecialization.queriedCut c choice).kind
      (commonDenominator x) (commonDenominator_ne_zero x)) tau i j

end LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryProfile
