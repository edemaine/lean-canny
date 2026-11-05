/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
public import LeanCanny.Encoding.CoefficientMarkedRecordRuleSelection
public import LeanCanny.Encoding.CoefficientMarkedRecordRows
/-! # Constructed coordinate heads at the actual saved family rule -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCoordinateHead
open IntegralMixedHistory Polynomial
open scoped Classical

noncomputable def heads {n S B m : ℕ} {P : SpatialSource n} {I : Type}
    (x : State P S B m I) (hm : m ≤ S) (r : IntegralMixedCriticalSweep.Rule n) (d e : ℕ) :=
  fun j => SelectedMultivariatePolynomialLift.lift (IntegralMixedCriticalSweep.coordinate x hm r j)
    (SelectedPoweredPolynomialLift.representative x.sampler.scalarPrefix.basis
      (UniformIntegralPowerSchedule.weights S (2^B) m)) d e

theorem heads_transport {a b S T B C m k : ℕ} {P : SpatialSource a} {Q : SpatialSource b} {I J : Type}
    (x : State P S B m I) (y : State Q T C k J) (hx : m ≤ S) (hy : k ≤ T)
    (r : IntegralMixedCriticalSweep.Rule a) (s : IntegralMixedCriticalSweep.Rule b)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eI : I = J)
    (he : HEq x y) (hr : HEq r s) (d e : ℕ) : HEq (heads x hx r d e) (heads y hy s d e) := by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  cases eq_of_heq hr
  rfl

theorem heads_retarget {n S B m C : ℕ} {P Q : SpatialSource n} {I : Type}
    (x : State Q S B m I) (hm : m ≤ S) (c : IntegralMixedCausalRecordBits.Cut P C) (d e : ℕ) :
    HEq (fun j => SelectedMultivariatePolynomialLift.lift (native x hm (c.rule 1 one_ne_zero) c.current j)
      (SelectedPoweredPolynomialLift.representative x.sampler.scalarPrefix.basis
        (UniformIntegralPowerSchedule.weights S (2^B) m)) d e)
      (heads x hm (c.rule (commonDenominator x) (commonDenominator_ne_zero x)) d e) := by
  rcases c with ⟨critical, height, frozen, tag, coordinate, choice, degree, source_cap, degree_cap, current⟩
  cases current <;> rfl

theorem cut_rule {n B : ℕ} {P Q : SpatialSource n} (hd : P.degree = Q.degree)
    (c : IntegralMixedCausalRecordBits.Cut P B) (q : ℤ) (hq : q ≠ 0) :
    (CoefficientMixedCutSourceDegree.cut hd c).rule q hq = c.rule q hq := rfl

end LeanCanny.Algebra.CoefficientMixedCoordinateHead

namespace LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem specializes_family (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (d e : ℕ) :
    HEq (fun j => (polynomial hn ht ha ctx k j d e).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (CoefficientMixedCoordinateHead.heads
        ((actualFamily hn ht ha R).state (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux))
        ((actualFamily hn ht ha R).birth_bound _) ((actualFamily hn ht ha R).rule _) d e) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordCutSource.cut hn ht ha ctx k
  let cR := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let G := actualFamily hn ht ha R
  let y := G.state key
  let hm := CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le
  have HS := funext (fun j => specializes hn ht ha ctx R k hk.le hR j d e)
  have HN := CoefficientMixedCoordinateHead.heads_retarget x hm c d e
  have HR : c.rule (commonDenominator x) (commonDenominator_ne_zero x) =
      cR.rule (commonDenominator x) (commonDenominator_ne_zero x) := by
    have HT := CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx R
      (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)
    have HE := congrArg
      (fun z : IntegralMixedCausalRecordBits.Cut (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R)
        (CoefficientMarkedIntegerBirth.width hn ht ha ctx) =>
        z.rule (commonDenominator x) (commonDenominator_ne_zero x)) HT
    exact (CoefficientMixedCoordinateHead.cut_rule _ c _ _).symm.trans HE
  have HL := (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk.le aux).symm
  have HY := CoefficientMixedCoordinateHead.heads_transport x y hm (G.birth_bound key)
    (cR.rule (commonDenominator x) (commonDenominator_ne_zero x)) (G.rule key)
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux) (congrArg Layout.index HL)
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordRuleSelection.rule_heq hn ht ha ctx R k hk hc aux) d e
  rw [HR] at HN
  exact (heq_of_eq HS).trans (HN.trans HY)

end LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
