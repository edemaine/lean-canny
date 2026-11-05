/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedFactorChoice
public import LeanCanny.Encoding.CoefficientMarkedRecordCutSelection
public import LeanCanny.Encoding.CoefficientMarkedRecordFactorQueryBounds
/-! # Full factors for the literal clipped native lower-choice probes -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordChoiceFactor
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedRelativeCuts CoefficientMixedFactorSpecialization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem formal_atChoice {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {a m B : ℕ} {P : SpatialSource a} (bank : CoefficientHeightBank R A m)
    (low : MvPolynomial (Fin (a + 1)) R) (leading : R) (c : IntegralMixedCausalRecordBits.Cut P B)
    (requested : ℕ) :
    formalFactor bank low leading (c.rule 1 one_ne_zero) c.current
      (atChoice (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero) requested) =
    formalFactor bank low leading
      ((queriedCut c (min requested (choiceIndex (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)))).rule 1 one_ne_zero)
      (queriedCut c (min requested (choiceIndex (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)))).current
      ((queriedCut c (min requested (choiceIndex (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)))).kind 1 one_ne_zero) := by
  rw [queried_kind_atChoice]
  rfl

noncomputable def nativeFactors {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (hm : m ≤ S)
    (selection : CoefficientMarkedRecordCutSelection.KindSelection P) :=
  fun requested => x.sampler.scalarPrefix.basis.polynomial
    (IntegralMixedRelativeCuts.factor x hm selection.rule
      (atChoice selection.rule selection.kind requested))

private theorem nativeFactors_transport {a b S T B C m k : ℕ}
    {P : SpatialSource a} {Q : SpatialSource b} {I J : Type}
    (x : State P S B m I) (y : State Q T C k J) (hx : m ≤ S) (hy : k ≤ T)
    (r : CoefficientMarkedRecordCutSelection.KindSelection P)
    (s : CoefficientMarkedRecordCutSelection.KindSelection Q)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eI : I = J)
    (he : HEq x y) (hs : HEq r s) : HEq (nativeFactors x hx r) (nativeFactors y hy s) := by
  cases en
  cases eS
  cases eB
  cases em
  cases eI
  cases eq_of_heq eP
  cases eq_of_heq he
  cases eq_of_heq hs
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def factor (ctx : List Bool) (k requested : ℕ) :
    Polynomial (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).carrier :=
  let c := CoefficientMarkedRecordCutSource.cut hn ht ha ctx k
  formalFactor (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).bank
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (c.rule 1 one_ne_zero) c.current (atChoice (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero) requested)

noncomputable def polynomial (ctx : List Bool) (k requested : ℕ) :
    Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ℤ[X]) :=
  (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis.polynomial (factor hn ht ha ctx k requested)

noncomputable def native (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested : ℕ) :=
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  IntegralMixedRelativeCuts.factor x (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (atChoice (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
      (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) requested)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (requested : ℕ) :
    (polynomial hn ht ha ctx k requested).map (MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R ctx))) =
      (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk).sampler.scalarPrefix.basis.polynomial
        (native hn ht ha ctx R k hk requested) := by
  let F := CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  let c := CoefficientMarkedRecordCutSource.cut hn ht ha ctx k
  let low := CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx
  let a := CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx
  let hd := CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx R
  have hm := CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk
  obtain ⟨ψ, hb, hg, _, _⟩ :=
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR).pointwise
  have hs := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx R
  have HE := map_native F.bank low a x hm (c.rule 1 one_ne_zero) c.current
    (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero)
      (atChoice (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero) requested))
    (evalRingHom ((2 : ℤ) ^ R ctx)) ψ hg hs.1 hs.2
  unfold formalFactor at HE
  rw [CoefficientMixedCutSourceDegree.factor_eq hd F.bank low a (c.rule 1 one_ne_zero)
    (CoefficientMixedCutSpecialization.slope F.bank (c.rule 1 one_ne_zero) c.current)
    (atChoice (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero) requested)] at HE
  rw [native_retarget_atChoice] at HE
  rw [CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)] at HE
  change ((F.basis.polynomial (factor hn ht ha ctx k requested)).map _) = _
  rw [hb.polynomial_map, CoefficientCoordinateBasis.ofIntegral_polynomial]
  exact congrArg x.sampler.scalarPrefix.basis.polynomial HE

/-- Numeric re-querying uses MIN requested creatingChoice, not the unbounded
request or the raw serialized choice modulo a possibly different bound. -/
theorem polynomial_eq (ctx : List Bool) (k requested : ℕ) :
    polynomial hn ht ha ctx k requested =
      CoefficientMarkedRecordFactorQuery.polynomial hn ht ha ctx k
        (min requested (choiceIndex
          ((CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).rule 1 one_ne_zero)
          ((CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).kind 1 one_ne_zero))) := by
  exact congrArg (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis.polynomial
    (formal_atChoice (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).bank
      (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
      (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k) requested)

theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (requested tau : ℕ) (e : Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) →₀ ℕ) :
    (((polynomial hn ht ha ctx k requested).coeff tau).coeff e).natDegree ≤
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx ∧
    coefficientMass (((polynomial hn ht ha ctx k requested).coeff tau).coeff e) ≤
      2 ^ CoefficientMarkedRecordCutCoefficientBounds.coefficientBudget hn ht ha ctx := by
  rw [polynomial_eq]
  exact CoefficientMarkedRecordFactorQueryBounds.coefficient_degree_mass hn ht ha ctx k hk hc _ tau e

theorem scalar_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested tau : ℕ) :
    ((polynomial hn ht ha ctx k requested).coeff tau).totalDegree ≤
      CoefficientMarkedRecordCutCoefficientBounds.scalarDegree hn ht ha ctx := by
  rw [polynomial_eq]
  exact CoefficientMarkedRecordFactorQueryBounds.scalar_degree hn ht ha ctx k hk _ tau

theorem target_degree (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested : ℕ) :
    (polynomial hn ht ha ctx k requested).natDegree ≤
      2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx := by
  rw [polynomial_eq]
  exact CoefficientMarkedRecordFactorQueryBounds.target_degree hn ht ha ctx k hk _

theorem specializes_family (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (fun requested => (polynomial hn ht ha ctx k requested).map
      (MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R ctx))))
      (nativeFactors
        ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).state
          (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux))
        ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).birth_bound _)
        (CoefficientMarkedRecordCutSelection.familySelection
          (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R)
          (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux))) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  let G := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let selected : CoefficientMarkedRecordCutSelection.KindSelection
      (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R) :=
    ⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
      c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩
  have HE := funext (fun requested => specializes hn ht ha ctx R k hk.le hR requested)
  have HL := (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk.le aux).symm
  have HT := nativeFactors_transport x (G.state key)
    (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le) (G.birth_bound key)
    selected (CoefficientMarkedRecordCutSelection.familySelection G key)
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux)
    (congrArg LeanCanny.Algebra.IntegralMixedFramedPhysicalLayoutCongruence.Layout.index HL)
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordCutSelection.selection_heq hn ht ha ctx R k hk hc aux)
  exact (heq_of_eq HE).trans HT

end LeanCanny.Encoding.CoefficientMarkedRecordChoiceFactor
