/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordChoiceFactor
/-! # Literal clipped factor coefficients on the complete physical prefix -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def query {R : Type*} [CommRing R] {m : ℕ}
    (column : Fin m → ℕ) (w : Fin m → ℕ) (p : Polynomial (MvPolynomial (Fin m) R)) (tau : ℕ) :
    MvPolynomial ℕ R :=
  MvPolynomial.rename column (CoordinatePowerSubstitution.substitute w (p.coeff tau))

private theorem query_map {R A : Type*} [CommRing R] [CommRing A] {m : ℕ}
    (φ : R →+* A) (column : Fin m → ℕ) (w : Fin m → ℕ)
    (p : Polynomial (MvPolynomial (Fin m) R)) (tau : ℕ) :
    MvPolynomial.map φ (query column w p tau) =
      query column w (p.map (MvPolynomial.map φ)) tau := by
  simp only [query, MvPolynomial.map_rename, CoordinatePowerSubstitution.map_substitute, Polynomial.coeff_map]

noncomputable def native {a S B m : ℕ} {P : SpatialSource a}
    (L : Layout) (x : State P S B m L.index) (hm : m ≤ S)
    (selection : CoefficientMarkedRecordCutSelection.KindSelection P) :=
  fun requested tau => query (fun i => (L.enumeration (x.sampler.scalar i)).val)
    (UniformIntegralPowerSchedule.weights S (2^B) m)
    (CoefficientMarkedRecordChoiceFactor.nativeFactors x hm selection requested) tau

private theorem native_transport {a b S T B C m k : ℕ} {P : SpatialSource a} {Q : SpatialSource b}
    (L M : Layout) (x : State P S B m L.index) (y : State Q T C k M.index) (hx : m ≤ S) (hy : k ≤ T)
    (r : CoefficientMarkedRecordCutSelection.KindSelection P)
    (s : CoefficientMarkedRecordCutSelection.KindSelection Q)
    (en : a = b) (eS : S = T) (eB : B = C) (em : m = k) (eP : HEq P Q) (eL : L = M)
    (he : HEq x y) (hs : HEq r s) : native L x hx r = native M y hy s := by
  cases en
  cases eS
  cases eB
  cases em
  cases eL
  cases eq_of_heq eP
  cases eq_of_heq he
  cases eq_of_heq hs
  rfl

private theorem query_specializes {a S B m : ℕ} {P : SpatialSource a} (L : Layout)
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S B m L.index)
    (x : State P S B m L.index) (hm : m ≤ S)
    (selection : CoefficientMarkedRecordCutSelection.KindSelection P)
    (p : Polynomial (MvPolynomial (Fin m) ℤ[X])) (radius requested : ℕ)
    (hs : F.scalar = x.sampler.scalar)
    (hp : p.map (MvPolynomial.map (evalRingHom ((2 : ℤ)^radius))) =
      CoefficientMarkedRecordChoiceFactor.nativeFactors x hm selection requested) (tau : ℕ) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^radius))
      (query (fun i => (L.enumeration (F.scalar i)).val)
        (UniformIntegralPowerSchedule.weights S (2^B) m) p tau) = native L x hm selection requested tau := by
  rw [query_map, hp, hs]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (requested tau : ℕ) : MvPolynomial ℕ ℤ[X] :=
  let L := CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk
  let F := CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k
  query (fun i => (L.enumeration (F.scalar i)).val)
    (UniformIntegralPowerSchedule.weights (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k))
    (CoefficientMarkedRecordChoiceFactor.polynomial hn ht ha ctx k requested) tau

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut native
  CoefficientMarkedRecordChoiceFactor.nativeFactors

theorem specializes_native (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (requested tau : ℕ) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
    let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (polynomial hn ht ha ctx k hk requested tau) =
      native (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk) x
        (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk)
        ⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
          c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩ requested tau := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  obtain ⟨_, _, _, _, hs⟩ :=
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR).pointwise
  exact query_specializes (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk)
    (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k)
    (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk)
    (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk)
    ⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
      c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩
    (CoefficientMarkedRecordChoiceFactor.polynomial hn ht ha ctx k requested) (R ctx) requested hs
    (by simpa only [CoefficientMarkedRecordChoiceFactor.nativeFactors,
      CoefficientMarkedRecordChoiceFactor.native] using
      CoefficientMarkedRecordChoiceFactor.specializes hn ht ha ctx R k hk hR requested) tau

theorem specializes_family (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    let G := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R
    let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
    (fun requested tau => MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (polynomial hn ht ha ctx k hk.le requested tau)) =
      native (IntegralMixedFramedPhysicalLayoutCongruence.layout
        (IntegralMixedFramedHistoryFamilyBits.commands (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) key)) (G.state key) (G.birth_bound key)
        (CoefficientMarkedRecordCutSelection.familySelection G key) := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  let G := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let selected : CoefficientMarkedRecordCutSelection.KindSelection
      (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R) :=
    ⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
      c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩
  have HE := funext (fun requested => funext (fun tau =>
    specializes_native hn ht ha ctx R k hk.le hR requested tau))
  let M := layout (IntegralMixedFramedHistoryFamilyBits.commands
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) key)
  have HT := native_transport (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk.le) M x (G.state key)
    (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk.le) (G.birth_bound key)
    selected (CoefficientMarkedRecordCutSelection.familySelection G key)
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_cap hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordRows.family_source hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk.le aux).symm
    (CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk.le aux)
    (CoefficientMarkedRecordCutSelection.selection_heq hn ht ha ctx R k hk hc aux)
  exact HE.trans HT

end LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysical
