/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCutSource
public import LeanCanny.Algebra.CoefficientSelectedMultivariateLift
/-! # Constructed selected coordinate heads of actual canonical prefixes

The original record determines the rule and current-Q mode. The prefix
constructs every coefficient, basis representative and creating power.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCoordinateHead
open IntegralMixedHistory Polynomial
open scoped Classical
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
  {P : SpatialSource n} {cap width : ℕ} {ι : Type}

noncomputable def coordinate (bank : CoefficientHeightBank R A m)
    (low : MvPolynomial (Fin (n+1)) R) (leading : R) (D : ℕ)
    (r : IntegralMixedCriticalSweep.Rule n) (current : Bool) (j : Fin (n-r.critical.offset.val+1)) :=
  CoefficientMixedCriticalSweep.coordinateWithSlope bank low leading D r
    (CoefficientMixedCutSpecialization.slope bank r current) j

noncomputable def native (x : State P cap width m ι) (hm : m ≤ cap)
    (r : IntegralMixedCriticalSweep.Rule n) (current : Bool) (j : Fin (n-r.critical.offset.val+1)) :
    Polynomial (Polynomial x.sampler.scalarPrefix.carrier) :=
  match current with
  | false => IntegralMixedCriticalSweep.coordinate x hm r j
  | true => IntegralMixedCriticalSweep.coordinate x hm (CoefficientMixedCriticalSweep.currentRule x r) j

theorem map_native (bank : CoefficientHeightBank R A m) (low : MvPolynomial (Fin (n+1)) R) (a : R)
    (x : State P cap width m ι) (hm : m ≤ cap) (r : IntegralMixedCriticalSweep.Rule n)
    (current : Bool) (j : Fin (n-r.critical.offset.val+1))
    (φ : R →+* ℤ) (ψ : A →+* x.sampler.scalarPrefix.carrier)
    (HB : bank.Specializes φ ψ (CoefficientHeightBank.ofState x)) (HL : low.map φ = P.low) (HA : φ a = P.leading) :
    (coordinate bank low a P.degree r current j).map (Polynomial.mapRingHom ψ) = native x hm r current j := by
  cases current
  · dsimp only [coordinate, native, CoefficientMixedCutSpecialization.slope]
    rw [CoefficientMixedCriticalSweep.coordinateWithSlope_map HB, HL, HA, map_intCast]
    exact CoefficientMixedCriticalSweep.coordinateWithSlope_ofState x hm r j
  · dsimp only [coordinate, native, CoefficientMixedCutSpecialization.slope]
    rw [CoefficientMixedCriticalSweep.coordinateWithSlope_map HB, HL, HA, HB.commonDenominator]
    exact CoefficientMixedCriticalSweep.coordinate_currentQ_ofState x hm r j

end LeanCanny.Algebra.CoefficientMixedCoordinateHead

namespace LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev rule (ctx : List Bool) (k : ℕ) :=
  (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).rule 1 one_ne_zero

abbrev Coordinate (ctx : List Bool) (k : ℕ) :=
  Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3-(rule hn ht ha ctx k).critical.offset.val+1)

noncomputable def coordinate (ctx : List Bool) (k : ℕ) (j : Coordinate hn ht ha ctx k) :
    Polynomial (Polynomial (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).carrier) :=
  CoefficientMixedCoordinateHead.coordinate (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).bank
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx) (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.source (n := n) (t := t) ctx 0).degree (rule hn ht ha ctx k)
    (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).current j

noncomputable def weights (ctx : List Bool) (k : ℕ) : Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) → ℕ :=
  UniformIntegralPowerSchedule.weights (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)

noncomputable def polynomial (ctx : List Bool) (k : ℕ) (j : Coordinate hn ht ha ctx k) (d e : ℕ) :
    Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k+1)) ℤ[X]) :=
  CoefficientSelectedMultivariateLift.powered (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis
    (weights hn ht ha ctx k) (coordinate hn ht ha ctx k j) d e

noncomputable def native (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (j : Coordinate hn ht ha ctx k) :=
  CoefficientMixedCoordinateHead.native (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk)
    (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk) (rule hn ht ha ctx k)
    (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).current j

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (j : Coordinate hn ht ha ctx k) (d e : ℕ) :
    (polynomial hn ht ha ctx k j d e).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))) =
      SelectedMultivariatePolynomialLift.lift (native hn ht ha ctx R k hk j)
        (SelectedPoweredPolynomialLift.representative
          (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk).sampler.scalarPrefix.basis
          (weights hn ht ha ctx k)) d e := by
  let F := CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  obtain ⟨ψ, hb, hg, _, _⟩ :=
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR).pointwise
  have hs := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx R
  have HE := CoefficientMixedCoordinateHead.map_native F.bank
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx) (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    x (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk) (rule hn ht ha ctx k)
    (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).current j
    (evalRingHom ((2 : ℤ)^R ctx)) ψ hg hs.1 hs.2
  rw [← CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx R] at HE
  change (coordinate hn ht ha ctx k j).map (Polynomial.mapRingHom ψ) = native hn ht ha ctx R k hk j at HE
  change (CoefficientSelectedMultivariateLift.powered F.basis _ _ d e).map _ = _
  rw [CoefficientSelectedMultivariateLift.powered_map _ _ hb, HE,
    CoefficientSelectedMultivariateLift.powered_ofIntegral]

end LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
