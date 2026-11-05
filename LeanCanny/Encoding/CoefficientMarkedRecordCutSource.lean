/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
/-! # Constructed scalar-prefix coefficient polynomials for actual causal cuts -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

abbrev birth (ctx : List Bool) (k : ℕ) :=
  (CoefficientMarkedPreludeActual.indices n ctx).length + (CoefficientMarkedRecordActual.codes ctx k).length

noncomputable abbrev stagePrefix (ctx : List Bool) (k : ℕ) :=
  CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k)

noncomputable abbrev cut (ctx : List Bool) (k : ℕ) :=
  CoefficientMarkedRecordPrefix.cut hn ht ha ctx (birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)

noncomputable def raw (ctx : List Bool) (k : ℕ) : Polynomial (stagePrefix hn ht ha ctx k).carrier :=
  let c := cut hn ht ha ctx k
  CoefficientMixedCutSpecialization.raw (stagePrefix hn ht ha ctx k).bank
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree

noncomputable def polynomial (ctx : List Bool) (k : ℕ) :
    Polynomial (MvPolynomial (Fin (birth (n := n) ctx k)) ℤ[X]) :=
  (stagePrefix hn ht ha ctx k).basis.polynomial (raw hn ht ha ctx k)

noncomputable abbrev state (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :=
  CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)

theorem birth_room (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    birth (n := n) ctx k ≤ CoefficientMarkedRecordActual.horizon hn ht ha ctx := by
  rw [birth, CoefficientMarkedRecordActual.codes_length]
  exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk

noncomputable def nativeRaw (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) : Polynomial (state hn ht ha ctx R k hk).sampler.scalarPrefix.carrier :=
  let x := state hn ht ha ctx R k hk
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  IntegralMixedCutMatrix.raw x (birth_room hn ht ha ctx k hk)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) c.degree

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

/-- Every raw coefficient, not just the declared leading one, uses the actual causal cut. -/
theorem specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    (polynomial hn ht ha ctx k).map (MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R ctx))) =
      (state hn ht ha ctx R k hk).sampler.scalarPrefix.basis.polynomial (nativeRaw hn ht ha ctx R k hk) := by
  let F := stagePrefix hn ht ha ctx k
  let x := state hn ht ha ctx R k hk
  let c := cut hn ht ha ctx k
  let low := CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx
  let a := CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx
  have hm := birth_room hn ht ha ctx k hk
  obtain ⟨ψ, hb, hg, _, _⟩ :=
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR).pointwise
  have hs := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx R
  let hd := CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx R
  have HE := CoefficientMixedCutSpecialization.raw_map_native F.bank low a x hm
    (c.rule 1 one_ne_zero) c.current
    (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree
    (evalRingHom ((2 : ℤ) ^ R ctx)) ψ hg hs.1 hs.2
  rw [CoefficientMixedCutSourceDegree.raw_eq hd F.bank low a
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree] at HE
  rw [CoefficientMarkedRecordRawGrowth.raw_eq_original hn ht ha ctx R x hm
    (IntegralMixedCausalRecordPlanBits.code ctx k)] at HE
  change ((F.basis.polynomial (raw hn ht ha ctx k)).map _) = _
  rw [hb.polynomial_map, CoefficientCoordinateBasis.ofIntegral_polynomial]
  exact congrArg x.sampler.scalarPrefix.basis.polynomial HE

end LeanCanny.Encoding.CoefficientMarkedRecordCutSource
