/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoefficientMarkedRecordSpecialization
public import LeanCanny.Encoding.CoefficientMarkedRecordRawGrowth
public import LeanCanny.Algebra.CoefficientCoordinateDyadicTailBounds

/-! # Actual native growth bounds the formal next-cut matrix

The proved prefix maps on the parameter tail and the original native raw
profile supply scalar interpolation. No matrix mass or map is an input.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCoefficientBounds
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem topEntryBound_of_cutoff_le (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (C : ℕ)
    (hC : CoefficientMarkedRecordSpecialization.cutoff hn ht ha ctx
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k) ≤ C) :
    CoefficientMarkedRecordSpecialization.topEntryBound hn ht ha ctx
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k)) (IntegralMixedCausalRecordPlanBits.code ctx k)
      (IntegerPolynomialDyadic.massBudget C
        (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx)
        (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx)) := by
  let S := CoefficientMarkedRecordActual.horizon hn ht ha ctx
  let cs := CoefficientMarkedRecordActual.codes ctx k
  let F := CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs
  let code := IntegralMixedCausalRecordPlanBits.code ctx k
  let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx
    ((CoefficientMarkedPreludeActual.indices n ctx).length + cs.length) code
  let low := CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx
  let a := CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx
  let v : F.carrier := (CoefficientMixedCutSpecialization.raw F.bank low a
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree).coeff c.degree
  have room := CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le
  have hm : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S := by
    dsimp only [cs]
    rw [CoefficientMarkedRecordActual.codes_length]
    exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le
  let x (r : ℕ) := CoefficientMarkedRecordNative.run hn ht ha ctx (fun _ => r) S cs room
  let : ∀ r, CommRing (x r).sampler.scalarPrefix.carrier := fun r => (x r).sampler.scalarPrefix.ring
  have tail (r : ℕ) (hr : C ≤ r) :
      ∃ ψ : F.carrier →+* (x r).sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (evalRingHom ((2 : ℤ) ^ r)) ψ F.basis
        (CoefficientCoordinateBasis.ofIntegral (x r).sampler.scalarPrefix.basis) ∧
      ∀ i j, (Algebra.leftMulMatrix (x r).sampler.scalarPrefix.basis.finBasis (ψ v) i j).natAbs ≤
        2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * r +
          IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx) := by
    have hp := CoefficientMarkedRecordSpecialization.specializes hn ht ha ctx (fun _ => r) S cs room (hC.trans hr)
    obtain ⟨ψ, hb, hg, _, _⟩ := hp.pointwise
    refine ⟨ψ, hb, ?_⟩
    intro i j
    have hs := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx (fun _ => r)
    let hd := CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx (fun _ => r)
    have hmap := CoefficientMixedCutSpecialization.raw_map_native F.bank low a (x r) hm
      (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) c.degree
      (evalRingHom ((2 : ℤ) ^ r)) ψ hg hs.1 hs.2
    rw [CoefficientMixedCutSourceDegree.raw_eq hd F.bank low a
      (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree] at hmap
    have he := congrArg (fun p => p.coeff c.degree) hmap
    simp only [Polynomial.coeff_map] at he
    change ψ v = _ at he
    rw [he]
    exact CoefficientMarkedRecordRawGrowth.finite_basis_bound hn ht ha ctx (fun _ => r) k hk hc i j
  change ∀ i j, coefficientMass (Algebra.leftMulMatrix F.basis.basis v i j) ≤ _
  intro i j
  exact (CoefficientCoordinateDyadicBounds.degree_mass_of_tail F.basis
    (fun r => (x r).sampler.scalarPrefix.basis) v C _ _ tail i j).2

end LeanCanny.Encoding.CoefficientMarkedRecordCoefficientBounds
