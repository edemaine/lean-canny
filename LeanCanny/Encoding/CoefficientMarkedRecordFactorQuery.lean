/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCutSource
/-! # Untruncated causal factors at alternative query choices

The prefix is the actual original trace. Only the queried choice changes;
higher-coefficient guards retain the full factor before birth truncation.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedFactorSpecialization
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralMixedCausalRecordBits Polynomial
open scoped Classical
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ} {P : SpatialSource n}

noncomputable def formalFactor (bank : CoefficientHeightBank R A m) (low : MvPolynomial (Fin (n + 1)) R)
    (a : R) (r : IntegralMixedCriticalSweep.Rule n) (current : Bool) (c : Kind P r) : Polynomial A :=
  CoefficientMixedCutDispatcher.factor bank low a r (CoefficientMixedCutSpecialization.slope bank r current) c

noncomputable def nativeFactor {S B : ℕ} {I : Type} (x : State P S B m I) (hm : m ≤ S)
    (r : IntegralMixedCriticalSweep.Rule n) (current : Bool) (c : Kind P r) :=
  IntegralMixedRelativeCuts.factor x hm (CoefficientMixedCutSpecialization.nativeRule x r current)
    (CoefficientMixedCutSpecialization.nativeKind x r current c)

theorem map_native {S B : ℕ} {I : Type} (bank : CoefficientHeightBank R A m)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (x : State P S B m I) (hm : m ≤ S)
    (r : IntegralMixedCriticalSweep.Rule n) (current : Bool) (c : Kind P r)
    (φ : R →+* ℤ) (ψ : A →+* x.sampler.scalarPrefix.carrier)
    (HB : CoefficientHeightBank.Specializes φ ψ bank (CoefficientHeightBank.ofState x))
    (HL : low.map φ = P.low) (HA : φ a = P.leading) :
    (formalFactor bank low a r current c).map ψ = nativeFactor x hm r current c := by
  cases current
  · dsimp only [formalFactor, nativeFactor, CoefficientMixedCutSpecialization.slope,
      CoefficientMixedCutSpecialization.nativeRule, CoefficientMixedCutSpecialization.nativeKind]
    rw [CoefficientMixedCutDispatcher.factor_map HB, HL, HA, map_intCast]
    exact CoefficientMixedCutDispatcher.factor_ofState x hm r c
  · dsimp only [formalFactor, nativeFactor, CoefficientMixedCutSpecialization.slope,
      CoefficientMixedCutSpecialization.nativeRule, CoefficientMixedCutSpecialization.nativeKind]
    rw [CoefficientMixedCutDispatcher.factor_map HB, HL, HA, HB.commonDenominator]
    exact CoefficientMixedCutDispatcher.factor_currentQ_ofState x hm r c

def queriedCut {n B : ℕ} {P : SpatialSource n} (c : Cut P B) (choice : ℕ) : Cut P B :=
  { c with choice := choice }

theorem queried_transport {n B : ℕ} {P Q : SpatialSource n} (hd : P.degree = Q.degree) (c : Cut P B) (choice : ℕ) :
    CoefficientMixedCutSourceDegree.cut hd (queriedCut c choice) =
      queriedCut (CoefficientMixedCutSourceDegree.cut hd c) choice := rfl

theorem native_retarget {n S B m : ℕ} {P Q : SpatialSource n} {I : Type}
    (hd : P.degree = Q.degree) (x : State Q S B m I) (hm : m ≤ S) (c : Cut P B) :
    nativeFactor x hm (c.rule 1 one_ne_zero) c.current
      (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero)) =
      IntegralMixedRelativeCuts.factor x hm
        ((CoefficientMixedCutSourceDegree.cut hd c).rule (commonDenominator x) (commonDenominator_ne_zero x))
        ((CoefficientMixedCutSourceDegree.cut hd c).kind (commonDenominator x) (commonDenominator_ne_zero x)) := by
  cases P
  cases Q
  dsimp only at hd
  cases hd
  rcases c with ⟨cr, h, hf, tag, j, k, d, hs, hb, cur⟩
  cases cur <;> cases tag <;> rfl

end LeanCanny.Algebra.CoefficientMixedFactorSpecialization

namespace LeanCanny.Encoding.CoefficientMarkedRecordFactorQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open CoefficientMixedFactorSpecialization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev selected (ctx : List Bool) (k choice : ℕ) :=
  queriedCut (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k) choice

noncomputable def factor (ctx : List Bool) (k choice : ℕ) :
    Polynomial (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).carrier :=
  let c := selected hn ht ha ctx k choice
  formalFactor (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).bank
    (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
    (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero)

noncomputable def polynomial (ctx : List Bool) (k choice : ℕ) :
    Polynomial (MvPolynomial (Fin (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ℤ[X]) :=
  (CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k).basis.polynomial (factor hn ht ha ctx k choice)

noncomputable def native (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (choice : ℕ) :
    Polynomial (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk).sampler.scalarPrefix.carrier :=
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  let c := queriedCut (CoefficientMarkedRecordNative.cut hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)) choice
  IntegralMixedRelativeCuts.factor x (CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (c.kind (commonDenominator x) (commonDenominator_ne_zero x))

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (choice : ℕ) :
    (polynomial hn ht ha ctx k choice).map (MvPolynomial.map (evalRingHom ((2 : ℤ) ^ R ctx))) =
      (CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk).sampler.scalarPrefix.basis.polynomial
        (native hn ht ha ctx R k hk choice) := by
  let F := CoefficientMarkedRecordCutSource.stagePrefix hn ht ha ctx k
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk
  let c := selected hn ht ha ctx k choice
  let low := CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx
  let a := CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx
  let hd := CoefficientMarkedRecordNative.source_degree (n := n) (t := t) ctx R
  have hm := CoefficientMarkedRecordCutSource.birth_room hn ht ha ctx k hk
  obtain ⟨ψ, hb, hg, _, _⟩ :=
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR).pointwise
  have hs := CoefficientMarkedRecordNative.source_fields (n := n) (t := t) ctx R
  have HE := map_native F.bank low a x hm (c.rule 1 one_ne_zero) c.current
    (CoefficientMixedCutSourceDegree.kind hd (c.rule 1 one_ne_zero) (c.kind 1 one_ne_zero))
    (evalRingHom ((2 : ℤ) ^ R ctx)) ψ hg hs.1 hs.2
  unfold formalFactor at HE
  rw [CoefficientMixedCutSourceDegree.factor_eq hd F.bank low a (c.rule 1 one_ne_zero)
    (CoefficientMixedCutSpecialization.slope F.bank (c.rule 1 one_ne_zero) c.current) (c.kind 1 one_ne_zero)] at HE
  rw [native_retarget] at HE
  dsimp only [c, selected] at HE
  rw [queried_transport, CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)] at HE
  change ((F.basis.polynomial (factor hn ht ha ctx k choice)).map _) = _
  rw [hb.polynomial_map, CoefficientCoordinateBasis.ofIntegral_polynomial]
  exact congrArg x.sampler.scalarPrefix.basis.polynomial HE

end LeanCanny.Encoding.CoefficientMarkedRecordFactorQuery
