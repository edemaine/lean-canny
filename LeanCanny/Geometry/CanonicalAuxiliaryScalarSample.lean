/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryFramedSample
public import LeanCanny.Algebra.IntegralMixedFramedScalarValidation

/-! # Original component samples in the canonical square prefix

Actual scalar-only run variables are indexed newest first by Fin m. This
transports literal roots and the same interpreting hom, with all coordinate
quotients preserved. Prefix annihilators therefore validate these samples
without regularity assumptions. Native input padding and advice remain separate.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript (Instruction run)
open AuxiliaryTiltedTerm CoerciveComponentSampling UniformIntegralPowerSchedule
open scoped Classical

def CanonicalOriginalRealization {a n S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (p : Fin n→ℝ) : Prop :=
  ∃ z : Fin m→ℝ, (∀ i, (x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) ∧
  ∃ φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=z i^weights S (2^B) m i) ∧
    ∀ i : Fin n, ∃ j : Fin m, j.val=frontIndex n i.val ∧
      p i=φ (x.bank.numerator j)/(x.bank.denominator j:ℝ)

theorem canonicalRealization_of_original {a n S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (H : ScalarOnly x.sampler) (p : Fin n→ℝ)
    (hp : OriginalRealization x p) : CanonicalOriginalRealization x p := by
  obtain ⟨z,hz,φ,hφ,hp⟩ := hp
  refine ⟨z ∘ x.sampler.scalar,?_,φ,hφ,hp⟩
  intro i
  have HR := hz (x.sampler.scalar i)
  rw [H.rows i,MvPolynomial.eval₂_rename] at HR
  exact HR

theorem IsLimitInstruction.not_critical {n B : ℕ} (c : Instruction n B) (h : IsLimitInstruction c) :
    c.command.isCritical=false := by
  cases hc : c.command with
  | integer p hp hd => rfl
  | critical r => simp only [IsLimitInstruction,hc] at h
  | cut r k d hs hd => rfl

theorem exists_closed_canonical_sample {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D)
    (ha : t.arity≤n) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (C : Set (Zeros (polynomial n t))) (hC : IsClopen C) (x0 : Zeros (polynomial n t)) (hx0 : x0∈C) :
    ∃ cs : List (Instruction (n+2) B), ∃ _ : cs.length=n, ∃ hcs : cs.length≤S+1,
      (∀ c∈cs, IsLimitInstruction c) ∧
      ∃ p : Zeros (polynomial n t), p∈C ∧
        CanonicalOriginalRealization (run (initialState (S:=S) t ht hcap) cs hcs) p.val := by
  obtain ⟨cs,hlen,hcs,hLimit,p,hp,hread⟩ := exists_closed_framed_sample t ht ha hn hcap C hC x0 hx0
  have H0 : ScalarOnly (initialState (S:=S) t ht hcap).sampler := base_scalarOnly S (2^B)
  have H := IntegralMixedFramedHistoryScript.scalarOnly_run _ H0 cs hcs
    (fun c hc => IsLimitInstruction.not_critical c (hLimit c hc))
  exact ⟨cs,hlen,hcs,hLimit,p,hp,canonicalRealization_of_original _ H p.val hread⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
