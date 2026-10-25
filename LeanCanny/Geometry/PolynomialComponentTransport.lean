/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularComponentTransport
public import LeanCanny.Geometry.ComponentCriticalSampling

/-! # Component transport between exceptional polynomial levels

A critical-value annihilator constructs finitely many exceptional levels.
For a proper polynomial, connection of any two continuous sections within the
level fibers is constant on every preconnected region avoiding those levels.
All analytic chart and regularity hypotheses are derived from the polynomial.
This does not yet construct the recursive roadmap or its space bounds.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialComponentTransport
open Set MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An actual polynomial exceptional set controls component transport for
all continuous sections, including algebraic critical branches. -/
theorem exists_exceptional (p : MvPolynomial ι ℝ)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ c : Polynomial ℝ, c ≠ 0 ∧ {t : ℝ | c.eval t = 0}.Finite ∧
      ∀ (S : Set ℝ) [PreconnectedSpace S], (∀ t ∈ S, c.eval t ≠ 0) →
        ∀ (s d : S → ι → ℝ), Continuous s → Continuous d →
          (∀ t, p.eval (s t) = t.val) → (∀ t, p.eval (d t) = t.val) →
          ∀ a b : S,
            JoinedIn {x | p.eval x = a.val} (s a) (d a) ↔
              JoinedIn {x | p.eval x = b.val} (s b) (d b) := by
  obtain ⟨c, hc, hcm⟩ := Algebra.CriticalValueAnnihilator.exists_annihilator p
  refine ⟨c, hc, Polynomial.finite_setOfPred_isRoot hc, ?_⟩
  intro S _ havoid s d hs hd hps hpd a b
  have hsmooth : ContDiff ℝ 1 (fun x : ι → ℝ => p.eval x) :=
    (ProjectionCritical.contDiff_eval (RingHom.id ℝ) p).of_le le_top
  exact RegularComponentTransport.joined_sections_iff (fun x : ι → ℝ => p.eval x) S hp
    (fun _ _ => hsmooth.contDiffAt)
    (fun x hx => ComponentCriticalSampling.regular_level_of_annihilator p c hcm
      (p.eval x) (havoid _ hx) x rfl) hs hd hps hpd a b

end LeanCanny.Geometry.PolynomialComponentTransport
