/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryFramedRun
public import LeanCanny.Geometry.CanonicalAuxiliaryClosedSampling

/-! # A literal framed-run sample in each original clopen piece

The final tuple and interpreting hom belong to the ACTUAL source-framed run.
The bank-only terminal reframe is removed from the statement. All instructions
are tagged limit cuts, their number is exactly n, and bank index n-1-i recovers
each original coordinate. Native advice/ordinal serialization remains separate.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction Index run)
open AuxiliaryTiltedTerm CoerciveComponentSampling UniformIntegralPowerSchedule
open scoped Classical

def OriginalRealization {a n S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (p : Fin n → ℝ) : Prop :=
  ∃ z : ι → ℝ, (∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) ∧
  ∃ φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
    (∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) ∧
    ∀ i : Fin n, ∃ j : Fin m, j.val=frontIndex n i.val ∧
      p i=φ (x.bank.numerator j)/(x.bank.denominator j:ℝ)

theorem originalRealization_reframe {a b n S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (Q : SpatialSource b) (hQ : PurePowerReductionBounds.dimension (b+1) Q.degree≤2^B)
    (p : Fin n → ℝ) : OriginalRealization (reframe x Q hQ) p ↔ OriginalRealization x p := Iff.rfl

theorem originalRealization_of_heq {a n S B m m' : ℕ} {P : SpatialSource a} {ι κ : Type}
    (x : State P S B m ι) (y : State P S B m' κ) (hm : m=m') (hindex : ι=κ) (hxy : HEq x y)
    (p : Fin n → ℝ) (hy : OriginalRealization y p) : OriginalRealization x p := by
  subst m'
  subst κ
  have HE : x=y := eq_of_heq hxy
  rw [HE]
  exact hy

variable {n S B D : ℕ}

theorem exists_closed_framed_sample (t : Term) (ht : (term n t).degreeBound≤D) (ha : t.arity≤n) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (C : Set (Zeros (polynomial n t))) (hC : IsClopen C) (x0 : Zeros (polynomial n t)) (hx0 : x0∈C) :
    ∃ cs : List (Instruction (n+2) B), ∃ _ : cs.length=n, ∃ hcs : cs.length≤S+1,
      (∀ c∈cs, IsLimitInstruction c) ∧
      ∃ p : Zeros (polynomial n t), p∈C ∧
        OriginalRealization (run (initialState (S:=S) t ht hcap) cs hcs) p.val := by
  obtain ⟨L,_,hbirth,htrace,p,hp,hread⟩ := exists_closed_sample t ht ha hn hcap C hC x0 hx0
  obtain ⟨cs,hlen,hcs,hLimit,hIndex,hState⟩ := htrace.exists_framed_run hn hcap
  have HL : OriginalRealization L.state p.val := ⟨L.root,L.root_eq,L.hom,L.interprets,hread⟩
  have HR := originalRealization_of_heq
    (reframe (run (initialState (S:=S) t ht hcap) cs hcs)
      (source L.frozen D t ht L.birth B L.height) L.state.critical_cap)
    L.state (hlen.trans hbirth.symm) hIndex hState p.val HL
  exact ⟨cs,hlen,hcs,hLimit,p,hp,(originalRealization_reframe _ _ _ _).mp HR⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
