/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalPrefix
public import LeanCanny.Geometry.CanonicalAuxiliaryFramedSample
public import LeanCanny.Algebra.IntegralMixedFramedScalarOnly

/-! # A zero default birth gives positive canonical sampling without losing a point

The original point and its literal bank quotients persist. Coordinate i moves
from index n-1-i to n-i. The new newest scalar is exactly zero, including when
the original dimension and script length are both zero.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra IntegralMixedHistory IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryScript
open scoped Classical

private theorem scalar_roots {S N m : ℕ} {ι : Type} (F : Sampler S N m ι) (H : ScalarOnly F)
    (y : ι→ℝ) (hy : ∀ j,(F.rows j).eval₂ (Int.castRingHom ℝ) y=0) (i : Fin m) :
    (F.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) (y ∘ F.scalar)=0 := by
  have HI := hy (F.scalar i)
  rw [H.rows i,MvPolynomial.eval₂_rename] at HI
  exact HI

theorem canonical_zero_readback {a n S B : ℕ} {P : SpatialSource a}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction a B)) (hcs : cs.length≤S+1) (hm : cs.length≤S)
    (hc : ∀ c∈cs,c.command.isCritical=false) (p : Fin n→ℝ)
    (hp : OriginalRealization (run initial cs hcs) p) :
    let hnew : (zeroInstruction initial::cs).length≤S+1 := by simp only [List.length_cons]; omega
    ∃ w : Fin (cs.length+1)→ℝ,
    ∃ ψ : (run initial (zeroInstruction initial::cs) hnew).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,((run initial (zeroInstruction initial::cs) hnew).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) w=0) ∧
      w 0=0 ∧
      (∀ i,ψ ((run initial (zeroInstruction initial::cs) hnew).sampler.scalarPrefix.basis.generator i)=
        w i^weights S (2^B) (cs.length+1) i) ∧
      ∀ i : Fin n, ∃ j : Fin (cs.length+1), j.val=n-i.val ∧
        p i=ψ ((run initial (zeroInstruction initial::cs) hnew).bank.numerator j)/
          ((run initial (zeroInstruction initial::cs) hnew).bank.denominator j:ℝ) := by
  obtain ⟨z,hz,φ,hφ,hread⟩ := hp
  obtain ⟨y,ψ,hy,_,hzero,_,hψ,_,hold⟩ := run_zero_real_extend initial cs hcs hm z hz φ hφ
  let hnew : (zeroInstruction initial::cs).length≤S+1 := by simp only [List.length_cons]; omega
  let next := run initial (zeroInstruction initial::cs) hnew
  have H0 : ScalarOnly initial.sampler := by
    constructor
    · constructor
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  have Hc : ∀ c∈zeroInstruction initial::cs,c.command.isCritical=false := by
    intro c hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rfl
    · exact hc c hmem
  have HS := scalarOnly_run initial H0 (zeroInstruction initial::cs) hnew Hc
  let w : Fin (cs.length+1)→ℝ := y ∘ next.sampler.scalar
  refine ⟨w,ψ,?_,hzero,hψ,?_⟩
  · intro i
    exact scalar_roots next.sampler HS y hy i
  · intro i
    obtain ⟨j,hj,hvalue⟩ := hread i
    refine ⟨j.succ,?_,hvalue.trans (hold j).symm⟩
    have HI := i.isLt
    change j.val+1=n-i.val
    unfold frontIndex at hj
    omega

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
