/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
public import LeanCanny.Algebra.IntegralMixedCriticalRealExtension

/-! # Actual framed-run readback for a physical critical instruction

The new source is selected before the physical birth. Reframing retains the
literal old sampler, bank and interpreting hom; only the new critical block
and companion introduce coordinates.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory IntegralHistorySampler FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def criticalInstruction (Q : SpatialSource n)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (r : CriticalRule n) : Instruction n B :=
  ⟨Q,hcap,.critical r⟩

theorem run_critical (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (Q : SpatialSource n) (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (r : CriticalRule n)
    (h : (criticalInstruction Q hcap r::cs).length≤S+1) :
    run initial (criticalInstruction Q hcap r::cs) h=
      IntegralMixedHistory.criticalStep
        (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) Q hcap)
        (by simp only [List.length_cons] at h; omega) r := rfl

theorem run_critical_real_extend (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (Q : SpatialSource n) (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (r : CriticalRule n)
    (h : (criticalInstruction Q hcap r::cs).length≤S+1) (hd : Odd (Q.degree-1))
    (z : Index ι cs → ℝ)
    (hz : ∀ i, ((run initial cs (by simp only [List.length_cons] at h; omega)).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0)
    (φ : (run initial cs (by simp only [List.length_cons] at h; omega)).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ ((run initial cs (by simp only [List.length_cons] at h; omega)).sampler.scalarPrefix.basis.generator i)=
      z ((run initial cs (by simp only [List.length_cons] at h; omega)).sampler.scalar i)^weights S (2^B) cs.length i)
    (values : Fin cs.length → ℝ)
    (H : ∀ i, φ ((run initial cs (by simp only [List.length_cons] at h; omega)).bank.numerator i)/
      ((run initial cs (by simp only [List.length_cons] at h; omega)).bank.denominator i:ℝ)=values i)
    (a : Fin (n+1) → ℝ) :
    let old := reframe (run initial cs (by simp only [List.length_cons] at h; omega)) Q hcap
    let hm : cs.length≤S := by simp only [List.length_cons] at h; omega
    (∀ i, i.val<r.offset.val → ((data old hm r).scales i:ℝ)*a i=φ (expression old (r.heights i))) →
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) a=0 →
    (∀ i : Fin (n+1), r.offset.val ≤ i.val → i≠(data old hm r).free →
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) a=0) →
    let next := run initial (criticalInstruction Q hcap r::cs) h
    let t := a (ClearedCoordinateCritical.freeIndex r.offset.val ((family old hm r).fit []).le
      ((family old hm r).coordinate []))
    ∃ y : Index ι (criticalInstruction Q hcap r::cs) → ℝ,
    ∃ ψ : next.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ i, (next.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i, y (Sum.inl (Sum.inl i))=z i) ∧
      (∀ i, y (Sum.inl (ambient i))^physical S (2^B) cs.length=a i) ∧
      (ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ) ∧
      (∀ i, ψ (next.sampler.scalarPrefix.basis.generator i)=y (next.sampler.scalar i)^weights S (2^B) (cs.length+1) i) ∧
      ∀ i, ψ (next.bank.numerator i)/(next.bank.denominator i:ℝ)=(Fin.cons t values : Fin (cs.length+1) → ℝ) i := by
  dsimp only
  intro hf hp hg
  exact criticalStep_real_extend_correlated
    (reframe (run initial cs (by simp only [List.length_cons] at h; omega)) Q hcap)
    (by simp only [List.length_cons] at h; omega) r hd z hz φ hφ values H a hf hp hg

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
