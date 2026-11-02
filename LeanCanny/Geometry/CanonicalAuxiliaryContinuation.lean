/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryFiniteGrid
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateCommand
public import LeanCanny.Algebra.IntegralMixedDilationAdvance

/-! # A constructed component representative extends the actual tagged history

A bounded virtual trajectory supplies the selected factor root. The literal
limitCoordinate cut command retains its next ORIGINAL coordinate and extends
the same old real hom, physical tuple and bank values. Reframing advances k while
leaving the auxiliary tilt axis free. The next integer level capacity is chosen
separately; this theorem does not reuse an old level value or old dilated Y_k.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling IntegralMixedCanonicalDilation
open IntegralMixedDilationAdvance UniformIntegralPowerSchedule
open Set
open scoped Classical
variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type} [Fintype ι]

theorem continue_component (x : State (source k D t ht m B G) S B m ι) (hm : m≤S) (hmNext : m+1≤S)
    (HG : x.bank.Bounds G) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m → ℝ) (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (ha : t.arity≤n) (hk : k<n) (hD : 0<D) (select : Fin k → Fin m) (a : Fin n → ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, a j=values (select ⟨j.val,hj⟩))
    (C : Set (slice (polynomial n t) k a)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) k a) (hx0 : x0∈C) (nextLevelCoefficient : ℤ) :
    let r := rule (by omega : k≤n+1) select
    let j := coordinateIndex (by omega : k≤n+1) select (⟨k,by omega⟩:Fin (n+1)) (Nat.le_refl k)
    ∃ b : slice (polynomial n t) k a, b∈C ∧
    ∃ c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) r),
      IntegralMixedLimitCoordinate.Valid x hm r j φ c ∧
    ∃ d : ℕ, ∃ hd : d≤IntegralMixedLimitCoordinate.degree (source k D t ht m B G) r,
      let born := IntegralMixedFullHistoryScript.step x hm (IntegralMixedLimitCoordinate.command x r j c d hd)
      let next := advance born (Fin.last n) nextLevelCoefficient
      ∃ y : (ι ⊕ Unit) → ℝ, ∃ ψ : next.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, (next.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i, y (Sum.inl i)=z i) ∧
        (ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ) ∧
        (∀ i, ψ (next.sampler.scalarPrefix.basis.generator i)=y (next.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
        (∀ i, ψ (next.bank.numerator i)/(next.bank.denominator i:ℝ)=
          (Fin.cons (b.val ⟨k,hk⟩) values : Fin (m+1) → ℝ) i) ∧
        ∀ (eta v : ℝ) i,
          i.val<(rule (by omega : k+1≤n+1) (nextSelector select)).critical.offset.val →
          ((data next hmNext (rule (by omega : k+1≤n+1) (nextSelector select)).critical).scales i:ℝ)*
            point (k:=k+1) next eta (Fin.snoc b.val 0) v i=
          heightValue next (rule (by omega : k+1≤n+1) (nextSelector select)) ψ eta i := by
  dsimp only
  let r := rule (by omega : k≤n+1) select
  let j0 : Fin (n+1) := ⟨k,by omega⟩
  let j := coordinateIndex (by omega : k≤n+1) select j0 (by exact Nat.le_refl k)
  obtain ⟨b,hb,hr⟩ := meets_selected_factors x hm HG φ values H ha (by omega : k≤n) hD select a Hparam C hC x0 hx0
  obtain ⟨c,hc⟩ := IntegralMixedLimitCoordinate.exists_valid x hm r j φ
  have HT : (Fin.snoc b.val (0:ℝ) : Fin (n+1) → ℝ) j0=b.val ⟨k,hk⟩ := by
    have HE : j0=(⟨k,hk⟩:Fin n).castSucc := Fin.ext rfl
    exact (congrArg (Fin.snoc b.val (0:ℝ) : Fin (n+1) → ℝ) HE).trans (Fin.snoc_castSucc _ _ _)
  have HRoot := hr j0 (by exact Nat.le_refl k) c hc
  rw [HT] at HRoot
  obtain ⟨d,hd,y,ψ,hy,hyold,hrestrict,hψ,Hnew⟩ := IntegralMixedLimitCoordinate.real_extend_correlated
    x hm r j φ c hc z hz hφ values H (b.val ⟨k,hk⟩) HRoot
  refine ⟨b,hb,c,hc,d,hd,y,ψ,hy,hyold,hrestrict,hψ,Hnew,?_⟩
  intro eta v
  apply advanced_frozen _ (Fin.last n) nextLevelCoefficient hmNext (by omega : k<n+1)
    select ψ values (b.val ⟨k,hk⟩) Hnew eta (Fin.snoc b.val 0) v _ HT
  intro i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · intro hi
    have HN : n<k := hi
    omega
  · intro hi
    change l.val<k at hi
    rw [Fin.snoc_castSucc]
    exact (b.property.2 l hi).trans (Hparam l hi)

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
