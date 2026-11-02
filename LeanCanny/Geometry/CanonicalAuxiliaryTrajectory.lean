/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenAuxiliaryTermSampling
public import LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
public import LeanCanny.Algebra.IntegralMixedCanonicalDilationRoot

/-! # Actual eta/Q critical trajectories over one selected retained hom

Bounded componentwise minimizers of the literal auxiliary integer term are
transported to the fixed-leading level source. Its level capacity is chosen
from the current retained bank. The virtual sweep parameter is eta=Q*s, so
E=eta/Q=s exactly. No physical retained-eta instruction or absolute norm-root
lifting is used to represent this varying family.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling IntegralMixedCanonicalDilation
open Set Filter
open scoped Classical Topology

noncomputable def source {n : ℕ} (k D : ℕ) (t : Term) (ht : (term n t).degreeBound≤D) (m B G : ℕ) :
    SpatialSource (n+2) :=
  FermatLevelLift.source (FixedLeadingTiltedSource.source k D (Fin.last n) (term n t) ht)
    (IntegralMixedCausalLevelCapacity.coefficient (n+1) D (FixedWidthPolynomial.count m B) G)

variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type}

theorem exists_series_roots (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (ha : t.arity≤n) (hk : k≤n) (hD : 0<D) (select : Fin k → Fin m) (a : Fin n → ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, a j=values (select ⟨j.val,hj⟩))
    (C : Set (slice (polynomial n t) k a)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) k a) (hx0 : x0∈C) :
    ∃ (y : ℕ → Fin (n+1) → ℝ) (b : slice (polynomial n t) k a) (eta : ℕ → ℝ),
      b∈C ∧ Tendsto y atTop (𝓝 (Fin.snoc b.val 0)) ∧ Tendsto eta atTop (𝓝 0) ∧
      (∀ i, eta i≠0) ∧
      ∀ᶠ i in atTop, ∀ j : Fin (n+1), ∀ hj : k≤j.val,
        (IntegralMixedLimitCoordinate.selectedSeries x hm (rule (by omega : k≤n+1) select)
          (coordinateIndex (by omega : k≤n+1) select j hj) φ).eval₂
          (Polynomial.evalRingHom (y i j)) (eta i)=0 := by
  let s : ℕ → ℝ := fun i => 1/((i:ℝ)+1)
  have HS : ∀ i, 0<s i := fun _ => by dsimp [s]; positivity
  have HS1 : ∀ i, s i≤1 := by
    intro i
    apply (div_le_one (by positivity : (0:ℝ)<(i:ℝ)+1)).mpr
    have HI := Nat.cast_nonneg (α:=ℝ) i
    linarith
  have HS0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y,b,θ,hb,hθ,hy,hf,hc⟩ := FrozenAuxiliaryTermSampling.exists_critical_limits
    t ha k hk a D C hC x0 hx0 s HS HS1 HS0
  let eta : ℕ → ℝ := fun i => (commonDenominator x:ℝ)*s (θ i)
  have HQ : (commonDenominator x:ℝ)≠0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  have HE : ∀ i, eta i/(commonDenominator x:ℝ)=s (θ i) := fun i => by dsimp [eta]; field_simp
  have Heta : Tendsto eta atTop (𝓝 0) := by
    change Tendsto (fun i => (commonDenominator x:ℝ)*s (θ i)) atTop (𝓝 0)
    simpa only [Function.comp_def,mul_zero] using (HS0.comp hθ.tendsto_atTop).const_mul (commonDenominator x:ℝ)
  have Hne : ∀ i, eta i≠0 := fun i => mul_ne_zero HQ (ne_of_gt (HS (θ i)))
  have HA : (term n t).arity≤n+1 := by rw [arity]; omega
  have HP : ∀ i : Fin (n+1), ∀ hi : i.val<k,
      (Fin.snoc b.val (0:ℝ) : Fin (n+1) → ℝ) i=φ (x.bank.numerator (select ⟨i.val,hi⟩))/(x.bank.denominator (select ⟨i.val,hi⟩):ℝ) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      have HN : n<k := hi
      omega
    · intro hi
      change j.val<k at hi
      rw [Fin.snoc_castSucc]
      exact (b.property.2 j hi).trans ((Hparam j hi).trans (H _).symm)
  have HL := IntegralMixedCausalLevelCapacity.eventually_level_critical atTop x HG φ k D select (Fin.last n)
    (term n t) ht HA hk hD eta (y ∘ θ) (Fin.snoc b.val 0) Heta hy (Eventually.of_forall Hne) HP (by
      filter_upwards [hc] with i hi
      simpa only [HE i,Function.comp_def] using hi)
  refine ⟨y ∘ θ,b,eta,hb,hy,Heta,Hne,?_⟩
  filter_upwards [HL] with i hi
  obtain ⟨v,_,hp,hg⟩ := hi
  intro j hj
  apply IntegralMixedCanonicalDilation.critical_root x hm (by omega : k≤n+1) select j hj φ values H
    (eta i) (y (θ i)) v _ hp hg
  intro l hl
  exact (hf (θ i) l hl).trans (Hparam ⟨l.val,by omega⟩ hl)

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
