/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialLimitAnnihilator
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.ExtendFrom

/-! # Endpoint limits of bounded continuous algebraic branches

A bounded continuous branch satisfying a nonzero bivariate polynomial equation
has a limit as its parameter decreases to zero. Factoring the lowest parameter
power gives a nonzero univariate polynomial containing every possible limit.
Continuity makes the set of cluster values preconnected, so its finiteness
forces uniqueness. Neither nonsingularity nor a derivative bound is needed.

This establishes endpoint continuation for branches once their existence,
continuity and boundedness have been proved. It does not construct a roadmap
or bound its algebraic representation.
-/

@[expose] public section

namespace LeanCanny.Geometry.AlgebraicBranchLimit
open Set Filter Polynomial
open scoped Topology

/-- Cluster values of a continuous real-valued branch on a one-sided interval
form an interval. No boundedness hypothesis is needed for this statement. -/
theorem clusterValues_ordConnected {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Ioo a b)) :
    OrdConnected {x | MapClusterPt x (𝓝[>] a) f} := by
  constructor
  intro x hx y hy z hz
  change MapClusterPt z (𝓝[>] a) f
  rw [MapClusterPt, ((nhdsGT_basis a).map f).clusterPt_iff_forall_mem_closure]
  intro v hv
  let c := min v b
  have hac : a < c := lt_min hv hab
  have htail : f '' Ioo a c ∈ Filter.map f (𝓝[>] a) :=
    image_mem_map ((nhdsGT_basis a).mem_of_mem hac)
  have hxc : x ∈ closure (f '' Ioo a c) := hx.clusterPt.mem_closure_of_mem _ htail
  have hyc : y ∈ closure (f '' Ioo a c) := hy.clusterPt.mem_closure_of_mem _ htail
  have hsub : Ioo a c ⊆ Ioo a b := fun t ht => ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  have hconnected := (isPreconnected_Ioo.image f (hf.mono hsub)).closure
  have hzc := hconnected.ordConnected.out hxc hyc hz
  apply (closure_mono (image_mono (show Ioo a c ⊆ Ioo a v from ?_))) hzc
  intro t ht
  exact ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩

/-- Compactness supplies a cluster value; connectedness and a finite set of
possible values force the branch to converge to that one value. -/
theorem exists_tendsto_of_finite_clusterValues {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    {K : Set ℝ} (hK : IsCompact K) (hbound : ∀ᶠ t in 𝓝[>] a, f t ∈ K)
    (hfinite : {x | MapClusterPt x (𝓝[>] a) f}.Finite) :
    ∃ x ∈ K, Tendsto f (𝓝[>] a) (𝓝 x) := by
  obtain ⟨x, hxK, hx⟩ := hK.exists_mapClusterPt (Filter.le_principal_iff.mpr (Filter.mem_map.mpr hbound))
  have hc : IsPreconnected {x | MapClusterPt x (𝓝[>] a) f} :=
    (clusterValues_ordConnected hab hf).isPreconnected
  refine ⟨x, hxK, hK.tendsto_nhds_of_unique_mapClusterPt hbound ?_⟩
  intro y hyK hy
  by_contra hne
  exact hfinite.not_infinite (hc.infinite_of_nontrivial ⟨y, hy, x, hx, hne⟩)

private theorem cluster_pair {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {ι : Type*} {l : Filter ι} {f : ι → A} {g : ι → B} {a : A} {b : B}
    (hf : Tendsto f l (𝓝 a)) (hg : MapClusterPt b l g) :
    MapClusterPt (a, b) l (fun i => (f i, g i)) := by
  rw [((𝓝 a).basis_sets.prod_nhds (𝓝 b).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  exact ((hg.frequently ht).and_eventually (hf.eventually hs)).mono fun _ h => ⟨h.2, h.1⟩

/-- Evaluate the outer variable at the curve parameter and the coefficient
variable at the branch value. -/
noncomputable def value (p : Polynomial (Polynomial ℝ)) (t x : ℝ) : ℝ :=
  p.eval₂ (Polynomial.evalRingHom x) t

theorem continuous_value (p : Polynomial (Polynomial ℝ)) :
    Continuous (fun z : ℝ × ℝ => value p z.1 z.2) := by
  unfold value
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply continuous_finsetSum
  intro i _
  exact (((p.coeff i).continuous).comp continuous_snd).mul (continuous_fst.pow i)

/-- All cluster values satisfy the lowest nonzero parameter coefficient. The
factorization removes the apparent degeneracy when specializing at zero. -/
theorem clusterValue_isRoot (p : Polynomial (Polynomial ℝ)) {f : ℝ → ℝ}
    (hzero : ∀ᶠ t in 𝓝[>] (0 : ℝ), value p t (f t) = 0)
    {x : ℝ} (hx : MapClusterPt x (𝓝[>] (0 : ℝ)) f) :
    p.trailingCoeff.eval x = 0 := by
  obtain ⟨q, hq, hq0⟩ := LeanCanny.Algebra.InfinitesimalSign.factor_at_trailingDegree p
  have hzq : ∀ᶠ t in 𝓝[>] (0 : ℝ), value q t (f t) = 0 := by
    filter_upwards [hzero, self_mem_nhdsWithin] with t ht htpos
    have htnz : t ≠ 0 := ne_of_gt htpos
    unfold value at ht ⊢
    rw [hq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at ht
    exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ htnz)
  have hp := cluster_pair
    (show Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds) hx
  have hvalue := hp.continuousAt_comp (continuous_value q).continuousAt
  have hv : value q 0 x = 0 :=
    isClosed_singleton.mem_of_mapClusterPt hvalue hzq
  simpa only [value, Polynomial.eval₂_at_zero, hq0,
    Polynomial.coe_evalRingHom] using hv

/-- Every bounded continuous root branch of a nonzero real bivariate
polynomial extends to a unique limit at parameter zero, even at singular
fibers. The endpoint is a root of the lowest nonzero parameter coefficient. -/
theorem exists_limit (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0)
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : ContinuousOn f (Ioo 0 b))
    {K : Set ℝ} (hK : IsCompact K) (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ K)
    (hzero : ∀ᶠ t in 𝓝[>] (0 : ℝ), value p t (f t) = 0) :
    ∃ x ∈ K, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 x) ∧
      p.trailingCoeff.eval x = 0 := by
  have htc : p.trailingCoeff ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hroots : {x : ℝ | p.trailingCoeff.eval x = 0}.Finite :=
    Polynomial.finite_setOfPred_isRoot htc
  have hfinite : {x | MapClusterPt x (𝓝[>] (0 : ℝ)) f}.Finite :=
    hroots.subset (fun _ hx => clusterValue_isRoot p hzero hx)
  obtain ⟨x, hxK, hlim⟩ := exists_tendsto_of_finite_clusterValues hb hf hK hbound hfinite
  exact ⟨x, hxK, hlim, clusterValue_isRoot p hzero hlim.mapClusterPt⟩

private theorem tendsto_add_right (a : ℝ) :
    Tendsto (fun t : ℝ => a + t) (𝓝[>] (0 : ℝ)) (𝓝[>] a) := by
  rw [(nhdsGT_basis 0).tendsto_iff (nhdsGT_basis a)]
  intro v hv
  refine ⟨v - a, sub_pos.mpr hv, ?_⟩
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

private theorem tendsto_sub_right (a : ℝ) :
    Tendsto (fun t : ℝ => t - a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) := by
  rw [(nhdsGT_basis a).tendsto_iff (nhdsGT_basis 0)]
  intro v hv
  refine ⟨a + v, by linarith, ?_⟩
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

private theorem value_translate (p : Polynomial (Polynomial ℝ)) (a t x : ℝ) :
    value (p.comp (X + C (C a))) t x = value p (a + t) x := by
  simp [value, Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_X, add_comm]

/-- Translation gives a limit at any finite left endpoint, including an
algebraic endpoint at which the defining polynomial becomes singular. -/
theorem exists_right_limit (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0)
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    {K : Set ℝ} (hK : IsCompact K) (hbound : ∀ t ∈ Ioo a b, f t ∈ K)
    (hzero : ∀ t ∈ Ioo a b, value p t (f t) = 0) :
    ∃ x ∈ K, Tendsto f (𝓝[>] a) (𝓝 x) := by
  let q : Polynomial (Polynomial ℝ) := p.comp (X + C (C a))
  have hq : q ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hshift : MapsTo (fun t : ℝ => a + t) (Ioo 0 (b - a)) (Ioo a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hc : ContinuousOn (fun t => f (a + t)) (Ioo 0 (b - a)) :=
    hf.comp (by fun_prop) hshift
  have hinterval : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (b - a) :=
    (nhdsGT_basis 0).mem_of_mem (sub_pos.mpr hab)
  have hB : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (a + t) ∈ K :=
    hinterval.mono fun t ht => hbound _ (hshift ht)
  have hZ : ∀ᶠ t in 𝓝[>] (0 : ℝ), value q t (f (a + t)) = 0 := by
    filter_upwards [hinterval] with t ht
    change value (p.comp (X + C (C a))) t (f (a + t)) = 0
    rw [value_translate]
    exact hzero _ (hshift ht)
  obtain ⟨x, hx, hlim, _⟩ := exists_limit q hq (sub_pos.mpr hab) hc hK hB hZ
  refine ⟨x, hx, ?_⟩
  simpa only [Function.comp_def, add_sub_cancel] using hlim.comp (tendsto_sub_right a)

private theorem tendsto_neg_left (b : ℝ) :
    Tendsto (fun t : ℝ => -t) (𝓝[<] b) (𝓝[>] (-b)) := by
  rw [(nhdsLT_basis b).tendsto_iff (nhdsGT_basis (-b))]
  intro v hv
  refine ⟨-v, by linarith, ?_⟩
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

private theorem value_reflect (p : Polynomial (Polynomial ℝ)) (t x : ℝ) :
    value (p.comp (-X)) t x = value p (-t) x := by
  simp [value, Polynomial.eval₂_comp]

theorem exists_left_limit (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0)
    {a b : ℝ} {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    {K : Set ℝ} (hK : IsCompact K) (hbound : ∀ t ∈ Ioo a b, f t ∈ K)
    (hzero : ∀ t ∈ Ioo a b, value p t (f t) = 0) :
    ∃ x ∈ K, Tendsto f (𝓝[<] b) (𝓝 x) := by
  let q : Polynomial (Polynomial ℝ) := p.comp (-X)
  have hq : q ≠ 0 := Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp
  have hreflect : MapsTo (fun t : ℝ => -t) (Ioo (-b) (-a)) (Ioo a b) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hc : ContinuousOn (fun t => f (-t)) (Ioo (-b) (-a)) :=
    hf.comp (by fun_prop) hreflect
  have hZ : ∀ t ∈ Ioo (-b) (-a), value q t (f (-t)) = 0 := by
    intro t ht
    change value (p.comp (-X)) t (f (-t)) = 0
    rw [value_reflect]
    exact hzero _ (hreflect ht)
  obtain ⟨x, hx, hlim⟩ := exists_right_limit q hq (by linarith : -b < -a) hc hK
    (fun t ht => hbound _ (hreflect ht)) hZ
  refine ⟨x, hx, ?_⟩
  simpa only [Function.comp_def, neg_neg] using hlim.comp (tendsto_neg_left b)

/-- Coordinate equations suffice to extend an entire vector-valued algebraic
branch continuously to the closed parameter interval. -/
theorem continuous_extension {ι : Type*} {a b : ℝ} {f : ℝ → ι → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (K : ι → Set ℝ) (hK : ∀ i, IsCompact (K i))
    (hbound : ∀ t ∈ Ioo a b, ∀ i, f t i ∈ K i)
    (hzero : ∀ t ∈ Ioo a b, ∀ i, value (p i) t (f t i) = 0) :
    ∃ g : ℝ → ι → ℝ, ContinuousOn g (Icc a b) ∧ EqOn g f (Ioo a b) := by
  have hc (i : ι) : ContinuousOn (fun t => f t i) (Ioo a b) :=
    (continuous_apply i).comp_continuousOn hf
  choose x hx hxlim using fun i => exists_right_limit (p i) (hp i) hab (hc i) (hK i)
    (fun t ht => hbound t ht i) (fun t ht => hzero t ht i)
  choose y hy hylim using fun i => exists_left_limit (p i) (hp i) hab (hc i) (hK i)
    (fun t ht => hbound t ht i) (fun t ht => hzero t ht i)
  have hl : Tendsto f (𝓝[>] a) (𝓝 x) := tendsto_pi_nhds.mpr hxlim
  have hr : Tendsto f (𝓝[<] b) (𝓝 y) := tendsto_pi_nhds.mpr hylim
  exact ⟨extendFrom (Ioo a b) f, continuousOn_Icc_extendFrom_Ioo hf hl hr,
    extendFrom_extends hf⟩

end LeanCanny.Geometry.AlgebraicBranchLimit
