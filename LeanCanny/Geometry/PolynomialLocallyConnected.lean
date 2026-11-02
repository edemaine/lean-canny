/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialBallComponents
public import LeanCanny.Geometry.FiniteComponentNeighborhoods
/-! # Every closed real polynomial zero set is locally connected

Squared-distance sublevels form actual neighborhoods of each old tuple. Their
finite connected components are supplied by the explicit one-slack polynomial
lift. No regularity, compactness or component oracle is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialLocallyConnected
open Set Filter MvPolynomial CoerciveComponentSampling
open scoped Classical Topology
variable {n : ℕ}

theorem locallyConnected (q : MvPolynomial (Fin n) ℝ) : LocallyConnectedSpace (Zeros q) := by
  apply FiniteComponentNeighborhoods.locallyConnected
  intro x U HU
  obtain ⟨ε,hε,HE⟩ := Metric.mem_nhds_iff.mp HU
  let K : Set (Zeros q) := {y | SquaredDistanceFibers.value x.val y.val≤(ε/2)^2}
  have HG : Continuous (fun y : Zeros q => SquaredDistanceFibers.value x.val y.val) :=
    (SquaredDistanceFibers.continuous_value x.val).comp continuous_subtype_val
  have H0 : SquaredDistanceFibers.value x.val x.val=0 := (SquaredDistanceFibers.zero_iff _ _).mpr rfl
  have HN : K∈𝓝 x := by
    have HH : {y : Zeros q | SquaredDistanceFibers.value x.val y.val<(ε/2)^2}∈𝓝 x :=
      (isOpen_lt HG continuous_const).mem_nhds (by change SquaredDistanceFibers.value x.val x.val<(ε/2)^2; rw [H0]; positivity)
    apply Filter.mem_of_superset HH
    intro y hy
    change SquaredDistanceFibers.value x.val y.val≤(ε/2)^2
    exact le_of_lt hy
  refine ⟨K,HN,?_,PolynomialBallComponents.components_finite q x.val ((ε/2)^2)⟩
  intro y hy
  apply HE
  change dist y.val x.val<ε
  rw [dist_pi_lt_iff hε]
  intro i
  have HI : (y.val i-x.val i)^2≤SquaredDistanceFibers.value x.val y.val :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y.val j-x.val j)) (Finset.mem_univ i)
  have HS : (y.val i-x.val i)^2≤(ε/2)^2 := HI.trans hy
  have HA : |y.val i-x.val i|≤ε/2 := (sq_le_sq₀ (abs_nonneg _) (by linarith)).mp (by simpa only [sq_abs] using HS)
  change |y.val i-x.val i|<ε
  exact HA.trans_lt (by linarith)
end LeanCanny.Geometry.PolynomialLocallyConnected
