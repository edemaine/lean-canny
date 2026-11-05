/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialBallComponents
public import LeanCanny.Geometry.PolynomialComponentPaths
public import LeanCanny.Geometry.SquaredDistanceProper
public import LeanCanny.Geometry.BoundedPathExhaustion
/-! # One outer ball preserves all connections between inner polynomial zeros

The actual one-slack ball polynomial has finitely many components. Paths in
those components attach every inner point to one of finitely many projected
representatives without leaving the inner section. Compact path exhaustion
then bounds the finitely many connections between the representatives.

The resulting radius is existential. No effective or binary radius bound is
asserted, and the original zero set may be singular and unbounded.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialInnerBallConnections
open Set Metric MvPolynomial CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def sectionSet (q : MvPolynomial (Fin n) ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  Zeros q ∩ {x | SquaredDistanceFibers.value 0 x ≤ r}

noncomputable abbrev lift (q : MvPolynomial (Fin n) ℝ) (r : ℝ) :=
  PolynomialBallComponents.polynomial q 0 r

noncomputable def representative (q : MvPolynomial (Fin n) ℝ) (r : ℝ)
    (i : ConnectedComponents (Zeros (lift q r))) : Zeros (lift q r) :=
  Classical.choose (ConnectedComponents.surjective_coe i)

theorem representative_spec (q : MvPolynomial (Fin n) ℝ) (r : ℝ)
    (i : ConnectedComponents (Zeros (lift q r))) :
    ConnectedComponents.mk (representative q r i) = i :=
  Classical.choose_spec (ConnectedComponents.surjective_coe i)

noncomputable def point (q : MvPolynomial (Fin n) ℝ) (r : ℝ)
    (i : ConnectedComponents (Zeros (lift q r))) : Fin n → ℝ :=
  PolynomialBallComponents.old (representative q r i).val

theorem inner_attachment (q : MvPolynomial (Fin n) ℝ) (r : ℝ)
    (x : Fin n → ℝ) (hx : x ∈ sectionSet q r) :
    ∃ i : ConnectedComponents (Zeros (lift q r)), JoinedIn (sectionSet q r) x (point q r i) := by
  let xx : PolynomialBallComponents.Section q 0 r := ⟨⟨x,hx.1⟩,hx.2⟩
  obtain ⟨z,hz⟩ := PolynomialBallComponents.projection_surjective q 0 r xx
  have HX : PolynomialBallComponents.old z.val = x :=
    congrArg (fun a : PolynomialBallComponents.Section q 0 r => a.val.val) hz
  let i := ConnectedComponents.mk z
  have HR : representative q r i ∈ connectedComponent z :=
    ConnectedComponents.coe_eq_coe'.mp (representative_spec q r i)
  have H := PolynomialComponentPaths.subtype_joined (lift q r) z (representative q r i) HR
  have HC : Continuous (PolynomialBallComponents.old (n := n)) :=
    continuous_pi (fun j => continuous_apply j.castSucc)
  have HP := H.map HC.continuousOn
  rw [HX] at HP
  refine ⟨i,HP.mono ?_⟩
  rintro y ⟨w,hw,rfl⟩
  let a := PolynomialBallComponents.projection q 0 r ⟨w,hw⟩
  exact ⟨a.val.property,a.property⟩

theorem exists_outer_radius (q : MvPolynomial (Fin n) ℝ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ M : ℕ, ∀ x y : Fin n → ℝ, x ∈ sectionSet q r → y ∈ sectionSet q r →
      (JoinedIn (Zeros q) x y ↔ JoinedIn (Zeros q ∩ closedBall 0 (M : ℝ)) x y) := by
  let I := ConnectedComponents (Zeros (lift q r))
  let : Finite I := PolynomialFiniteComponents.components_finite (lift q r) (lift q r).totalDegree le_rfl
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨M,hM⟩ := BoundedPathExhaustion.finite_marked_radius (Zeros q) (point q r)
  have HK : IsCompact (sectionSet q r) :=
    (SquaredDistanceFibers.compact_sublevel (0 : Fin n → ℝ) r hr).inter_left
      (isClosed_eq (MvPolynomial.continuous_eval q) continuous_const)
  obtain ⟨s,hs⟩ := (isBounded_iff_subset_closedBall (0 : Fin n → ℝ)).mp HK.isBounded
  obtain ⟨N,hN⟩ := exists_nat_ge s
  have HInner : sectionSet q r ⊆ Zeros q ∩ closedBall 0 ((max N M : ℕ) : ℝ) := by
    intro x hx
    refine ⟨hx.1,?_⟩
    apply closedBall_subset_closedBall (hN.trans ?_) (hs hx)
    exact_mod_cast le_max_left N M
  refine ⟨max N M,?_⟩
  intro x y hx hy
  constructor
  · intro hxy
    obtain ⟨i,hi⟩ := inner_attachment q r x hx
    obtain ⟨j,hj⟩ := inner_attachment q r y hy
    have HOld : sectionSet q r ⊆ Zeros q := inter_subset_left
    have HRep := ((hi.mono HOld).symm.trans hxy).trans (hj.mono HOld)
    have HMid := (hM i j).mp HRep
    have HMid' : JoinedIn (Zeros q ∩ closedBall 0 ((max N M : ℕ) : ℝ))
        (point q r i) (point q r j) :=
      HMid.mono (BoundedPathExhaustion.bounded_mono (Zeros q) (le_max_right N M))
    exact ((hi.mono HInner).trans HMid').trans (hj.mono HInner).symm
  · exact fun H => H.mono inter_subset_left

theorem exists_outer_ball (q : MvPolynomial (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℕ, ∀ x y : Fin n → ℝ, x ∈ Zeros q → y ∈ Zeros q →
      x ∈ closedBall 0 R → y ∈ closedBall 0 R →
      (JoinedIn (Zeros q) x y ↔ JoinedIn (Zeros q ∩ closedBall 0 (M : ℝ)) x y) := by
  have HR : 0 ≤ (n : ℝ) * R ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  obtain ⟨M,hM⟩ := exists_outer_radius q ((n : ℝ) * R ^ 2) HR
  have HSection (x : Fin n → ℝ) (hx : x ∈ Zeros q) (hball : x ∈ closedBall 0 R) :
      x ∈ sectionSet q ((n : ℝ) * R ^ 2) := by
    refine ⟨hx,?_⟩
    have HNorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hball
    have HS (i : Fin n) : (x i) ^ 2 ≤ R ^ 2 := by
      have HI : |x i| ≤ R := (norm_le_pi_norm x i).trans HNorm
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) hR).mpr HI
    calc
      SquaredDistanceFibers.value 0 x = ∑ i : Fin n, (x i) ^ 2 := by
        simp only [SquaredDistanceFibers.value, Pi.zero_apply, sub_zero]
      _ ≤ ∑ _i : Fin n, R ^ 2 := Finset.sum_le_sum (fun i _ => HS i)
      _ = (n : ℝ) * R ^ 2 := by simp
  exact ⟨M,fun x y hx hy hbx hby => hM x y (HSection x hx hbx) (HSection y hy hby)⟩

end LeanCanny.Geometry.PolynomialInnerBallConnections
