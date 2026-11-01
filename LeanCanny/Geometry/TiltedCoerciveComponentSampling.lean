/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CoerciveComponentSampling
public import LeanCanny.Algebra.CoerciveCriticalFibers
/-! # Positive-component maxima as limits of tilted coercive critical points

The auxiliary threshold is used only to construct a compact isolating
neighborhood. It is absent from the critical polynomial. A linear objective
tilt makes each limit retain a positive coordinate and the same clopen label.
-/
@[expose] public section
namespace LeanCanny.Geometry.TiltedCoerciveComponentSampling
open Set Filter MvPolynomial CoercivePolynomialSampling
open scoped Classical Topology
variable {n : ℕ}

noncomputable abbrev Positive (q : MvPolynomial (Fin n) ℝ) (u : Fin n) :=
  {x : CoerciveComponentSampling.Zeros q // 0 < x.val u}

noncomputable def polynomial (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n) (s : ℝ) :
    MvPolynomial (Fin n) ℝ := regularization q D (s^2)-C s*X u

noncomputable def objective (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n) (s : ℝ)
    (x : Fin n → ℝ) : ℝ := (q.eval x)^2-s*x u+s^2*penalty D x

theorem eval_polynomial (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n) (s : ℝ) (x : Fin n → ℝ) :
    (polynomial q D u s).eval x=objective q D u s x := by
  rw [polynomial,eval_sub,eval_regularization,eval_mul,eval_C,eval_X]
  unfold objective CoercivePolynomialSampling.objective
  ring

theorem continuous_objective (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n) (s : ℝ) :
    Continuous (objective q D u s) :=
  (((MvPolynomial.continuous_eval q).pow 2).sub (continuous_const.mul (continuous_apply u))).add
    (continuous_const.mul (continuous_penalty D))

theorem compact_isolation (K : Set (Fin n → ℝ)) (hK : IsCompact K) (C : Set K) (hC : IsClopen C) :
    ∃ S : Set (Fin n → ℝ), IsCompact S ∧ Subtype.val '' C⊆S ∧
      (∀ a∈K, a∈S → a∈Subtype.val '' C) ∧ Subtype.val '' C⊆interior S := by
  let A : Set (Fin n → ℝ) := Subtype.val '' C
  let B : Set (Fin n → ℝ) := Subtype.val '' Cᶜ
  have HA : IsClosed A := hK.isClosed.isClosedEmbedding_subtypeVal.isClosedMap C hC.isClosed
  have HB : IsClosed B := hK.isClosed.isClosedEmbedding_subtypeVal.isClosedMap Cᶜ hC.compl.isClosed
  have HAK : A⊆K := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have HAc : IsCompact A := hK.of_isClosed_subset HA HAK
  have HAB : A⊆Bᶜ := by
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,HE⟩
    have H : w=z := Subtype.ext HE
    exact hw (H.symm ▸ hz)
  obtain ⟨U,HU,HAU,HUB⟩ := HAc.exists_isOpen_closure_subset (HB.isOpen_compl.mem_nhdsSet.mpr HAB)
  obtain ⟨R,HR⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let V : Set (Fin n → ℝ) := U∩Metric.ball 0 (R+1)
  have HV : IsOpen V := HU.inter Metric.isOpen_ball
  have HAV : A⊆V := by
    intro x hx
    refine ⟨HAU hx,?_⟩
    change dist x 0<R+1
    rw [dist_zero_right]
    exact (HR (mem_image_of_mem _ (HAK hx))).trans_lt (lt_add_one R)
  have HC : IsCompact (closure V) :=
    (isCompact_closedBall (0 : Fin n → ℝ) (R+1)).of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ h => Metric.ball_subset_closedBall h.2) Metric.isClosed_closedBall)
  refine ⟨closure V,HC,HAV.trans subset_closure,?_,HAV.trans (interior_maximal subset_closure HV)⟩
  intro a ha hS
  by_contra HN
  have HNC : (⟨a,ha⟩ : K)∉C := fun H => HN ⟨⟨a,ha⟩,H,rfl⟩
  exact HUB (closure_mono inter_subset_left hS) ⟨⟨a,ha⟩,HNC,rfl⟩

theorem exists_positive_critical_limits (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (u : Fin n)
    (hcompact : IsCompact (CoerciveComponentSampling.Zeros q))
    (C : Set (Positive q u)) (hC : IsClopen C) (x0 : Positive q u) (hx0 : x0∈C)
    (s : ℕ → ℝ) (hs : ∀ k, 0 < s k) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Positive q u) (φ : ℕ → ℕ), a∈C ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 a.val.val) ∧ x0.val.val u≤a.val.val u ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k)) (pderiv j (polynomial q D u (s (φ k))))=0 := by
  let δ := x0.val.val u/2
  have Hδ : 0 < δ := half_pos x0.property
  have Hδx : δ < x0.val.val u := half_lt_self x0.property
  let K : Set (Fin n → ℝ) := CoerciveComponentSampling.Zeros q∩{x | δ≤x u}
  have HK : IsCompact K := hcompact.inter_right (isClosed_le continuous_const (continuous_apply u))
  let P : K → Positive q u := fun z => ⟨⟨z.val,z.property.1⟩,Hδ.trans_le z.property.2⟩
  have HP : Continuous P := (continuous_subtype_val.subtype_mk _).subtype_mk _
  let CK : Set K := P ⁻¹' C
  have HCK : IsClopen CK := hC.preimage HP
  let xK : K := ⟨x0.val.val,x0.val.property,Hδx.le⟩
  have HXK : xK∈CK := hx0
  obtain ⟨S,HS,HA,HI,Hinter⟩ := compact_isolation K HK CK HCK
  have HX : x0.val.val∈S := HA ⟨xK,HXK,rfl⟩
  choose y hy hm using fun k => HS.exists_isMinOn ⟨x0.val.val,HX⟩
    (continuous_objective q D u (s k)).continuousOn
  obtain ⟨a,ha,φ,Hφ,HL⟩ := HS.tendsto_subseq hy
  obtain ⟨M,HM⟩ := HS.bddAbove_image (continuous_apply u).continuousOn
  have Hcompare (k : ℕ) : (q.eval (y k))^2-s k*(y k u)+(s k)^2*penalty D (y k)≤
      -s k*x0.val.val u+(s k)^2*penalty D x0.val.val := by
    have H := hm k HX
    change objective q D u (s k) (y k)≤objective q D u (s k) x0.val.val at H
    unfold objective at H
    rw [x0.val.property] at H
    simpa only [zero_pow (by decide : 2≠0),zero_sub,neg_mul] using H
  have Hres (k : ℕ) : (q.eval (y k))^2≤s k*(M-x0.val.val u)+(s k)^2*penalty D x0.val.val := by
    have HN := mul_nonneg (sq_nonneg (s k)) (penalty_nonneg D (y k))
    have HU := mul_le_mul_of_nonneg_left (HM (mem_image_of_mem _ (hy k))) (hs k).le
    nlinarith [Hcompare k]
  have HT := hs0.comp Hφ.tendsto_atTop
  have Hbound : Tendsto (fun k => s (φ k)*(M-x0.val.val u)+(s (φ k))^2*penalty D x0.val.val)
      atTop (𝓝 0) := by
    simpa using (HT.mul_const (M-x0.val.val u)).add ((HT.pow 2).mul_const (penalty D x0.val.val))
  have Hq := ((MvPolynomial.continuous_eval q).continuousAt.tendsto.comp HL).pow 2
  have Hle := le_of_tendsto_of_tendsto Hq Hbound (Eventually.of_forall (fun k => Hres (φ k)))
  have Hroot : q.eval a=0 := sq_eq_zero_iff.mp (le_antisymm Hle (sq_nonneg _))
  have Hlower (k : ℕ) : x0.val.val u-s k*penalty D x0.val.val≤y k u := by
    apply (mul_le_mul_iff_right₀ (hs k)).mp
    have HN := mul_nonneg (sq_nonneg (s k)) (penalty_nonneg D (y k))
    nlinarith [Hcompare k,sq_nonneg (q.eval (y k))]
  have HU : x0.val.val u≤a u := by
    have HT' : Tendsto (fun k => x0.val.val u-s (φ k)*penalty D x0.val.val) atTop (𝓝 (x0.val.val u)) := by
      simpa using tendsto_const_nhds.sub (HT.mul_const (penalty D x0.val.val))
    exact le_of_tendsto_of_tendsto HT' ((continuous_apply u).continuousAt.tendsto.comp HL)
      (Eventually.of_forall (fun k => Hlower (φ k)))
  have HAK : a∈K := ⟨Hroot,(Hδx.trans_le HU).le⟩
  have HAC : a∈Subtype.val '' CK := HI a HAK ha
  have HCa : (⟨a,HAK⟩ : K)∈CK := by
    obtain ⟨z,hz,HE⟩ := HAC
    have HZ : z=(⟨a,HAK⟩ : K) := Subtype.ext HE
    exact HZ ▸ hz
  refine ⟨y,P ⟨a,HAK⟩,φ,HCa,Hφ,HL,HU,?_⟩
  filter_upwards [HL.eventually (isOpen_interior.mem_nhds (Hinter HAC))] with k hk
  have HN : S∈𝓝 (y (φ k)) := mem_interior_iff_mem_nhds.mp hk
  have Hmin : IsLocalMin (fun x => eval x (polynomial q D u (s (φ k)))) (y (φ k)) := by
    simpa only [eval_polynomial] using (hm (φ k)).isLocalMin HN
  exact (PolynomialCalculus.critical_iff (RingHom.id ℝ) _ _).mp Hmin.fderiv_eq_zero

end LeanCanny.Geometry.TiltedCoerciveComponentSampling
