/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CoerciveComponentEliminants
/-! # Actual critical limits meet clopen pieces of an unbounded polynomial zero set

Normal separation supplies a closed isolating neighborhood without compactness.
Coercive minimization on that closed set is attained, and comparison with one
fixed zero bounds every minimizer in a single compact penalty sublevel.
-/
@[expose] public section
namespace LeanCanny.Geometry.UnboundedCoerciveComponents
open Set Filter MvPolynomial CoercivePolynomialSampling CoerciveComponentSampling LeanCanny.Algebra
open scoped Topology Classical
variable {n : ℕ}

theorem isolating_neighborhood (q : MvPolynomial (Fin n) ℝ)
    (C : Set (Zeros q)) (hC : IsClopen C) :
    ∃ S : Set (Fin n → ℝ), IsClosed S ∧ Subtype.val '' C⊆S ∧
      (∀ a, eval a q=0 → a∈S → a∈Subtype.val '' C) ∧ Subtype.val '' C⊆interior S := by
  let A : Set (Fin n → ℝ) := Subtype.val '' C
  let B : Set (Fin n → ℝ) := Subtype.val '' Cᶜ
  have HZ : IsClosed (Zeros q) := isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have HA : IsClosed A := HZ.isClosedEmbedding_subtypeVal.isClosedMap C hC.isClosed
  have HB : IsClosed B := HZ.isClosedEmbedding_subtypeVal.isClosedMap Cᶜ hC.compl.isClosed
  have HAB : A⊆Bᶜ := by
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,HE⟩
    have H : w=z := Subtype.ext HE
    exact hw (H.symm ▸ hz)
  obtain ⟨U,HU,HAU,HUB⟩ := normal_exists_closure_subset HA HB.isOpen_compl HAB
  refine ⟨closure U,isClosed_closure,HAU.trans subset_closure,?_,?_⟩
  · intro a hq hS
    by_contra HN
    have HNC : (⟨a,hq⟩ : Zeros q)∉C := fun H => HN ⟨⟨a,hq⟩,H,rfl⟩
    exact HUB hS ⟨⟨a,hq⟩,HNC,rfl⟩
  · exact HAU.trans (interior_maximal subset_closure HU)

theorem exists_critical_limits (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (C : Set (Zeros q)) (hC : IsClopen C)
    (x0 : Zeros q) (hx0 : x0∈C) (s : ℕ → ℝ) (hs : ∀ k, 0 < s k)
    (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Zeros q) (φ : ℕ → ℕ), a∈C ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 a.val) ∧
      (∀ k, penalty D (y k)≤penalty D x0.val) ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k)) (pderiv j (regularization q D (s (φ k))))=0 := by
  obtain ⟨S,hS,HA,HS,HI⟩ := isolating_neighborhood q C hC
  obtain ⟨y,a,φ,_hy,hm,hb,hφ,hlim,ha,hq⟩ :=
    CoerciveConstrainedSampling.exists_minimizers_subsequence_on q D S hS x0.val
      (HA ⟨x0,hx0,rfl⟩) x0.property s hs hs0
  have HAC : a∈Subtype.val '' C := HS a hq ha
  have HA' : (⟨a,hq⟩ : Zeros q)∈C := by
    obtain ⟨z,hz,HE⟩ := HAC
    have HZ : z=(⟨a,hq⟩ : Zeros q) := Subtype.ext HE
    exact HZ ▸ hz
  refine ⟨y,⟨a,hq⟩,φ,HA',hφ,hlim,hb,?_⟩
  filter_upwards [hlim.eventually (isOpen_interior.mem_nhds (HI HAC))] with k hk
  have HN : S∈𝓝 (y (φ k)) := mem_interior_iff_mem_nhds.mp hk
  have HL : IsLocalMin (fun x => eval x (regularization q D (s (φ k)))) (y (φ k)) := by
    simpa only [eval_regularization] using (hm (φ k)).isLocalMin HN
  exact (PolynomialCalculus.critical_iff (RingHom.id ℝ) _ _).mp HL.fderiv_eq_zero

theorem meets_piece (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D)
    (C : Set (CoerciveComponentSampling.Zeros q)) (hC : IsClopen C)
    (x0 : CoerciveComponentSampling.Zeros q) (hx0 : x0∈C) :
    ∃ a : CoerciveComponentSampling.Zeros q, a∈C ∧ a.val∈CoerciveComponentEliminants.grid q D := by
  let s : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have HS : ∀ k, 0 < s k := fun k => by dsimp [s]; positivity
  have HS0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨y,a,φ,HA,Hφ,HL,_HB,HC⟩ := exists_critical_limits q D C hC x0 hx0 s HS HS0
  refine ⟨a,HA,?_⟩
  intro i
  apply CoerciveComponentEliminants.trailing_root (ParametricCoerciveEliminant.polynomial q D i) (s ∘ φ) (fun k => y (φ k) i) (a.val i)
    (fun k => ne_of_gt (HS (φ k))) (HS0.comp Hφ.tendsto_atTop) ((continuous_apply i).continuousAt.tendsto.comp HL)
  filter_upwards [HC] with k hk
  have HX : ∀ j, eval (y (φ k)) (pderiv j (CoerciveCriticalFibers.polynomial (q.map (RingHom.id ℝ)) D (s (φ k))))=0 := by
    simpa only [MvPolynomial.map_id,CoercivePolynomialSampling.regularization,CoerciveCriticalFibers.polynomial] using hk
  exact ParametricCoerciveEliminant.eval_eq_zero (RingHom.id ℝ) q D hD i (s (φ k)) (y (φ k)) HX

end LeanCanny.Geometry.UnboundedCoerciveComponents
