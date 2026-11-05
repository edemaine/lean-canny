/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureProductStratum
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.List.OfFn
/-! # Exact zero counts preserve every feature sign on connected strata -/
@[expose] public section
namespace LeanCanny.Geometry.SquareFeatureSignStratum
open Set Filter LeanCanny.Algebra
open scoped Classical Topology BigOperators

noncomputable def zeros {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) (x : X) : Finset ι :=
  Finset.univ.filter (fun i => f i x = 0)

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- Nonzero values persist locally; a constant total zero count forbids any
additional coordinate from leaving zero in that same neighborhood. -/
theorem locally_constant_zeros (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (k : ℕ)
    (hk : ∀ x, (zeros f x).card = k) : IsLocallyConstant (zeros f) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have HR : ∀ᶠ y in 𝓝 x, ∀ i, f i x ≠ 0 → f i y ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases HI : f i x = 0
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h HI))
    · have HO : IsOpen {y : X | f i y ≠ 0} := (hf i).isOpen_preimage _ isOpen_ne
      filter_upwards [HO.mem_nhds HI] with y hy
      exact fun _ => hy
  filter_upwards [HR] with y hy
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra hx
    exact hy i hx hi
  · exact (hk x).trans (hk y).symm |>.le

theorem locally_constant_sign (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (k : ℕ)
    (hk : ∀ x, (zeros f x).card = k) (i : ι) : IsLocallyConstant (fun x => SignType.sign (f i x)) := by
  have HZ := locally_constant_zeros f hf k hk
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  rcases lt_trichotomy (f i x) 0 with HN | HE | HP
  · filter_upwards [(isOpen_lt (hf i) continuous_const).mem_nhds HN] with y hy
    rw [sign_neg hy, sign_neg HN]
  · filter_upwards [HZ.eventually_eq x] with y hy
    have HI : i ∈ zeros f x := by simp [zeros, HE]
    rw [←hy] at HI
    have HY : f i y = 0 := (Finset.mem_filter.mp HI).2
    rw [HY, HE]
  · filter_upwards [(isOpen_lt continuous_const (hf i)).mem_nhds HP] with y hy
    rw [sign_pos hy, sign_pos HP]

theorem sign_eq_of_preconnected (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (k : ℕ)
    {s : Set X} (hs : IsPreconnected s) (hk : ∀ x ∈ s, (zeros f x).card = k)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) (i : ι) : SignType.sign (f i x) = SignType.sign (f i y) := by
  let _ : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let g : ι → s → ℝ := fun j z => f j z.val
  have HG : ∀ j, Continuous (g j) := fun j => (hf j).comp continuous_subtype_val
  have HC : ∀ z : s, (zeros g z).card = k := fun z => hk z.val z.property
  exact (locally_constant_sign g HG k HC i).apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩

/-- List multiplicities count the INDEXED zero features, not distinct values. -/
theorem zeroCount_ofFn (n : ℕ) (a : Fin n → ℝ) :
    SquareFeatureProduct.zeroCount (List.ofFn a) = (Finset.univ.filter (fun i => a i = 0)).card := by
  have HE : ∀ n (a : Fin n → ℝ), SquareFeatureProduct.zeroCount (List.ofFn a) =
      ∑ i : Fin n, if a i = 0 then 1 else 0 := by
    intro n
    induction n with
    | zero => intro a; simp [SquareFeatureProduct.zeroCount]
    | succ n ih =>
        intro a
        rw [List.ofFn_succ, SquareFeatureProduct.zeroCount_cons, Fin.sum_univ_succ, ih]
        split_ifs <;> omega
  rw [HE, Finset.card_filter]

theorem sign_eq_on_equation_stratum (n : ℕ) (f : Fin n → X → ℝ) (hf : ∀ i, Continuous (f i)) (k : ℕ)
    {s : Set X} (hs : IsPreconnected s)
    (hEq : ∀ x ∈ s, ∃ w : ℝ, SquareFeatureProduct.equation (List.ofFn (fun i => f i x)) k w = 0)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) (i : Fin n) :
    SignType.sign (f i x) = SignType.sign (f i y) := by
  apply sign_eq_of_preconnected f hf k hs ?_ hx hy i
  intro z hz
  have HZ := (SquareFeatureProduct.exists_equation_iff _ k).mp (hEq z hz)
  rw [zeroCount_ofFn] at HZ
  exact HZ

end LeanCanny.Geometry.SquareFeatureSignStratum
