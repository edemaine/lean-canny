/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CoerciveConstrainedSampling
/-! # Coercive critical limits meet each clopen piece of a compact singular zero set

A closed isolating neighborhood is constructed from the actual zero-set
piece. Its boundary contains no original zero. Constrained minimizers therefore
become unconstrained critical points eventually, without regularity of the
original zero set or its defining sum of squares.
-/
@[expose] public section
namespace LeanCanny.Geometry.CoerciveComponentSampling
open Set Filter MvPolynomial CoercivePolynomialSampling
open scoped Topology Classical
variable {n : ℕ}

noncomputable abbrev Zeros (q : MvPolynomial (Fin n) ℝ) := {x : Fin n → ℝ | eval x q=0}

theorem isolating_neighborhood (q : MvPolynomial (Fin n) ℝ)
    (hcompact : IsCompact (Zeros q)) (C : Set (Zeros q)) (hC : IsClopen C) :
    ∃ S : Set (Fin n → ℝ), IsClosed S ∧ Subtype.val '' C⊆S ∧
      (∀ a, eval a q=0 → a∈S → a∈Subtype.val '' C) ∧ Subtype.val '' C⊆interior S := by
  let A : Set (Fin n → ℝ) := Subtype.val '' C
  let B : Set (Fin n → ℝ) := Subtype.val '' Cᶜ
  have HZ : IsClosed (Zeros q) := hcompact.isClosed
  have HA : IsClosed A := HZ.isClosedEmbedding_subtypeVal.isClosedMap C hC.isClosed
  have HB : IsClosed B := HZ.isClosedEmbedding_subtypeVal.isClosedMap Cᶜ hC.compl.isClosed
  have HAc : IsCompact A := hcompact.of_isClosed_subset HA (by rintro _ ⟨z,_,rfl⟩; exact z.property)
  have HAB : A⊆Bᶜ := by
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,HE⟩
    have H : w=z := Subtype.ext HE
    exact hw (H.symm ▸ hz)
  obtain ⟨U,HU,HAU,HUB⟩ := HAc.exists_isOpen_closure_subset (HB.isOpen_compl.mem_nhdsSet.mpr HAB)
  refine ⟨closure U,isClosed_closure,HAU.trans subset_closure,?_,?_⟩
  · intro a hq hS
    by_contra HN
    have HNC : (⟨a,hq⟩ : Zeros q)∉C := fun H => HN ⟨⟨a,hq⟩,H,rfl⟩
    exact HUB hS ⟨⟨a,hq⟩,HNC,rfl⟩
  · exact HAU.trans (interior_maximal subset_closure HU)

theorem exists_critical_limits (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (hcompact : IsCompact (Zeros q)) (C : Set (Zeros q)) (hC : IsClopen C)
    (x0 : Zeros q) (hx0 : x0∈C) (s : ℕ → ℝ) (hs : ∀ k, 0 < s k)
    (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → (Fin n → ℝ)) (a : Zeros q) (φ : ℕ → ℕ), a∈C ∧ StrictMono φ ∧
      Tendsto (y ∘ φ) atTop (𝓝 a.val) ∧
      (∀ k, penalty D (y k)≤penalty D x0.val) ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k)) (pderiv j (regularization q D (s (φ k))))=0 := by
  obtain ⟨S,hS,HA,HS,HI⟩ := isolating_neighborhood q hcompact C hC
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

end LeanCanny.Geometry.CoerciveComponentSampling
