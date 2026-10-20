/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPowerHomotopy

/-! # Multidegrees for the pure-power Koszul differential

An exterior occurrence of coordinate `i` contributes the exponent vector
of its input power. The pure-power differential preserves the sum of these
vectors and the coefficient monomial exponent. This finer grading keeps the
chosen eligible coordinate fixed throughout each differential image.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def wordExponent (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) : Fin n →₀ ℕ :=
  ∑ j, Finsupp.single (v j) (d (v j))

noncomputable def subsetExponent (d : Fin n → ℕ) (s : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i (d i)

theorem wordExponent_succ (d : Fin n → ℕ) {k : ℕ} (v : Fin (k + 1) → Fin n) :
    wordExponent d v = Finsupp.single (v 0) (d (v 0)) + wordExponent d (Matrix.vecTail v) := by
  rw [wordExponent, Fin.sum_univ_succ]
  rfl

theorem wordExponent_cons (d : Fin n → ℕ) {k : ℕ} (i : Fin n) (v : Fin k → Fin n) :
    wordExponent d (Fin.cons i v) = Finsupp.single i (d i) + wordExponent d v := by
  rw [wordExponent_succ]
  rfl

theorem wordExponent_degree (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) :
    (wordExponent d v).degree = wordWeight d v := by
  simp only [wordExponent, map_sum, Finsupp.degree_single, wordWeight]

theorem wordExponent_image (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) :
    subsetExponent d (Finset.univ.image v) = wordExponent d v := by
  rw [subsetExponent, Finset.sum_image (by intro i _ j _ hij; exact hv hij)]
  rfl

theorem wordExponent_ordered (d : Fin n → ℕ) (s : Finset (Fin n)) {k : ℕ} (hs : s.card = k) :
    wordExponent d (s.orderEmbOfFin hs) = subsetExponent d s := by
  calc
    _ = ∑ i : s, Finsupp.single i.val (d i.val) :=
      Fintype.sum_equiv (s.orderIsoOfFin hs).toEquiv _ _ (fun _ => rfl)
    _ = _ := by
      unfold subsetExponent
      exact Finset.sum_coe_sort s (fun i => Finsupp.single i (d i))

theorem wordExponent_apply_of_not_mem (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (i : Fin n)
    (hi : i ∉ Set.range v) : wordExponent d v i = 0 := by
  rw [wordExponent, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Finsupp.single_eq_of_ne (fun hij => hi ⟨j, hij.symm⟩)

abbrev ComponentIndex (d : Fin n → ℕ) (t : Fin n →₀ ℕ) :=
  (k : ℕ) × (v : Fin k → Fin n) × {m : Fin n →₀ ℕ // m + wordExponent d v = t}

noncomputable def component (d : Fin n → ℕ) (t : Fin n →₀ ℕ) : Submodule R (Total n R) :=
  Submodule.span R (Set.range (fun a : ComponentIndex d t => monomialBlade (R := R) a.2.1 a.2.2.val))

theorem monomialBlade_mem_component (d : Fin n → ℕ) (t : Fin n →₀ ℕ) {k : ℕ} (v : Fin k → Fin n)
    (m : Fin n →₀ ℕ) (hm : m + wordExponent d v = t) : monomialBlade (R := R) v m ∈ component (R := R) d t :=
  Submodule.subset_span ⟨⟨k, v, m, hm⟩, rfl⟩

theorem wedge_component_mem (d : Fin n → ℕ) (t : Fin n →₀ ℕ) (i : Fin n) (x : Total n R)
    (hx : x ∈ component (R := R) d t) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x ∈
      component (R := R) d (Finsupp.single i (d i) + t) := by
  have hle : component (R := R) d t ≤ (component (R := R) d (Finsupp.single i (d i) + t)).comap
      ((KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)).restrictScalars R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v, m, hm⟩, rfl⟩
    change KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (monomialBlade (R := R) v m) ∈
      component (R := R) d (Finsupp.single i (d i) + t)
    rw [wedge_monomialBlade]
    apply monomialBlade_mem_component
    rw [wordExponent_cons, ← hm]
    ac_rfl
  exact hle hx

theorem powers_differential_word_mem_component (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m) ∈
      component (R := R) d (m + wordExponent d v) := by
  induction k with
  | zero => rw [differential_monomialBlade_zero]; exact Submodule.zero_mem _
  | succ k ih =>
    rw [differential_powers_succ]
    apply Submodule.sub_mem
    · rw [monomial_smul_monomialBlade]
      apply monomialBlade_mem_component
      rw [wordExponent_succ]
      ac_rfl
    · have hw := wedge_component_mem d (m + wordExponent d (Matrix.vecTail v)) (v 0) _ (ih (Matrix.vecTail v))
      have he : Finsupp.single (v 0) (d (v 0)) + (m + wordExponent d (Matrix.vecTail v)) = m + wordExponent d v := by
        rw [wordExponent_succ]
        ac_rfl
      simpa only [he] using hw

theorem powers_differential_component_mem (d : Fin n → ℕ) (t : Fin n →₀ ℕ) (x : Total n R)
    (hx : x ∈ component (R := R) d t) :
    KoszulExterior.differential (Macaulay.powers (R := R) d) x ∈ component (R := R) d t := by
  have hle : component (R := R) d t ≤ (component (R := R) d t).comap
      ((KoszulExterior.differential (Macaulay.powers (R := R) d)).restrictScalars R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v, m, hm⟩, rfl⟩
    change KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m) ∈ component (R := R) d t
    rw [← hm]
    exact powers_differential_word_mem_component d v m
  exact hle hx

end LeanCanny.Algebra.KoszulWeighted
