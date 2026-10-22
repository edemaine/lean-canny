/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayKoszulExteriorBridge
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite weighted polynomial pieces of the Koszul exterior algebra

A generator consists of an exterior word and a monomial. Its total weight
is the monomial degree plus the sum of the input degrees in that word.
Fixed-width monomial ranks give a finite spanning family at each weight and
exterior degree. Repeated coordinates and different word orders are allowed;
the exterior algebra itself imposes the alternating relations.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

abbrev Poly (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R
abbrev Total (n : ℕ) (R : Type*) [CommRing R] := KoszulExterior.Total (Poly n R) (Fin n)

def wordWeight (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) : ℕ := ∑ j, d (v j)

theorem wordWeight_succ (d : Fin n → ℕ) {k : ℕ} (v : Fin (k + 1) → Fin n) :
    wordWeight d v = d (v 0) + wordWeight d (Matrix.vecTail v) := by
  exact Fin.sum_univ_succ _

theorem wordWeight_cons (d : Fin n → ℕ) {k : ℕ} (i : Fin n) (v : Fin k → Fin n) :
    wordWeight d (Fin.cons i v) = d i + wordWeight d v := by
  rw [wordWeight_succ]
  rfl

noncomputable def blade {k : ℕ} (v : Fin k → Fin n) : Total n R :=
  ExteriorAlgebra.ιMulti (Poly n R) k (fun j => Pi.single (v j) 1)

theorem blade_succ {k : ℕ} (v : Fin (k + 1) → Fin n) :
    blade (R := R) v = ExteriorAlgebra.ι (Poly n R) (Pi.single (v 0) 1 : Fin n → Poly n R) *
      blade (R := R) (Matrix.vecTail v) := by
  rw [blade, ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem blade_cons {k : ℕ} (i : Fin n) (v : Fin k → Fin n) :
    blade (R := R) (Fin.cons i v) =
      ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) * blade (R := R) v := by
  rw [blade_succ]
  rfl

theorem blade_zero (v : Fin 0 → Fin n) : blade (R := R) v = 1 :=
  ExteriorAlgebra.ιMulti_zero_apply _

noncomputable def monomialBlade {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) : Total n R :=
  MvPolynomial.monomial m (1 : R) • blade v

noncomputable def indices (d : Fin n → ℕ) (L W k : ℕ) (v : Fin k → Fin n) : Finset (Macaulay.Index n W) :=
  Finset.univ.filter (fun r => (FixedWidthPolynomial.vector n W r).degree + wordWeight d v = L)

theorem mem_indices (d : Fin n → ℕ) (L W k : ℕ) (v : Fin k → Fin n) (r : Macaulay.Index n W) :
    r ∈ indices d L W k v ↔ (FixedWidthPolynomial.vector n W r).degree + wordWeight d v = L := by
  simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev Index (d : Fin n → ℕ) (L W k : ℕ) := (v : Fin k → Fin n) × ↥(indices d L W k v)

noncomputable def generator (d : Fin n → ℕ) (L W k : ℕ) (a : Index d L W k) : Total n R :=
  monomialBlade a.1 (FixedWidthPolynomial.vector n W a.2.val)

noncomputable def space (d : Fin n → ℕ) (L W k : ℕ) : Submodule R (Total n R) :=
  Submodule.span R (Set.range (generator (R := R) d L W k))

theorem generator_mem (d : Fin n → ℕ) (L W k : ℕ) (a : Index d L W k) :
    generator (R := R) d L W k a ∈ space (R := R) d L W k :=
  Submodule.subset_span (Set.mem_range_self a)

instance space_finite (d : Fin n → ℕ) (L W k : ℕ) : Module.Finite R (space (R := R) d L W k) :=
  Module.Finite.span_of_finite R (Set.finite_range _)

theorem monomialBlade_mem (d : Fin n → ℕ) (L W k : ℕ) (hW : L < 2 ^ W)
    (v : Fin k → Fin n) (m : Fin n →₀ ℕ) (hm : m.degree + wordWeight d v = L) :
    monomialBlade (R := R) v m ∈ space (R := R) d L W k := by
  have hb (i : Fin n) : m i < 2 ^ W := by
    have hi : m i ≤ m.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact (hi.trans (by omega)).trans_lt hW
  let r := FixedWidthPolynomial.index n W m hb
  have hr : r ∈ indices d L W k v := by
    rw [mem_indices, FixedWidthPolynomial.vector_index]
    exact hm
  have h := generator_mem (R := R) d L W k ⟨v, r, hr⟩
  simpa only [generator, r, FixedWidthPolynomial.vector_index] using h

theorem space_eq_of_widths (d : Fin n → ℕ) (L W V k : ℕ) (hW : L < 2 ^ W) (hV : L < 2 ^ V) :
    space (R := R) d L W k = space (R := R) d L V k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact monomialBlade_mem d L V k hV a.1 _ ((mem_indices d L W k a.1 a.2.val).mp a.2.property)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact monomialBlade_mem d L W k hW a.1 _ ((mem_indices d L V k a.1 a.2.val).mp a.2.property)

theorem blade_eq_zero_of_lt {k : ℕ} (v : Fin k → Fin n) (hn : n < k) : blade (R := R) v = 0 := by
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hv
  have hinj : Function.Injective v := by
    intro i j hij
    exact hv (congrArg (fun t : Fin n => (Pi.single t 1 : Fin n → Poly n R)) hij)
  have hc := Fintype.card_le_of_injective v hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem space_eq_bot_of_lt (d : Fin n → ℕ) (L W k : ℕ) (hn : n < k) : space (R := R) d L W k = ⊥ := by
  apply eq_bot_iff.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change generator (R := R) d L W k a = 0
  rw [generator, monomialBlade, blade_eq_zero_of_lt a.1 hn, smul_zero]

theorem card_index_le (d : Fin n → ℕ) (L W k : ℕ) :
    Fintype.card (Index d L W k) ≤ n ^ k * FixedWidthPolynomial.count n W := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _v : Fin k → Fin n, FixedWidthPolynomial.count n W := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [Fintype.card_coe, Fintype.card_fin] using (Finset.card_le_univ (indices d L W k v))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

theorem smul_monomialBlade {k : ℕ} (a : R) (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    a • monomialBlade (R := R) v m = MvPolynomial.monomial m a • blade (R := R) v := by
  rw [monomialBlade, ← smul_assoc, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem homogeneous_smul_blade_mem (d : Fin n → ℕ) (L W k t : ℕ) (hW : L < 2 ^ W)
    (q : Poly n R) (hq : q.IsHomogeneous t) (v : Fin k → Fin n) (hv : t + wordWeight d v = L) :
    q • blade (R := R) v ∈ space (R := R) d L W k := by
  rw [q.as_sum, Finset.sum_smul]
  apply Submodule.sum_mem
  intro m hm
  have hg : m.degree = t := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hq.coeff_eq_zero h)
  rw [← smul_monomialBlade]
  exact Submodule.smul_mem _ _ (monomialBlade_mem d L W k hW v m (by omega))

theorem space_le_exteriorGrade (d : Fin n → ℕ) (L W k : ℕ) :
    space (R := R) d L W k ≤ (ExteriorAlgebra.exteriorPower (Poly n R) k (Fin n → Poly n R)).restrictScalars R := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range (Poly n R) k ⟨_, rfl⟩)

theorem wedge_generator (d : Fin n → ℕ) (L W k : ℕ) (i : Fin n) (a : Index d L W k) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (generator (R := R) d L W k a) ∈
      space (R := R) d (L + d i) W (k + 1) := by
  have hg := (mem_indices d L W k a.1 a.2.val).mp a.2.property
  have hr : a.2.val ∈ indices d (L + d i) W (k + 1) (Fin.cons i a.1) := by
    rw [mem_indices, wordWeight_cons]
    omega
  have he : KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (generator (R := R) d L W k a) =
      generator (R := R) d (L + d i) W (k + 1) ⟨Fin.cons i a.1, a.2.val, hr⟩ := by
    change KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)
      (MvPolynomial.monomial _ (1 : R) • blade a.1) = MvPolynomial.monomial _ (1 : R) • blade (Fin.cons i a.1)
    rw [map_smul, blade_cons]
    rfl
  rw [he]
  exact generator_mem _ _ _ _ _

theorem wedge_mem (d : Fin n → ℕ) (L W k : ℕ) (i : Fin n) (x : Total n R)
    (hx : x ∈ space (R := R) d L W k) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x ∈ space (R := R) d (L + d i) W (k + 1) := by
  have hle : space (R := R) d L W k ≤ (space (R := R) d (L + d i) W (k + 1)).comap
      ((KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)).restrictScalars R) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact wedge_generator d L W k i a
  exact hle hx

end LeanCanny.Algebra.KoszulWeighted
