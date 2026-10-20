/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCanonicalMatrix
public import LeanCanny.Algebra.MacaulayWeightedBridge

/-! # The Macaulay matrix in canonical Koszul coordinates

Singleton subsets index the degree-one terms and the empty subset indexes
degree zero. Under these index maps, the first canonical differential matrix
is the existing full rectangular Macaulay matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem exteriorBasis_empty : exteriorBasis (R := R) (∅ : Finset (Fin n)) = 1 := by
  rw [exteriorBasis_as_blade _ (Finset.card_empty), blade_zero]

theorem exteriorBasis_singleton (i : Fin n) :
    exteriorBasis (R := R) {i} = ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) := by
  rw [exteriorBasis_as_blade _ (Finset.card_singleton i)]
  have h : ({i} : Finset (Fin n)).orderEmbOfFin (Finset.card_singleton i) = (fun _ : Fin 1 => i) := by
    funext j
    exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem {i} (Finset.card_singleton i) j)
  rw [h, blade_one]

theorem exteriorBasis_repr_algebraMap (q : Poly n R) :
    (exteriorBasis (R := R)).repr (algebraMap (Poly n R) (Total n R) q) ∅ = q := by
  have h : algebraMap (Poly n R) (Total n R) q = q • exteriorBasis (R := R) ∅ := by
    rw [exteriorBasis_empty, Algebra.smul_def, mul_one]
  rw [h, map_smul, Module.Basis.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

noncomputable def macaulayCanonicalSource (d : Fin n → ℕ) (W : ℕ) (a : Macaulay.MultiplierIndex d W) :
    CanonicalIndex d (Macaulay.level d) W 1 := by
  refine ⟨{a.1}, a.2.val, ?_⟩
  rw [mem_canonicalIndices]
  refine ⟨Finset.card_singleton _, ?_⟩
  simpa only [subsetWeight, Finset.sum_singleton] using
    (Macaulay.mem_multiplierIndices d W a.1 a.2.val).mp a.2.property

noncomputable def macaulayCanonicalTarget (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) :
    CanonicalIndex d (Macaulay.level d) W 0 := by
  refine ⟨∅, r.val, ?_⟩
  rw [mem_canonicalIndices]
  refine ⟨Finset.card_empty, ?_⟩
  simpa only [subsetWeight, Finset.sum_empty, add_zero] using
    (Macaulay.mem_activeIndices d W r.val).mp r.property

theorem macaulayCanonicalSource_bijective (d : Fin n → ℕ) (W : ℕ) :
    Function.Bijective (macaulayCanonicalSource d W) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Finset.singleton_injective (congrArg Sigma.fst h)
    subst j
    apply congrArg (Sigma.mk i)
    apply Subtype.ext
    exact congrArg (fun x : CanonicalIndex d (Macaulay.level d) W 1 => x.2.val) h
  · rintro ⟨s, r, hr⟩
    have ha := (mem_canonicalIndices d (Macaulay.level d) W 1 s r).mp hr
    obtain ⟨i, hs⟩ := Finset.card_eq_one.mp ha.1
    subst s
    refine ⟨⟨i, r, ?_⟩, rfl⟩
    rw [Macaulay.mem_multiplierIndices]
    simpa only [subsetWeight, Finset.sum_singleton] using ha.2

theorem macaulayCanonicalTarget_bijective (d : Fin n → ℕ) (W : ℕ) :
    Function.Bijective (macaulayCanonicalTarget d W) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun x : CanonicalIndex d (Macaulay.level d) W 0 => x.2.val) h
  · rintro ⟨s, r, hr⟩
    have ha := (mem_canonicalIndices d (Macaulay.level d) W 0 s r).mp hr
    have hs : s = ∅ := Finset.card_eq_zero.mp ha.1
    subst s
    refine ⟨⟨r, ?_⟩, rfl⟩
    rw [Macaulay.mem_activeIndices]
    simpa only [subsetWeight, Finset.sum_empty, add_zero] using ha.2

noncomputable def macaulaySourceEquiv (d : Fin n → ℕ) (W : ℕ) :
    Macaulay.MultiplierIndex d W ≃ CanonicalIndex d (Macaulay.level d) W 1 :=
  Equiv.ofBijective (macaulayCanonicalSource d W) (macaulayCanonicalSource_bijective d W)

noncomputable def macaulayTargetEquiv (d : Fin n → ℕ) (W : ℕ) :
    Macaulay.activeIndices d W ≃ CanonicalIndex d (Macaulay.level d) W 0 :=
  Equiv.ofBijective (macaulayCanonicalTarget d W) (macaulayCanonicalTarget_bijective d W)

theorem canonicalGenerator_macaulaySource (d : Fin n → ℕ) (W : ℕ) (a : Macaulay.MultiplierIndex d W) :
    canonicalGenerator (R := R) d (Macaulay.level d) W 1 (macaulayCanonicalSource d W a) =
      generator (R := R) d (Macaulay.level d) W 1 (macaulaySourceIndex d W a) := by
  rw [canonicalGenerator_apply]
  change MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val) (1 : R) •
    exteriorBasis (R := R) {a.1} = monomialBlade (R := R) (fun _ : Fin 1 => a.1) _
  rw [exteriorBasis_singleton, monomialBlade, blade_one]
  rfl

theorem canonicalMatrix_macaulay_entry (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    canonicalMatrix p d (Macaulay.level d) W hp hW 0
      (macaulayCanonicalSource d W a) (macaulayCanonicalTarget d W r) = Macaulay.fullMatrix p d W a r := by
  rw [canonicalMatrix_apply, canonicalGenerator_macaulaySource, differential_macaulay_generator]
  change ((exteriorBasis (R := R)).repr
    (algebraMap (Poly n R) (Total n R) (Macaulay.sourceRow p d W a)) ∅).coeff _ = _
  rw [exteriorBasis_repr_algebraMap]
  rfl

theorem canonicalMatrix_macaulay (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (canonicalMatrix p d (Macaulay.level d) W hp hW 0).submatrix
      (macaulayCanonicalSource d W) (macaulayCanonicalTarget d W) = Macaulay.fullMatrix p d W := by
  ext a r
  exact canonicalMatrix_macaulay_entry p d W hp hW a r

end LeanCanny.Algebra.KoszulWeighted
