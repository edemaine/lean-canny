/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulComplex
public import LeanCanny.Algebra.KoszulIdealAnnihilator
public import LeanCanny.Algebra.HomologySupport
public import LeanCanny.Algebra.ExtVanishing
public import LeanCanny.Algebra.FiniteComplexAcyclicity
public import LeanCanny.Algebra.ProjectiveDepth
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
/-! # Projective root exclusion implies positive Koszul exactness

For as many homogeneous inputs as variables, exclusion of nonzero common
roots provides enough depth to apply the bounded-complex acyclicity lemma.
The input ideal annihilates the finite positive homology, so Rees' theorem
gives the required Ext vanishing. This proves exactness in every positive
exterior degree, before restriction to a fixed polynomial weight.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped Classical
universe u
namespace LeanCanny.Algebra.KoszulExterior
variable {n : ℕ} {R : Type u} [CommRing R]
theorem exteriorPower_subsingleton_of_lt (k : ℕ) (hk : n < k) :
    Subsingleton (ExteriorAlgebra.exteriorPower R k (Fin n → R)) := by
  let b := (Pi.basisFun R (Fin n)).exteriorPower k
  have hempty : IsEmpty (Set.powersetCard (Fin n) k) := ⟨fun s => by
    have hle := Finset.card_le_univ s.val
    have he : s.val.card = k := s.property
    simp only [Fintype.card_fin] at hle
    omega⟩
  exact ⟨fun x y => b.repr.injective (by ext s; exact isEmptyElim s)⟩

theorem homology_finite [IsNoetherianRing R] (p : Fin n → R) (k : ℕ) :
    Module.Finite R ((complex p).homology k) := by
  have : IsNoetherian R ((complex p).sc k).X₂ := by
    change IsNoetherian R (ExteriorAlgebra.exteriorPower R k (Fin n → R))
    infer_instance
  exact HomologySupport.finite ((complex p).sc k)

theorem homology_support [IsNoetherianRing R] (p : Fin n → R) (k : ℕ) :
    Module.support R ((complex p).homology (k + 1)) ⊆ PrimeSpectrum.zeroLocus (Ideal.span (Set.range p)) := by
  have : IsNoetherian R ((complex p).sc (k + 1)).X₂ := by
    change IsNoetherian R (ExteriorAlgebra.exteriorPower R (k + 1) (Fin n → R))
    infer_instance
  apply HomologySupport.support
  change Ideal.span (Set.range p) • LinearMap.ker
    ((complex p).d (k + 1) ((ComplexShape.down ℕ).next (k + 1))).hom ≤
    LinearMap.range ((complex p).d ((ComplexShape.down ℕ).prev (k + 1)) (k + 1)).hom
  rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl),
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) from rfl),
    complex_d, complex_d]
  exact ideal_smul_ker_le_range p k

variable {K : Type u} [Field K] [IsAlgClosed K]
theorem complex_exactAt_of_no_nonzero_root_of_le
    (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : (complex p).ExactAt k := by
  apply FiniteComplexAcyclicity.exactAt_of_bounded_ext (complex p) n ?_ ?_ k hk hkn
  · apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (ExteriorAlgebra.exteriorPower (MvPolynomial (Fin n) K) (n + 1) (Fin n → MvPolynomial (Fin n) K))
    exact exteriorPower_subsingleton_of_lt (R := MvPolynomial (Fin n) K) (n + 1) (Nat.lt_succ_self n)
  · intro t ht _ l _ j hj
    let : Module.Finite (MvPolynomial (Fin n) K) ((complex p).homology t) := homology_finite p t
    have : Module.Finite (MvPolynomial (Fin n) K) ((complex p).X l) := by
      change Module.Finite (MvPolynomial (Fin n) K)
        (ExteriorAlgebra.exteriorPower (MvPolynomial (Fin n) K) l (Fin n → MvPolynomial (Fin n) K))
      infer_instance
    have : Module.Free (MvPolynomial (Fin n) K) ((complex p).X l) := by
      change Module.Free (MvPolynomial (Fin n) K)
        (ExteriorAlgebra.exteriorPower (MvPolynomial (Fin n) K) l (Fin n → MvPolynomial (Fin n) K))
      infer_instance
    apply ExtVanishing.finite_free
    apply ProjectiveDepth.subsingleton_ext_of_no_nonzero_root p d hp hd hroot _ _ j hj
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt ht)
    exact homology_support p s

theorem complex_exactAt_of_no_nonzero_root
    (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (k : ℕ) (hk : 0 < k) : (complex p).ExactAt k := by
  by_cases hkn : k ≤ n
  · exact complex_exactAt_of_no_nonzero_root_of_le p d hp hd hroot k hk hkn
  · apply HomologicalComplex.ExactAt.of_isZero
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact exteriorPower_subsingleton_of_lt k (by omega)

theorem graded_exact_of_no_nonzero_root
    (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (k : ℕ) :
    LinearMap.ker (gradedDifferential p k) = LinearMap.range (gradedDifferential p (k + 1)) := by
  have he := complex_exactAt_of_no_nonzero_root p d hp hd hroot (k + 1) (Nat.succ_pos k)
  have hs := ((complex p).exactAt_iff' (k + 2) (k + 1) k
    ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl)).mp he
  have hr := hs.moduleCat_range_eq_ker
  change LinearMap.range ((complex p).d (k + 2) (k + 1)).hom =
    LinearMap.ker ((complex p).d (k + 1) k).hom at hr
  rw [complex_d, complex_d] at hr
  exact hr.symm

end LeanCanny.Algebra.KoszulExterior
