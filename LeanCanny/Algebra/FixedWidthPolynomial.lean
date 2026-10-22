/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Encoding.FixedWidthQuery
public import Mathlib.Algebra.BigOperators.Fin

/-! # Dense indexed polynomial sources from fixed-width exponent blocks

A binary rank lists one W-bit exponent per variable. The finite base-2^W
function equivalence proves uniqueness and coverage of all exponent vectors.
A polynomial whose support fits these blocks is exactly the indexed source of
its actual coefficients. This representation is mathematical; the exponentially
many coefficients are accessed by rank rather than stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthPolynomial
open LeanCanny.Encoding
open RationalSubstitution.Indexed
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

def count (A W : ℕ) : ℕ := (2 ^ W) ^ A

noncomputable def vector (A W : ℕ) (r : Fin (count A W)) : Fin A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (finFunctionFinEquiv.symm r i).val)

def index (A W : ℕ) (m : Fin A →₀ ℕ) (hm : ∀ i, m i < 2 ^ W) : Fin (count A W) :=
  finFunctionFinEquiv (fun i => ⟨m i, hm i⟩)

theorem vector_index (A W : ℕ) (m : Fin A →₀ ℕ) (hm : ∀ i, m i < 2 ^ W) : vector A W (index A W m hm) = m := by
  ext i
  change (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun i => ⟨m i, hm i⟩)) i).val = m i
  rw [Equiv.symm_apply_apply]

theorem vector_injective (A W : ℕ) : Function.Injective (vector A W) := by
  intro r s h
  apply finFunctionFinEquiv.symm.injective
  funext i
  apply Fin.ext
  exact congrArg (fun m : Fin A →₀ ℕ => m i) h

theorem vector_lt (A W : ℕ) (r : Fin (count A W)) (i : Fin A) : vector A W r i < 2 ^ W :=
  (finFunctionFinEquiv.symm r i).isLt

theorem vector_apply (A W : ℕ) (r : Fin (count A W)) (i : Fin A) :
    vector A W r i = r.val / 2 ^ (i.val * W) % 2 ^ W := by
  change r.val / (2 ^ W) ^ i.val % 2 ^ W = _
  rw [← pow_mul, Nat.mul_comm W i.val]

theorem drop_value (bits : List Bool) (k : ℕ) :
    Nat.fromBitsLE (bits.drop k) = Nat.fromBitsLE bits / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show bits.drop (k + 1) = (bits.drop k).drop 1 from List.drop_drop.symm,
      BinaryNat.drop_one_value, ih, Nat.div_div_eq_div_mul, pow_succ]

def entry (W r i : ℕ) : ℕ := Nat.fromBitsLE ((r.bits.drop (i * W)).take W)

theorem entry_eq_digit (W r i : ℕ) : entry W r i = r / 2 ^ (i * W) % 2 ^ W := by
  rw [entry, BinaryNat.value_take, drop_value, Nat.fromBitsLE_bits]

theorem entry_lt (W r i : ℕ) : entry W r i < 2 ^ W := by
  rw [entry_eq_digit]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem entry_vector (A W : ℕ) (r : Fin (count A W)) : exponentVector A (entry W r.val) = vector A W r := by
  ext i
  simp only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, entry_eq_digit, vector_apply]

theorem sum_monomials_eq (A W : ℕ) (p : MvPolynomial (Fin A) R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) :
    ∑ r : Fin (count A W), MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r)) = p := by
  classical
  have hsub : p.support ⊆ Finset.univ.image (vector A W) := by
    intro m hm
    exact Finset.mem_image.mpr ⟨index A W m (hp m hm), Finset.mem_univ _, vector_index A W m (hp m hm)⟩
  calc
    _ = ∑ m ∈ Finset.univ.image (vector A W), MvPolynomial.monomial m (p.coeff m) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => vector_injective A W h
    _ = ∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m) := by
      symm
      apply Finset.sum_subset hsub
      intro m _ hm
      simp only [MvPolynomial.notMem_support_iff.mp hm, map_zero]
    _ = p := p.as_sum.symm

theorem indexed_source_eq (A W : ℕ) (p : MvPolynomial (Fin A) R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) :
    source A (count A W) (fun r => p.coeff (exponentVector A (entry W r))) (entry W) = p := by
  rw [source, Finset.sum_range]
  calc
    _ = ∑ r : Fin (count A W), MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [entry_vector]
    _ = p := sum_monomials_eq A W p hp

end LeanCanny.Algebra.FixedWidthPolynomial
