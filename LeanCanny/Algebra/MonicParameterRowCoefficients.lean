/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterRows
public import LeanCanny.Algebra.CoordinatePowerCoefficients

/-! # Exact coefficient queries for a monic scalar row

The new scalar exponent selects at most one lower coefficient. Independent
positive coordinate powers then reduce that coefficient to its original
exponent vector, without summing over the padded scalar degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterRows
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} [CommRing R]

noncomputable def appendExponent (e : ι →₀ ℕ) (k : ℕ) : (ι ⊕ Unit) →₀ ℕ :=
  e.mapDomain Sum.inl+Finsupp.single (Sum.inr ()) k

theorem appendExponent_old (e : ι →₀ ℕ) (k : ℕ) (j : ι) :
    appendExponent e k (Sum.inl j)=e j := by
  simp [appendExponent,Finsupp.mapDomain_apply_of_injective Sum.inl_injective]

theorem appendExponent_new (e : ι →₀ ℕ) (k : ℕ) :
    appendExponent e k (Sum.inr ())=k := by
  simp [appendExponent,Finsupp.mapDomain_of_notMem_range]

theorem appendExponent_eq (e f : ι →₀ ℕ) (k l : ℕ) :
    appendExponent e k=appendExponent f l ↔ e=f ∧ k=l := by
  constructor
  · intro H
    constructor
    · ext j
      simpa only [appendExponent_old] using congrArg (fun v => v (Sum.inl j)) H
    · simpa only [appendExponent_new] using congrArg (fun v => v (Sum.inr ())) H
  · rintro ⟨rfl,rfl⟩
    rfl

theorem coefficient_block (p : MvPolynomial ι R) (e : ι →₀ ℕ) (k l : ℕ) :
    (rename Sum.inl p*X (Sum.inr ())^k).coeff (appendExponent e l) =
      if k=l then p.coeff e else 0 := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,add_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq]
    split_ifs <;> simp
  | monomial f c =>
    rw [rename_monomial,X_pow_eq_monomial,monomial_mul_monomial,mul_one]
    change (monomial (appendExponent f k) c).coeff (appendExponent e l)=_
    simp only [coeff_monomial,appendExponent_eq]
    by_cases hk : k=l <;> by_cases he : f=e <;> simp [hk,he]


theorem coefficient_lower (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (w : ι → ℕ) (W : ℕ) (hW : 0<W) (e : ι →₀ ℕ) (k : ℕ) :
    (lower p N w W).coeff (appendExponent e (k*W)) =
      if k<N then (CoordinatePowerSubstitution.substitute w (coefficient p N k)).coeff e else 0 := by
  have HE (j : ℕ) : j*W=k*W ↔ j=k := by
    constructor
    · exact Nat.eq_of_mul_eq_mul_right hW
    · intro H
      rw [H]
  simp only [lower,coeff_sum,coefficient_block,HE,Finset.sum_ite_eq',Finset.mem_range]

theorem coefficient_row (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (w : ι → ℕ) (W : ℕ) (hW : 0<W) (e : ι →₀ ℕ) (k : ℕ) :
    (row p N w W).coeff (appendExponent e (k*W)) =
      (if k=N then (if e=0 then 1 else 0) else 0)+
      (if k<N then (CoordinatePowerSubstitution.substitute w (coefficient p N k)).coeff e else 0) := by
  have HE : N*W=k*W ↔ k=N := by
    constructor
    · intro H
      exact (Nat.eq_of_mul_eq_mul_right hW H).symm
    · intro H
      rw [H]
  have HX := coefficient_block (1 : MvPolynomial ι R) e (N*W) (k*W)
  simp only [map_one,one_mul,HE,coeff_one] at HX
  rw [row,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,HX,coefficient_lower p N w W hW]
  simp only [eq_comm]


theorem coefficient_monic_row (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (hp : p.Monic) (hd : p.natDegree=N)
    (w : ι → ℕ) (W : ℕ) (hW : 0<W) (e : ι →₀ ℕ) (k : ℕ) :
    (row p N w W).coeff (appendExponent e (k*W)) =
      (if k=N then (if e=0 then 1 else 0) else 0)+
      (if k<N then (CoordinatePowerSubstitution.substitute w (p.coeff k)).coeff e else 0) := by
  have HT : p.coeff N=1 := by
    calc
      p.coeff N=p.coeff p.natDegree := congrArg (fun k => p.coeff k) hd.symm
      _ = 1 := by rw [Polynomial.coeff_natDegree,hp.leadingCoeff]
  simpa only [coefficient,HT,one_pow,mul_one] using coefficient_row p N w W hW e k

theorem coefficient_off_power (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (w : ι → ℕ) (W : ℕ) (e : ι →₀ ℕ) (l : ℕ) (hl : ¬W∣l) :
    (row p N w W).coeff (appendExponent e l)=0 := by
  have HE (k : ℕ) : ¬k*W=l := by
    intro H
    apply hl
    exact H ▸ dvd_mul_left W k
  have HX := coefficient_block (1 : MvPolynomial ι R) e (N*W) l
  simp only [map_one,one_mul,ite_eq_right (HE N)] at HX
  simp only [row,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,HX,lower,coeff_sum,
    coefficient_block,ite_eq_right (HE _),Finset.sum_const_zero,add_zero]

variable [Fintype ι]

theorem coefficient_monic_row_powers (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (hp : p.Monic) (hd : p.natDegree=N)
    (w : ι → ℕ) (hw : ∀ i,0<w i) (W : ℕ) (hW : 0<W) (e : ι →₀ ℕ) (k : ℕ) (hk : k<N) :
    (row p N w W).coeff (appendExponent (CoordinatePowerSubstitution.exponent w e) (k*W)) =
      (p.coeff k).coeff e := by
  rw [coefficient_monic_row p N hp hd w W hW,ite_eq_right (by omega : k≠N),ite_eq_left hk,zero_add]
  exact CoordinatePowerSubstitution.coefficient_scaled w hw (p.coeff k) e

end LeanCanny.Algebra.MonicParameterRows
