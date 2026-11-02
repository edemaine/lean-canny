/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Indexed denominator clearing in a joint multivariate polynomial ring

The same indexed original terms as the native univariate substitution engine
form a polynomial on the complete joint variable tuple. Kronecker encoding
commutes with this construction, and even denominator powers preserve signs.
-/
@[expose] public section
namespace LeanCanny.Algebra.MvIndexedRationalClearing
open LeanCanny.Encoding
open scoped Classical BigOperators
variable {σ : Type*}

noncomputable def cleared (A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ r ∈ Finset.range M, MvPolynomial.C (a r)*∏ i ∈ Finset.range A,n i^e r i*d i^(W-e r i)

theorem encode (B V A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial (Fin B) ℤ) :
    FixedWidthKronecker.encode B V (cleared A M W a e n d)=
      RationalSubstitution.Indexed.cleared A M W a e
        (fun i => FixedWidthKronecker.encode B V (n i)) (fun i => FixedWidthKronecker.encode B V (d i)) := by
  have HC (z : ℤ) : FixedWidthKronecker.encode B V (MvPolynomial.C z)=Polynomial.C z := by
    simp only [FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C]
  simp only [cleared,RationalSubstitution.Indexed.cleared,map_sum,map_mul,map_prod,map_pow,HC]

theorem totalDegree (A M W E : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ ℤ)
    (he : ∀ r,r<M → ∀ i,i<A → e r i≤W)
    (hn : ∀ i,i<A → (n i).totalDegree≤E) (hd : ∀ i,i<A → (d i).totalDegree≤E) :
    (cleared A M W a e n d).totalDegree≤A*W*E := by
  unfold cleared
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,Nat.zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range A,W*E := by
      apply Finset.sum_le_sum
      intro i hi
      have HE := he r (Finset.mem_range.mp hr) i (Finset.mem_range.mp hi)
      calc
        _ ≤ (n i^e r i).totalDegree+(d i^(W-e r i)).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ e r i*(n i).totalDegree+(W-e r i)*(d i).totalDegree :=
          Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) (MvPolynomial.totalDegree_pow _ _)
        _ ≤ e r i*E+(W-e r i)*E := Nat.add_le_add
          (Nat.mul_le_mul_left _ (hn i (Finset.mem_range.mp hi)))
          (Nat.mul_le_mul_left _ (hd i (Finset.mem_range.mp hi)))
        _ = W*E := by rw [← Nat.add_mul,Nat.add_sub_of_le HE]
    _ = A*W*E := by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_assoc]

theorem mass (A M W s b : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ ℤ)
    (he : ∀ r,r<M → ∀ i,i<A → e r i≤W) (ha : ∀ r,r<M → (a r).natAbs≤2^s)
    (hn : ∀ i,i<A → MvMass.mass (n i)≤2^b) (hd : ∀ i,i<A → MvMass.mass (d i)≤2^b) :
    MvMass.mass (cleared A M W a e n d)≤2^(M.size+s+A*W*b) := by
  have HF (r i : ℕ) (hr : r<M) (hi : i<A) : MvMass.mass (n i^e r i*d i^(W-e r i))≤2^(W*b) := by
    calc
      _ ≤ MvMass.mass (n i^e r i)*MvMass.mass (d i^(W-e r i)) := MvMass.mul_le _ _
      _ ≤ MvMass.mass (n i)^e r i*MvMass.mass (d i)^(W-e r i) := Nat.mul_le_mul (MvMass.pow_le _ _) (MvMass.pow_le _ _)
      _ ≤ (2^b)^e r i*(2^b)^(W-e r i) := Nat.mul_le_mul (Nat.pow_le_pow_left (hn i hi) _) (Nat.pow_le_pow_left (hd i hi) _)
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le (he r hr i hi),← pow_mul,Nat.mul_comm]
  have HP (r : ℕ) (hr : r<M) : MvMass.mass (∏ i ∈ Finset.range A,n i^e r i*d i^(W-e r i))≤2^(A*W*b) := by
    calc
      _ ≤ ∏ i ∈ Finset.range A,MvMass.mass (n i^e r i*d i^(W-e r i)) := MvMass.prod_le _ _
      _ ≤ ∏ _i ∈ Finset.range A,2^(W*b) := Finset.prod_le_prod (fun i hi => HF r i hr (Finset.mem_range.mp hi))
      _ = _ := by simp only [Finset.prod_const,Finset.card_range,← pow_mul]; congr 1; ring
  have HT (r : ℕ) (hr : r<M) :
      MvMass.mass (MvPolynomial.C (a r)*∏ i ∈ Finset.range A,n i^e r i*d i^(W-e r i))≤2^(s+A*W*b) := by
    apply (MvMass.mul_le _ _).trans
    rw [MvMass.C,pow_add]
    exact Nat.mul_le_mul (ha r hr) (HP r hr)
  calc
    _ ≤ ∑ r ∈ Finset.range M,MvMass.mass (MvPolynomial.C (a r)*∏ i ∈ Finset.range A,n i^e r i*d i^(W-e r i)) := MvMass.sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range M,2^(s+A*W*b) := Finset.sum_le_sum (fun r hr => HT r (Finset.mem_range.mp hr))
    _ = M*2^(s+A*W*b) := by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    _ ≤ 2^M.size*2^(s+A*W*b) := Nat.mul_le_mul_right _ (Nat.lt_size_self M).le
    _ = _ := by rw [← pow_add,Nat.add_assoc]

theorem eval (A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ ℤ) (z : σ → ℝ)
    (he : ∀ r,r<M → ∀ i,i<A → e r i≤W)
    (hd : ∀ i,i<A → (d i).eval₂ (Int.castRingHom ℝ) z≠0) :
    (cleared A M W a e n d).eval₂ (Int.castRingHom ℝ) z=
      (∏ i ∈ Finset.range A,(d i).eval₂ (Int.castRingHom ℝ) z^W)*
      (RationalSubstitution.Indexed.source A M a e).eval₂ (Int.castRingHom ℝ)
        (fun i => (n i.val).eval₂ (Int.castRingHom ℝ) z/(d i.val).eval₂ (Int.castRingHom ℝ) z) := by
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z
  have HC (v : ℤ) : ψ (MvPolynomial.C v)=(Int.castRingHom ℝ) v := MvPolynomial.eval₂_C _ _ _
  change ψ (cleared A M W a e n d)=(∏ i ∈ Finset.range A,ψ (d i)^W)*
    (RationalSubstitution.Indexed.source A M a e).eval₂ (Int.castRingHom ℝ) (fun i => ψ (n i.val)/ψ (d i.val))
  simp only [cleared,map_sum,map_mul,map_prod,map_pow,HC]
  rw [RationalSubstitution.Indexed.eval₂_source (Int.castRingHom ℝ) A M a e (fun i => ψ (n i)/ψ (d i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = (Int.castRingHom ℝ) (a r)*∏ i ∈ Finset.range A,ψ (d i)^W*(ψ (n i)/ψ (d i))^e r i := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (RationalSubstitution.scale_div_pow _ _ _ _ (he r (Finset.mem_range.mp hr) i (Finset.mem_range.mp hi)) (hd i (Finset.mem_range.mp hi))).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem sign (A M D : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ ℤ) (z : σ → ℝ)
    (he : ∀ r,r<M → ∀ i,i<A → e r i≤2*D)
    (hd : ∀ i,i<A → (d i).eval₂ (Int.castRingHom ℝ) z≠0) :
    SignType.sign ((cleared A M (2*D) a e n d).eval₂ (Int.castRingHom ℝ) z)=
      SignType.sign ((RationalSubstitution.Indexed.source A M a e).eval₂ (Int.castRingHom ℝ)
        (fun i => (n i.val).eval₂ (Int.castRingHom ℝ) z/(d i.val).eval₂ (Int.castRingHom ℝ) z)) := by
  have HP : 0<∏ i ∈ Finset.range A,(d i).eval₂ (Int.castRingHom ℝ) z^(2*D) := by
    apply Finset.prod_pos
    intro i hi
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (hd i (Finset.mem_range.mp hi))) _
  rw [eval A M (2*D) a e n d z he hd,sign_mul,sign_pos HP,one_mul]

end LeanCanny.Algebra.MvIndexedRationalClearing
