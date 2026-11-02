/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthTarskiPrincipalSpace
public import Mathlib.Algebra.MvPolynomial.CommRing
/-! # Whole-output MV degree boxes for selected Tarski principal circuits

Bounds apply to actual integer representatives before selecting the old hom.
They retain outer degree parameters without assuming specialized degrees.
-/
@[expose] public section
namespace LeanCanny.Algebra.MultivariateTarskiDegreeBounds
open Polynomial PrincipalSubresultant
open scoped Classical BigOperators
variable {σ R : Type*} [CommRing R]

private theorem sum_degree {J : Type*} (s : Finset J) (f : J→MvPolynomial σ R) (D : ℕ)
    (hf : ∀ j∈s,(f j).totalDegree≤D) : (∑j∈s,f j).totalDegree≤D :=
  (MvPolynomial.totalDegree_finsetSum s f).trans (Finset.sup_le hf)

theorem mul_coefficient (p q : Polynomial (MvPolynomial σ R)) (P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) (i : ℕ) :
    ((p*q).coeff i).totalDegree≤P+Q := by
  rw [Polynomial.coeff_mul]
  exact sum_degree _ _ _ (fun j _=>(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp j.1) (hq j.2)))

theorem derivative_coefficient (p : Polynomial (MvPolynomial σ R)) (P : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (i : ℕ) : (p.derivative.coeff i).totalDegree≤P := by
  rw [Polynomial.coeff_derivative]
  have H : ((i: MvPolynomial σ R)+1)=MvPolynomial.C ((i:R)+1) :=by simp
  rw [H]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_C,Nat.add_zero] using hp (i+1))

theorem low_coefficient (p : Polynomial (MvPolynomial σ R)) (d P : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (i : ℕ) : ((PseudoRemainder.low d p).coeff i).totalDegree≤P := by
  rw [PseudoRemainder.low_coeff]
  split_ifs
  · exact hp i
  · simp

theorem high_coefficient (p : Polynomial (MvPolynomial σ R)) (d P : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (i : ℕ) : ((PseudoRemainder.high d p).coeff i).totalDegree≤P := by
  rw [PseudoRemainder.high_coeff]
  exact hp _

theorem step_coefficient (p q : Polynomial (MvPolynomial σ R)) (d P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) (i : ℕ) :
    ((PseudoRemainder.step p d q).coeff i).totalDegree≤P+Q := by
  rw [PseudoRemainder.step,Polynomial.coeff_sub,Polynomial.coeff_C_mul]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp d) (low_coefficient q d Q hq i))
  · exact mul_coefficient _ _ P Q (low_coefficient p d P hp) (high_coefficient q d Q hq) i

theorem iterate_coefficient (p q : Polynomial (MvPolynomial σ R)) (d k P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) :
    ∀ i,(((PseudoRemainder.step p d)^[k] q).coeff i).totalDegree≤k*P+Q := by
  induction k with
  | zero =>simpa using hq
  | succ k ih =>
    intro i
    rw [Function.iterate_succ_apply']
    have H:=step_coefficient p ((PseudoRemainder.step p d)^[k] q) d P (k*P+Q) hp ih i
    rw [Nat.succ_mul]
    omega

def seedDegreeBound (D P Q : ℕ) :=2*(D+1)*P+(Q+P)

theorem seed_coefficient (p q : Polynomial (MvPolynomial σ R)) (d D P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) (i : ℕ) :
    ((PseudoRemainder.seed p q d D).coeff i).totalDegree≤seedDegreeBound D P Q :=
  iterate_coefficient p (q*p.derivative) d (2*(D+1)) P (Q+P) hp
    (fun i=>mul_coefficient q p.derivative Q P hq (derivative_coefficient p P hp) i) i

theorem determinant {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial σ R)) (D : J→ℕ) (hM : ∀ i j,(M i j).totalDegree≤D j) :
    M.det.totalDegree≤∑j,D j := by
  rw [Matrix.det_apply]
  apply sum_degree
  intro e _
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    ((MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum (fun j _=>hM (e j) j)))

theorem minor (p q : Polynomial (MvPolynomial σ R)) (m n k j P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) :
    (Subresultant.minor p q m n k j).det.totalDegree≤(m-k)*Q+(n-k)*P := by
  have HM : ∀ i t : Fin ((m-k)+(n-k)),
      (Subresultant.minor p q m n k j i t).totalDegree≤t.addCases (fun _=>Q) (fun _=>P) := by
    intro i t
    induction t using Fin.addCases <;>
      simp only [Subresultant.minor,Matrix.of_apply,Fin.addCases_left,Fin.addCases_right,Subresultant.band]
    · split_ifs
      · exact hq _
      · simp
    · split_ifs
      · exact hp _
      · simp
  simpa only [Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,Fin.sum_const,smul_eq_mul]
    using determinant _ _ HM

theorem principal (p q : Polynomial (MvPolynomial σ R)) (m n j D : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤D) (hq : ∀ i,(q.coeff i).totalDegree≤D) :
    (signedPsc p q m n j).totalDegree≤(m+n+1)*D := by
  have HD : D≤(m+n+1)*D :=by nlinarith
  by_cases hj : j≤min m n
  · rw [signedPsc_of_le p q hj,psc_eq_minor]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have HS : ((-1 : MvPolynomial σ R)^(m-j).choose 2).totalDegree=0 :=by
      have HE : (-1 : MvPolynomial σ R)=MvPolynomial.C (-1 : R) :=by simp
      rw [HE,←map_pow,MvPolynomial.totalDegree_C]
    rw [HS,Nat.zero_add]
    exact (minor p q m n j j D D hp hq).trans (by nlinarith [Nat.sub_le m j,Nat.sub_le n j])
  · rw [signedPsc_of_lt p q (by omega)]
    split_ifs
    · exact (hp _).trans HD
    · exact (hq _).trans HD
    · simp

def principalDegreeBound (d s D P Q : ℕ) :=(d+s+1)*max P (seedDegreeBound D P Q)

theorem principal_seed (p q : Polynomial (MvPolynomial σ R)) (d s j D P Q : ℕ)
    (hp : ∀ i,(p.coeff i).totalDegree≤P) (hq : ∀ i,(q.coeff i).totalDegree≤Q) :
    (signedPsc p (PseudoRemainder.seed p q d D) d s j).totalDegree≤principalDegreeBound d s D P Q :=
  principal _ _ d s j _ (fun i=>(hp i).trans (le_max_left _ _))
    (fun i=>(seed_coefficient p q d D P Q hp hq i).trans (le_max_right _ _))

theorem seedDegreeBound_binary {D P Q : List Bool→ℕ} (hD : BinaryFn D) (hP : BinaryFn P) (hQ : BinaryFn Q) :
    BinaryFn (fun c=>seedDegreeBound (D c) (P c) (Q c)) :=
  (((BinaryFn.const 2).mul (hD.add (BinaryFn.const 1))).mul hP).add (hQ.add hP)

theorem principalDegreeBound_binary {d s D P Q : List Bool→ℕ}
    (hd : BinaryFn d) (hs : BinaryFn s) (hD : BinaryFn D) (hP : BinaryFn P) (hQ : BinaryFn Q) :
    BinaryFn (fun c=>principalDegreeBound (d c) (s c) (D c) (P c) (Q c)) := by
  have HB:=seedDegreeBound_binary hD hP hQ
  have HM : BinaryFn (fun c=>max (P c) (seedDegreeBound (D c) (P c) (Q c))) :=
    (BinaryFn.ite (hP.le HB) HB hP).of_eq (fun c=>(Nat.max_def : max _ _=if _ then _ else _).symm)
  exact ((hd.add hs).add (BinaryFn.const 1)).mul HM

theorem output_width_unary {d s D P Q : List Bool→ℕ}
    (hd : BinaryFn d) (hs : BinaryFn s) (hD : BinaryFn D) (hP : BinaryFn P) (hQ : BinaryFn Q) :
    UnaryFn (fun c=>(principalDegreeBound (d c) (s c) (D c) (P c) (Q c)).size) :=
  (UnaryFn.length (principalDegreeBound_binary hd hs hD hP hQ).bits_mem_FP).of_eq
    (fun _=>BinaryNatCode.length_encode _)

end LeanCanny.Algebra.MultivariateTarskiDegreeBounds
