/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCoordinateBasisMatrix
public import LeanCanny.Algebra.CharacteristicLowestBounds
public import LeanCanny.Algebra.CharacteristicPolynomialQuotient
public import LeanCanny.Algebra.RelativeMatrixDegree
public import LeanCanny.Algebra.IntegralParameterMatrixBounds
/-! # Parameter-mass bounds for actual padded scalar generator matrices

The estimates concern entire integer parameter polynomials before evaluation.
The new generator matrix is constructed from the old coefficient matrices.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParameterMatrixMassBounds
open Polynomial Matrix
open scoped Classical BigOperators
variable {ι :Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mul_mass (A B :Matrix ι ι ℤ[X]) (H G :ℕ)
    (hA :∀i j,coefficientMass (A i j)≤2^H) (hB :∀i j,coefficientMass (B i j)≤2^G) (i j :ι):
    coefficientMass ((A*B) i j)≤2^(H+G+(Fintype.card ι).size):=by
  rw [Matrix.mul_apply]
  calc
    _≤∑k:ι,coefficientMass (A i k*B k j):=coefficientMass_sum_le _ _
    _≤∑_k:ι,2^H*2^G:=Finset.sum_le_sum (fun k _=>
      (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul (hA i k) (hB k j)))
    _=Fintype.card ι*(2^H*2^G):=by simp
    _≤2^(Fintype.card ι).size*(2^H*2^G):=
      Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _=2^(H+G+(Fintype.card ι).size):=by rw [←pow_add,←pow_add];congr 1;omega

theorem pow_mass (A :Matrix ι ι ℤ[X]) (H :ℕ)
    (hA :∀i j,coefficientMass (A i j)≤2^H) (e :ℕ) (i j :ι):
    coefficientMass ((A^e) i j)≤2^(e*(H+(Fintype.card ι).size)):=by
  induction e generalizing i j with
  | zero=>
    simp only [pow_zero,Nat.zero_mul,Matrix.one_apply]
    split_ifs
    · change coefficientMass (Polynomial.C (1:ℤ))≤1
      rw [coefficientMass_C]
      norm_num
    · simp
  | succ e ih=>
    rw [pow_succ']
    have HM:=mul_mass A (A^e) H (e*(H+(Fintype.card ι).size)) hA (fun i j=>ih i j) i j
    convert HM using 1
    congr 1
    ring

theorem normalized_mass (A B :Matrix ι ι ℤ[X]) (H d k :ℕ) (hk :k<d)
    (hA :∀i j,coefficientMass (A i j)≤2^H) (hB :∀i j,coefficientMass (B i j)≤2^H) (i j :ι):
    coefficientMass ((A*B^(d-1-k)) i j)≤2^(d*(H+(Fintype.card ι).size)):=by
  have HM:=mul_mass A (B^(d-1-k)) H ((d-1-k)*(H+(Fintype.card ι).size)) hA
    (fun i j=>pow_mass B H hB _ i j) i j
  apply HM.trans
  apply Nat.pow_le_pow_right (by decide)
  calc
    _=(d-1-k+1)*(H+(Fintype.card ι).size):=by ring
    _≤d*(H+(Fintype.card ι).size):=Nat.mul_le_mul_right _ (by omega)

private theorem neg_one_pow_mass (n :ℕ) (q :ℤ[X]):
    coefficientMass (((-1:ℤ[X])^n)*q)=coefficientMass q:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [pow_succ',mul_assoc,neg_one_mul,coefficientMass_neg]
    exact ih

def characteristicBudget (n H :ℕ):=n.size*n+n*(H+1)

theorem characteristicBudget_binary {n H :List Bool→ℕ} (hn :BinaryFn n) (hH :BinaryFn H):
    BinaryFn (fun q=>characteristicBudget (n q) (H q)):=
  (hn.size.mul hn).add (hn.mul (hH.add (BinaryFn.const 1)))

def stepBudget (N m H :ℕ):=N*(H+(N^m).size)

theorem stepBudget_binary {N m H :List Bool→ℕ}
    (hN :BinaryFn N) (hm :UnaryFn m) (hH :BinaryFn H):
    BinaryFn (fun q=>stepBudget (N q) (m q) (H q)):=
  hN.mul (hH.add (hN.powUnary hm).size)

theorem charpoly_coefficient_mass (A :Matrix ι ι ℤ[X]) (H :ℕ)
    (hA :∀i j,coefficientMass (A i j)≤2^H) (k :ℕ):
    coefficientMass (A.charpoly.coeff k)≤2^characteristicBudget (Fintype.card ι) H:=by
  have HM:=CharacteristicLowestBounds.coefficient_mass_le A (2^H) hA k
  rw [AffineCharacteristic.subtractive_det_eq_sign_mul_charpoly,coeff_C_mul,neg_one_pow_mass] at HM
  have HF :(Fintype.card ι).factorial≤2^((Fintype.card ι).size*Fintype.card ι):=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (pow_mul _ _ _).symm)
  have HE :2^H+1≤2^(H+1):=by
    rw [pow_succ]
    have HP:=Nat.one_le_two_pow (n:=H)
    omega
  calc
    _≤(Fintype.card ι).factorial*(2^H+1)^Fintype.card ι:=HM
    _≤2^((Fintype.card ι).size*Fintype.card ι)*(2^(H+1))^Fintype.card ι:=
      Nat.mul_le_mul HF (Nat.pow_le_pow_left HE _)
    _=2^characteristicBudget (Fintype.card ι) H:=by
      rw [←pow_mul,←pow_add]
      congr 1
      unfold characteristicBudget
      ring

theorem padded_root_mass {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d H :ℕ)
    (hp :∀k r s,coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff k) r s)≤2^H)
    (e f :Fin (m+1)→Fin N):
    coefficientMass (Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _) e f)≤
      2^(N*(H+(Fintype.card (Fin m→Fin N)).size)):=by
  obtain ⟨⟨r,i⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective e
  obtain ⟨⟨s,j⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective f
  rw [CoefficientCoordinateBasis.padded_root_matrix]
  split_ifs with hcol hrow heq hallowed
  · change coefficientMass (Polynomial.C (1:ℤ))≤_
    rw [coefficientMass_C]
    simpa only [Int.natAbs_one] using
      (show (1:ℕ)≤2^(N*(H+(Fintype.card (Fin m→Fin N)).size)) from Nat.one_le_two_pow)
  · simp
  · simp
  · rw [coefficientMass_neg]
    have HK :i.val-(N-d)<d:=by have :=i.isLt;omega
    exact (normalized_mass _ _ H d _ HK (hp _) (hp _) r s).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hallowed.1))
  · simp

theorem normalized_degree (A B :Matrix ι ι ℤ[X]) (E d k :ℕ) (hk :k<d)
    (hA :RelativeMatrixDegree.Bound A E) (hB :RelativeMatrixDegree.Bound B E) (i j :ι):
    ((A*B^(d-1-k)) i j).natDegree≤d*E:=by
  have HM:=RelativeMatrixDegree.mul hA (RelativeMatrixDegree.pow hB (d-1-k)) i j
  apply HM.trans
  calc
    E+(d-1-k)*E=(d-1-k+1)*E:=by ring
    _≤d*E:=Nat.mul_le_mul_right E (by omega)

theorem padded_root_degree {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d E :ℕ)
    (hp :∀k,RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b.basis (p.coeff k)) E)
    (e f :Fin (m+1)→Fin N):
    (Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _) e f).natDegree≤N*E:=by
  obtain ⟨⟨r,i⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective e
  obtain ⟨⟨s,j⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective f
  rw [CoefficientCoordinateBasis.padded_root_matrix]
  split_ifs with hcol hrow heq hallowed
  · simp
  · simp
  · simp
  · rw [Polynomial.natDegree_neg]
    have HK :i.val-(N-d)<d:=by have :=i.isLt;omega
    exact (normalized_degree _ _ E d _ HK (hp _) (hp _) r s).trans
      (Nat.mul_le_mul_right E hallowed.1)
  · simp

theorem padded_of_mass {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d H :ℕ) (a :A)
    (hA :∀r s,coefficientMass (Algebra.leftMulMatrix b.basis a r s)≤2^H)
    (e f :Fin (m+1)→Fin N):
    coefficientMass (Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.of _ a) e f)≤2^H:=by
  obtain ⟨⟨r,i⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective e
  obtain ⟨⟨s,j⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective f
  change coefficientMass (Algebra.leftMulMatrix (b.step _ _ _).basis (AdjoinRoot.of _ a) _ _)≤_
  rw [CoefficientCoordinateBasis.step_of_matrix]
  split_ifs
  · exact hA r s
  · simp

theorem padded_of_degree {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d E :ℕ) (a :A)
    (hA :RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b.basis a) E)
    (e f :Fin (m+1)→Fin N):
    (Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.of _ a) e f).natDegree≤E:=by
  obtain ⟨⟨r,i⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective e
  obtain ⟨⟨s,j⟩,rfl⟩:=(CoefficientCoordinateBasis.indexEquiv m N).surjective f
  change (Algebra.leftMulMatrix (b.step _ _ _).basis (AdjoinRoot.of _ a) _ _).natDegree≤_
  rw [CoefficientCoordinateBasis.step_of_matrix]
  split_ifs
  · exact hA r s
  · simp

theorem padded_root_charpoly_mass {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d H :ℕ)
    (hp :∀k r s,coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff k) r s)≤2^H) (k :ℕ):
    coefficientMass ((Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _)).charpoly.coeff k)≤
      2^characteristicBudget (N^(m+1)) (stepBudget N m H):=by
  have HM:=charpoly_coefficient_mass (Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _))
    (N*(H+(Fintype.card (Fin m→Fin N)).size)) (padded_root_mass b p d H hp) k
  simpa only [Fintype.card_fun,Fintype.card_fin,stepBudget] using HM

theorem padded_root_charpoly_degree {A :Type*} [CommRing A] [Nontrivial A] [Algebra ℤ[X] A] {m N :ℕ}
    (b :CoefficientCoordinateBasis ℤ[X] A m N) (p :A[X]) (d E :ℕ)
    (hp :∀k,RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b.basis (p.coeff k)) E) (k :ℕ):
    ((Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _)).charpoly.coeff k).natDegree≤
      N^(m+1)*(N*E):=by
  have HD:=RelativeMatrixDegree.charpoly_coefficient (padded_root_degree b p d E hp) k
  simpa only [Fintype.card_fun,Fintype.card_fin] using HD

end LeanCanny.Algebra.ParameterMatrixMassBounds
