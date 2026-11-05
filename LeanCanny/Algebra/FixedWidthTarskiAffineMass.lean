/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthTarskiMass
/-! # Direct principal mass and affine input-height budgets

Support-box injectivity bounds the whole MV mass by the encoded mass, without
charging the box cardinality. The width used in this proof does not alter the
installed principal polynomial or its native metadata.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthTarskiMass
open Polynomial LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open scoped Classical BigOperators

private theorem partial_coeff_sum_le (p : ℤ[X]) (N : ℕ) :
    (∑ r : Fin N, (p.coeff r.val).natAbs) ≤ coefficientMass p := by
  let M := max N (p.natDegree + 1)
  have HM : p.natDegree < M := by dsimp [M]; omega
  have HE : coefficientMass p = ∑ i ∈ Finset.range M, (p.coeff i).natAbs :=
    p.sum_over_range' (fun _ => rfl) M HM
  rw [Fin.sum_univ_eq_sum_range (fun i => (p.coeff i).natAbs) N, HE]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_left _ _))

theorem mass_le_encoded_exact (A W : ℕ) (p : MvPolynomial (Fin A) ℤ)
    (hp : ∀ e ∈ p.support, ∀ i, e i < 2^W) :
    MvMass.mass p ≤ coefficientMass (FixedWidthKronecker.encode A W p) := by
  calc
    _ = MvMass.mass (∑ r : Fin (count A W), MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r))) :=
      congrArg MvMass.mass (sum_monomials_eq A W p hp).symm
    _ ≤ ∑ r : Fin (count A W), MvMass.mass (MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r))) :=
      MvMass.sum_le _ _
    _ = ∑ r : Fin (count A W), ((FixedWidthKronecker.encode A W p).coeff r.val).natAbs := by
      apply Finset.sum_congr rfl
      intro r _
      rw [MvMass.monomial, FixedWidthKronecker.coefficient A W p hp r]
    _ ≤ _ := partial_coeff_sum_le _ _

theorem principal_mass_direct (F : FixedWidthTarskiPrincipalBits.Family) (c : List Bool)
    (j dp dq bp bq : ℕ) (hp : (F.head c).natDegree ≤ dp) (hq : (F.query c).natDegree ≤ dq)
    (hP : ∀ i, MvMass.mass ((F.head c).coeff i) ≤ 2^bp)
    (hQ : ∀ i, MvMass.mass ((F.query c).coeff i) ≤ 2^bq) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial F c j) ≤
      2^principalMass (F.degree c) (F.seedDegree c) (F.bound c) dp dq bp bq := by
  let p := FixedWidthTarskiPrincipalBits.polynomial F c j
  let W := p.totalDegree.size
  let enc : MvPolynomial (Fin (F.arity c)) ℤ →+* ℤ[X] := FixedWidthKronecker.encode (F.arity c) W
  have HE : enc p = PrincipalSubresultant.signedPsc ((F.head c).map enc)
      (PseudoRemainder.seed ((F.head c).map enc) ((F.query c).map enc) (F.degree c) (F.bound c))
      (F.degree c) (F.seedDegree c) j := by
    rw [show p = FixedWidthTarskiPrincipalBits.polynomial F c j from rfl,
      FixedWidthTarskiPrincipalBits.polynomial, ← PrincipalSubresultant.signedPsc_map_map,
      ← PseudoRemainder.seed_map]
  apply (mass_le_encoded_exact (F.arity c) W p ?_).trans
  · rw [show FixedWidthKronecker.encode (F.arity c) W p = enc p from rfl, HE]
    apply encoded_principal_mass _ _ _ _ _ _ dp dq bp bq
    · exact Polynomial.natDegree_map_le.trans hp
    · exact Polynomial.natDegree_map_le.trans hq
    · intro i
      rw [Polynomial.coeff_map]
      exact (encode_mass_le _ _ _).trans (hP i)
    · intro i
      rw [Polynomial.coeff_map]
      exact (encode_mass_le _ _ _).trans (hQ i)
  · intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      (Nat.lt_size_self _)

def seedSlope (D Kp Kq : ℕ) := (2*(D+1)+1)*Kp+Kq
def principalSlope (d s D Kp Kq : ℕ) := (d+s+1)*(Kp+seedSlope D Kp Kq)
def principalOffset (d s D dp dq Hp Hq : ℕ) :=
  (d+s).size*(d+s)+(d+s+1)*(headMass dp Hp+seedMass D dp dq Hp Hq)

theorem seedMass_affine (D dp dq Kp Kq Hp Hq r : ℕ) :
    seedMass D dp dq (Kp*r+Hp) (Kq*r+Hq) = seedSlope D Kp Kq*r+seedMass D dp dq Hp Hq := by
  unfold seedMass headMass PseudoRemainder.fixedSeedMassBound seedSlope
  ring

theorem principalMass_affine (d s D dp dq Kp Kq Hp Hq r : ℕ) :
    principalMass d s D dp dq (Kp*r+Hp) (Kq*r+Hq) ≤
      principalSlope d s D Kp Kq*r+principalOffset d s D dp dq Hp Hq := by
  have HH : headMass dp (Kp*r+Hp) = Kp*r+headMass dp Hp := by unfold headMass; omega
  have HM : max (headMass dp (Kp*r+Hp)) (seedMass D dp dq (Kp*r+Hp) (Kq*r+Hq)) ≤
      (Kp+seedSlope D Kp Kq)*r+(headMass dp Hp+seedMass D dp dq Hp Hq) := by
    rw [HH, seedMass_affine]
    apply max_le
    · nlinarith
    · nlinarith
  have HB := Nat.mul_le_mul_left (d+s+1) HM
  unfold principalMass PrincipalSubresultant.parameterMassBound principalSlope principalOffset
  nlinarith only [HB]

theorem seedSlope_binary {D Kp Kq : List Bool → ℕ} (hD : BinaryFn D) (hKp : BinaryFn Kp) (hKq : BinaryFn Kq) :
    BinaryFn (fun c => seedSlope (D c) (Kp c) (Kq c)) :=
  (((((BinaryFn.const 2).mul (hD.add (BinaryFn.const 1))).add (BinaryFn.const 1)).mul hKp).add hKq)

theorem principalSlope_binary {d s D Kp Kq : List Bool → ℕ}
    (hd : BinaryFn d) (hs : BinaryFn s) (hD : BinaryFn D) (hKp : BinaryFn Kp) (hKq : BinaryFn Kq) :
    BinaryFn (fun c => principalSlope (d c) (s c) (D c) (Kp c) (Kq c)) :=
  ((hd.add hs).add (BinaryFn.const 1)).mul (hKp.add (seedSlope_binary hD hKp hKq))

theorem principalOffset_binary {d s D dp dq Hp Hq : List Bool → ℕ}
    (hd : BinaryFn d) (hs : BinaryFn s) (hD : BinaryFn D) (hdp : BinaryFn dp) (hdq : BinaryFn dq)
    (hHp : BinaryFn Hp) (hHq : BinaryFn Hq) :
    BinaryFn (fun c => principalOffset (d c) (s c) (D c) (dp c) (dq c) (Hp c) (Hq c)) := by
  have HR := hd.add hs
  exact (HR.size.mul HR).add ((HR.add (BinaryFn.const 1)).mul
    ((headMass_binary hdp hHp).add (seedMass_binary hD hdp hdq hHp hHq)))

end LeanCanny.Algebra.FixedWidthTarskiMass
