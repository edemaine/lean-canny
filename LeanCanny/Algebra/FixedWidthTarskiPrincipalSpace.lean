/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateReader
public import LeanCanny.Algebra.BivariateTarskiSeedSpace
public import LeanCanny.Algebra.PolynomialPrincipalCoefficientSpace
/-! # Native selected-coefficient principal circuits over integer MV representatives

Kronecker substitution is applied to the coefficient ring only. The existing
streamed pseudo-reduction and principal determinant kernels then compute the
same ring element. A whole-output box permits exact coefficient decoding.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthTarskiPrincipalBits
open Polynomial PrincipalSubresultant LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial

structure Family where
  arity : List Bool→ℕ
  width : List Bool→ℕ
  head : (c : List Bool)→Polynomial (MvPolynomial (Fin (arity c)) ℤ)
  query : (c : List Bool)→Polynomial (MvPolynomial (Fin (arity c)) ℤ)
  degree : List Bool→ℕ
  bound : List Bool→ℕ
  seedDegree : List Bool→ℕ
  degree_pos : ∀ c,0<degree c
  degree_le : ∀ c,degree c≤bound c
  input_degree : ∀ c,(query c*(head c).derivative).natDegree≤bound c

noncomputable def encode (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c)) ℤ→+*ℤ[X] :=FixedWidthKronecker.encode (F.arity c) (F.width c)
noncomputable def head (F : Family) (c : List Bool) : (ℤ[X])[X] :=(F.head c).map (encode F c)
noncomputable def query (F : Family) (c : List Bool) : (ℤ[X])[X] :=(F.query c).map (encode F c)

noncomputable def seedFamily (F : Family) : BivariateTarskiSeedBits.Family where
  head:=head F
  query:=query F
  degree:=F.degree
  bound:=F.bound
  degree_pos:=F.degree_pos
  degree_le:=F.degree_le
  input_degree c:=by
    change ((F.query c).map (encode F c)*((F.head c).map (encode F c)).derivative).natDegree≤F.bound c
    rw [Polynomial.derivative_map,←Polynomial.map_mul]
    exact Polynomial.natDegree_map_le.trans (F.input_degree c)

structure Access (F : Family) where
  head : CertifiedPolynomial.BivariateReader (head F)
  query : CertifiedPolynomial.BivariateReader (query F)
  degree : BinaryFn F.degree
  bound : BinaryFn F.bound
  seedDegree : BinaryFn F.seedDegree

noncomputable def seedAccess {F : Family} (A : Access F) : BivariateTarskiSeedBits.Access (seedFamily F) where
  head:=A.head
  query:=A.query
  degree:=A.degree
  bound:=A.bound

noncomputable def principalFamily (F : Family) : PolynomialPrincipalCoefficientBits.Family where
  left:=head F
  right:=(seedFamily F).seed
  leftDegree:=F.degree
  rightDegree:=F.seedDegree

noncomputable def principalAccess {F : Family} (A : Access F) : PolynomialPrincipalCoefficientBits.Access (principalFamily F) where
  left:=A.head
  right:=BivariateTarskiSeedBits.reader (seedAccess A)
  leftDegree:=A.degree
  rightDegree:=A.seedDegree

noncomputable def polynomial (F : Family) (c : List Bool) (j : ℕ) : MvPolynomial (Fin (F.arity c)) ℤ :=
  signedPsc (F.head c) (PseudoRemainder.seed (F.head c) (F.query c) (F.degree c) (F.bound c))
    (F.degree c) (F.seedDegree c) j

theorem seed_encoded (F : Family) (c : List Bool) :
    (seedFamily F).seed c=(PseudoRemainder.seed (F.head c) (F.query c) (F.degree c) (F.bound c)).map (encode F c) :=
  PseudoRemainder.seed_map _ _ _ _ _

theorem polynomial_encoded (F : Family) (c : List Bool) (j : ℕ) :
    PolynomialPrincipalCoefficientBits.polynomial (principalFamily F) (pair c (BinaryNatCode.encode j))=
      encode F c (polynomial F c j) := by
  simp only [PolynomialPrincipalCoefficientBits.polynomial,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,principalFamily]
  rw [seed_encoded]
  exact signedPsc_map_map _ _ _ _ _ _

noncomputable def value {F : Family} (A : Access F) :=PolynomialPrincipalCoefficientBits.residueValue (principalAccess A)

theorem evaluator {F : Family} (A : Access F) : SpaceFunction (value A) :=
  PolynomialPrincipalCoefficientBits.evaluator (principalAccess A)

def packet (c : List Bool) (j r : ℕ) (modulus : List Bool) :=
  pair (pair (pair c (BinaryNatCode.encode j)) (BinaryNatCode.encode r)) modulus

theorem packet_encoded {F : Family} (A : Access F) (c : List Bool) (j r : ℕ) (modulus : List Bool) :
    value A (packet c j r modulus)=residueBits (((encode F c (polynomial F c j)).coeff r : ℤ) :
      ZMod (Nat.fromBitsLE modulus+1)) := by
  rw [value,PolynomialPrincipalCoefficientBits.residueValue_eq]
  apply congrArg₂ (fun (a : ℤ) (m : ℕ)=>residueBits (a : ZMod m))
  · simp only [packet,PolynomialPrincipalMinorBits.origin,PolynomialPrincipalCoefficientBits.parameter,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact congrArg (fun p : ℤ[X]=>p.coeff r) (polynomial_encoded F c j)
  · simp only [packet,PolynomialPrincipalMinorBits.modulus,pairSnd_pair]

theorem packet_coefficient {F : Family} (A : Access F) (c : List Bool) (j r D : ℕ) (modulus : List Bool)
    (hP : (polynomial F c j).totalDegree≤D) (hW : D<2^F.width c)
    (hr : r<count (F.arity c) (F.width c)) :
    value A (packet c j r modulus)=residueBits (((polynomial F c j).coeff
      (nativeExponent (Equiv.refl _) (F.width c) r) : ℤ) : ZMod (Nat.fromBitsLE modulus+1)) := by
  rw [packet_encoded]
  have HC:=FixedWidthKronecker.native_coefficient (Equiv.refl _) (F.width c) D (polynomial F c j) hP hW r hr
  have HE : (encode F c (polynomial F c j)).coeff r=(polynomial F c j).coeff
      (nativeExponent (Equiv.refl _) (F.width c) r) :=by
    simpa [encode,FixedWidthKronecker.native] using HC
  rw [HE]

/-- Specialization is a ring hom on actual representatives. No property of a
coefficient representative chooser is used. -/
theorem selected {R : Type*} [CommRing R] (F : Family) (c : List Bool) (j : ℕ)
    (φ : MvPolynomial (Fin (F.arity c)) ℤ→+*R) :
    φ (polynomial F c j)=signedPsc ((F.head c).map φ)
      (PseudoRemainder.seed ((F.head c).map φ) ((F.query c).map φ) (F.degree c) (F.bound c))
      (F.degree c) (F.seedDegree c) j := by
  rw [PseudoRemainder.seed_map,signedPsc_map_map]
  rfl

end LeanCanny.Algebra.FixedWidthTarskiPrincipalBits
