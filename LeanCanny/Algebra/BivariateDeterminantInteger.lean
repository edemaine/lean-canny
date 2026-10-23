/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedMatrix

/-! # Native integer bivariate determinant coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.BivariateDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

section Integer
variable (N : List Bool → ℕ) (modulus inner outer bound : List Bool → List Bool)
variable (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial (Polynomial ℤ)))

noncomputable def integerValue (c : List Bool) : List Bool :=
  residueBits (((((P c).det.coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

/-- Native original entry residues suffice; the binary dimension writer may
represent an exponential number of rows. -/
theorem integerEvaluator (coefficient : List Bool → List Bool)
    (hN : ∀ c, 0 < N c)
    (hP : ∀ c i j k, ((P c i j).coeff k).natDegree ≤ Nat.fromBitsLE (bound c))
    (hc : ∀ c (i j : Fin (N c)) u v,
      coefficient (pair c (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
          residueBits (((((P c i j).coeff v).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (E : SpaceFunction coefficient) (hn : (fun c => BinaryNatCode.encode (N c)) ∈ FP)
    (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) (hb : bound ∈ FP) :
    SpaceFunction (integerValue N modulus inner outer P) := by
  let A : CertifiedMatrix.Bivariate modulus := {
    dimension := N
    dimension_pos := hN
    dimensionFP := BinaryFn.of_bits hn
    bound c := Nat.fromBitsLE (bound c)
    boundFP := BinaryFn.fromBits hb
    matrix := P
    inner_bound := hP
    coefficient := coefficient
    coefficient_eq := hc
    evaluator := E }
  exact A.determinantEvaluator inner outer hm hi ho

end Integer
end LeanCanny.Algebra.BivariateDeterminantBits
