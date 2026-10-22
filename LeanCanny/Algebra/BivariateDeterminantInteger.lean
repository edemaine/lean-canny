/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxSpace

/-! # Native integer bivariate determinant coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.BivariateDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

section Integer
variable (N : List Bool → ℕ) (modulus inner outer bound : List Bool → List Bool)
variable (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial (Polynomial ℤ)))

noncomputable def integerFamily (hN : ∀ c, 0 < N c)
    (hP : ∀ c i j k, ((P c i j).coeff k).natDegree ≤ Nat.fromBitsLE (bound c)) : Family where
  dimension := N
  dimension_pos := hN
  modulus c := Nat.fromBitsLE (modulus c) + 1
  modulus_ne_zero _ := by omega
  inner c := Nat.fromBitsLE (inner c)
  outer c := Nat.fromBitsLE (outer c)
  bound c := Nat.fromBitsLE (bound c)
  matrix c := (P c).map (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom _)))
  inner_bound c i j k := by
    simp only [Matrix.map_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (hP c i j k)

noncomputable def integerValue (c : List Bool) : List Bool :=
  residueBits (((((P c).det.coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

lemma integerFamily_value (hN : ∀ c, 0 < N c)
    (hP : ∀ c i j k, ((P c i j).coeff k).natDegree ≤ Nat.fromBitsLE (bound c)) :
    (integerFamily N modulus inner outer bound P hN hP).value = integerValue N modulus inner outer P := by
  funext c
  let phi := Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))))
  change residueBits (((((P c).map phi).det).coeff _).coeff _) = _
  have hd : phi ((P c).det) = ((P c).map phi).det := phi.map_det (P c)
  rw [← hd]
  simp only [phi, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

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
  let a : Access (integerFamily N modulus inner outer bound P hN hP) := {
    dimension := fun c => BinaryNatCode.encode (N c)
    modulus := fun c => BinaryNat.succ (modulus c)
    inner := BinaryNat.normalize ∘ inner
    outer := BinaryNat.normalize ∘ outer
    bound := BinaryNat.normalize ∘ bound
    coefficient := coefficient
    dimension_eq _ := rfl
    modulus_eq c := BinaryNat.succ_eq_bits _
    inner_eq c := BinaryNat.normalize_eq_bits _
    outer_eq c := BinaryNat.normalize_eq_bits _
    bound_eq c := BinaryNat.normalize_eq_bits _
    coefficient_eq c i j u v := by
      change Fin (N c) at i j
      simpa only [integerFamily, Matrix.map_apply, Polynomial.coe_mapRingHom,
        Polynomial.coeff_map, Int.coe_castRingHom] using hc c i j u v }
  have hmod : a.modulus ∈ FP := mem_FP_comp (f := modulus) (g := BinaryNat.succ) hm BinaryNat.succ_mem_FP
  have hbound : a.bound ∈ FP := mem_FP_comp (f := bound) (g := BinaryNat.normalize) hb BinaryNat.normalize_mem_FP
  have hinner : a.inner ∈ FP := mem_FP_comp (f := inner) (g := BinaryNat.normalize) hi BinaryNat.normalize_mem_FP
  have houter : a.outer ∈ FP := mem_FP_comp (f := outer) (g := BinaryNat.normalize) ho BinaryNat.normalize_mem_FP
  have ha := a.evaluator hn hmod hbound hinner houter E
  exact ha.congr (integerFamily_value N modulus inner outer bound P hN hP)

end Integer
end LeanCanny.Algebra.BivariateDeterminantBits
