/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationLowest
public import LeanCanny.ETR.TubeDeformationBudget
public import LeanCanny.Algebra.EffectiveInfinitesimalSign

/-! # An effective nonvanishing interval for the lowest tube coefficient

Every projection coefficient has a uniform perturbation degree and integer
coefficient budget. The resulting mass bound gives an FP binary dyadic exponent
below which the nonzero lowest deformation coefficient stays nonzero after
perturbation specialization. This controls nonvanishing only; the geometric
sampling and root-persistence requirements remain separate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

noncomputable def specializationMassCode (source read degree bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (budget source read degree bits c) (BinaryNatCode.encode ((radixCode source degree c).length)))

theorem specializationMassCode_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (hd : degree ∈ FP) (hb : bits ∈ FP) : specializationMassCode source read degree bits ∈ FP := by
  have hsize := bits_mem_FP (UnaryFn.length (radixCode_mem_FP hs hd))
  have h := mem_FP_comp (mem_FP_pair (budget_mem_FP hs hr hd hb) hsize) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := specializationMassCode source read degree bits) h (fun _ => by
    simp only [specializationMassCode, Function.comp_apply, BinaryNatCode.encode])

theorem specializationMassCode_value (source read degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (specializationMassCode source read degree bits c) =
      Nat.fromBitsLE (budget source read degree bits c) + (radix source degree c).size := by
  simp only [specializationMassCode, BinaryNat.add_pair, MacaulayBits.fromBits_encode, radixCode_code,
    BinaryNatCode.length_encode, Nat.fromBitsLE_bits]

noncomputable def specializationExponent (source read degree bits : List Bool → List Bool) : List Bool → List Bool :=
  BinaryNat.succ ∘ specializationMassCode source read degree bits

theorem specializationExponent_mem_FP {source read degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hr : read ∈ FP) (hd : degree ∈ FP) (hb : bits ∈ FP) : specializationExponent source read degree bits ∈ FP :=
  mem_FP_comp (specializationMassCode_mem_FP hs hr hd hb) BinaryNat.succ_mem_FP

theorem specializationExponent_value (source read degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (specializationExponent source read degree bits c) =
      Nat.fromBitsLE (specializationMassCode source read degree bits c) + 1 := by
  simp only [specializationExponent, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]

theorem lowestCoefficient_coefficient_bits (source active read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (j k : ℕ) : (((lowestCoefficient source active n d ell c).coeff j).coeff k).natAbs.size ≤
      Nat.fromBitsLE (budget source read B.degree B.bits c) := by
  have h := coefficient_bits source active read (fun _ => BinaryNatCode.encode k) (fun _ => BinaryNatCode.encode j)
    (fun _ => BinaryNatCode.encode (determinant source active n d ell c).natTrailingDegree) n d ell B hr c
  simpa only [coefficient, lowestCoefficient, Polynomial.trailingCoeff, MacaulayBits.fromBits_encode] using h

theorem lowestCoefficient_coefficient_mass (source active read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (j : ℕ) : coefficientMass ((lowestCoefficient source active n d ell c).coeff j) ≤
      2 ^ Nat.fromBitsLE (specializationMassCode source read B.degree B.bits c) := by
  rw [specializationMassCode_value]
  exact coefficientMass_le_pow_of_degree_coeff _ _ _ (lowestCoefficient_inner_degree source active n d ell B c j)
    (fun k => (Nat.size_le.mp (lowestCoefficient_coefficient_bits source active read n d ell B hr c j k)).le)

theorem projectionPolynomial_ne_zero_of_small (source active read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (a : ℝ) (ha : 0 < a)
    (hsmall : a ≤ InfinitesimalSign.dyadic (Nat.fromBitsLE (specializationExponent source read B.degree B.bits c))) :
    projectionPolynomial source active n d ell c a ≠ 0 := by
  let p := lowestCoefficient source active n d ell c
  let q := p.leadingCoeff
  have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (lowestCoefficient_ne_zero source active n d ell c)
  have hm := lowestCoefficient_coefficient_mass source active read n d ell B hr c p.natDegree
  have hs : Nat.fromBitsLE (specializationMassCode source read B.degree B.bits c) <
      Nat.fromBitsLE (specializationExponent source read B.degree B.bits c) := by
    rw [specializationExponent_value]
    omega
  have hsign := InfinitesimalSign.integer_sign_eval_le_dyadic q _ _ hm hs a ha hsmall
  intro hz
  have he := congrArg (fun f : Polynomial ℝ => f.coeff p.natDegree) hz
  change ((p.map (Polynomial.eval₂RingHom (Int.castRingHom ℝ) a)).coeff p.natDegree) = 0 at he
  rw [Polynomial.coeff_map, Polynomial.coeff_natDegree] at he
  have hqa : q.eval₂ (Int.castRingHom ℝ) a = 0 := he
  rw [hqa, sign_zero] at hsign
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq) (sign_eq_zero_iff.mp hsign.symm)

theorem projectionPolynomial_ne_zero_dyadic (source active read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) : projectionPolynomial source active n d ell c
      (InfinitesimalSign.dyadic (Nat.fromBitsLE (specializationExponent source read B.degree B.bits c))) ≠ 0 :=
  projectionPolynomial_ne_zero_of_small source active read n d ell B hr c _ (InfinitesimalSign.dyadic_pos _) le_rfl

theorem small_specialization_preserves_lowest (source active read : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (a : ℝ) (ha : 0 < a)
    (hsmall : a ≤ InfinitesimalSign.dyadic (Nat.fromBitsLE (specializationExponent source read B.degree B.bits c))) :
    let φ := Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom ℝ) a)
    ((determinant source active n d ell c).map φ).natTrailingDegree =
      (determinant source active n d ell c).natTrailingDegree ∧
    ((determinant source active n d ell c).map φ).trailingCoeff = projectionPolynomial source active n d ell c a :=
  DeformationLowestCoefficient.trailingCoeff_map_of_nonzero _ _
    (projectionPolynomial_ne_zero_of_small source active read n d ell B hr c a ha hsmall)

end LeanCanny.ETR.TubeDeformation
