/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicPolynomialSpecialization
public import LeanCanny.Algebra.DyadicSpecializationSpace

/-! # Uniform coefficient access after specializing a polynomial parameter

Outer coefficients are polynomials in beta. Each is passed to the space-bounded
dyadic numerator evaluator with the same exponent and clearing degree.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicPolynomialBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation

structure Family where
  polynomial : List Bool → (ℤ[X])[X]
  degree : List Bool → List Bool
  parameterDegree : List Bool → List Bool
  exponent : List Bool → List Bool
  mass : List Bool → List Bool
  polynomial_degree : ∀ c, (polynomial c).natDegree ≤ Nat.fromBitsLE (degree c)
  coefficient_degree : ∀ c i, ((polynomial c).coeff i).natDegree ≤ Nat.fromBitsLE (parameterDegree c)
  coefficient_mass : ∀ c i, coefficientMass ((polynomial c).coeff i) ≤ 2 ^ Nat.fromBitsLE (mass c)

structure ControlsPolyTime (F : Family) : Prop where
  degree : F.degree ∈ FP
  parameterDegree : F.parameterDegree ∈ FP
  exponent : F.exponent ∈ FP
  mass : F.mass ∈ FP

noncomputable def Family.specialized (F : Family) (c : List Bool) : ℤ[X] :=
  DyadicPolynomial.specialize (F.polynomial c) (Nat.fromBitsLE (F.parameterDegree c)) (Nat.fromBitsLE (F.exponent c))

noncomputable def scalarFamily (F : Family) : DyadicBits.Family where
  polynomial r := (F.polynomial (pairFst r)).coeff (Nat.fromBitsLE (pairSnd r))
  degree := F.parameterDegree ∘ pairFst
  exponent := F.exponent ∘ pairFst
  mass := F.mass ∘ pairFst
  polynomial_degree r := F.coefficient_degree (pairFst r) _
  polynomial_mass r := F.coefficient_mass (pairFst r) _

theorem scalar_controls (F : Family) (hF : ControlsPolyTime F) : DyadicBits.ControlsPolyTime (scalarFamily F) := by
  have hd := mem_FP_comp pairFst_mem_FP hF.parameterDegree
  have hs := mem_FP_comp pairFst_mem_FP hF.exponent
  have hm := mem_FP_comp pairFst_mem_FP hF.mass
  exact ⟨hd, hs, hm⟩

structure Access (F : Family) where
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c i j m, 0 < m → coefficient
    (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode (m - 1))) =
      DyadicBits.integerResidue (((F.polynomial c).coeff i).coeff j) m

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst p)))
    (pair (BinaryNat.normalize (pairSnd (pairFst (pairFst p)))) (pairSnd (pairFst p)))) (pairSnd p)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hi := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have hj := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair hc (mem_FP_pair hi hj)) pairSnd_mem_FP
  refine mem_FP_of_eq (g := sourceQuery) h ?_
  intro p
  simp only [sourceQuery, Function.comp_apply]

def scalarAccess {F : Family} (a : Access F) : DyadicBits.Access (scalarFamily F) where
  coefficient := a.coefficient ∘ sourceQuery
  coefficient_eq := by
    intro r j m hm
    simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    simpa only [scalarFamily, BinaryNatCode.encode] using a.coefficient_eq (pairFst r) (Nat.fromBitsLE (pairSnd r)) j m hm

noncomputable def Family.residue (F : Family) (q : List Bool) : List Bool :=
  DyadicBits.integerResidue ((F.specialized (pairFst (pairFst q))).coeff (Nat.fromBitsLE (pairSnd (pairFst q))))
    (DyadicBits.mValue q)

theorem residueEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) : SpaceFunction F.residue := by
  let E := DyadicBits.residueEvaluator (scalarAccess a) (scalar_controls F hF)
    (P.precompose sourceQuery sourceQuery_mem_FP)
  refine E.congr (funext fun q => ?_)
  simp only [Family.residue, Family.specialized, DyadicPolynomial.coeff_specialize, DyadicBits.Family.residue,
    DyadicBits.Family.value, scalarFamily, Function.comp_apply]

theorem residue_packet (F : Family) (c : List Bool) (i m : ℕ) (hm : 0 < m) :
    F.residue (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1))) =
      DyadicBits.integerResidue ((F.specialized c).coeff i) m := by
  simp only [Family.residue, DyadicBits.mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)]

def massCode (F : Family) (c : List Bool) : List Bool := BinaryNat.add
  (pair (BinaryNat.add (pair (F.mass c) (BinaryNat.mul (pair (F.exponent c) (F.parameterDegree c)))))
    (BinaryNatCode.encode (BinaryNat.succ (F.degree c)).length))

theorem massCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : massCode F ∈ FP := by
  have hm := mem_FP_comp (mem_FP_pair hF.exponent hF.parameterDegree) BinaryNat.mul_mem_FP
  have hs := mem_FP_comp (mem_FP_pair hF.mass hm) BinaryNat.add_mem_FP
  have hl := bits_mem_FP (UnaryFn.length (mem_FP_comp hF.degree BinaryNat.succ_mem_FP))
  have h := mem_FP_comp (mem_FP_pair hs hl) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := massCode F) h ?_
  intro c
  simp only [massCode, Function.comp_apply, BinaryNatCode.encode]

theorem massCode_value (F : Family) (c : List Bool) : Nat.fromBitsLE (massCode F c) =
    Nat.fromBitsLE (F.mass c) + Nat.fromBitsLE (F.exponent c) * Nat.fromBitsLE (F.parameterDegree c) +
      (Nat.fromBitsLE (F.degree c) + 1).size := by
  simp only [massCode, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]

theorem specialized_degree (F : Family) (c : List Bool) :
    (F.specialized c).natDegree ≤ Nat.fromBitsLE (F.degree c) :=
  (DyadicPolynomial.natDegree_le _ _ _).trans (F.polynomial_degree c)

theorem specialized_mass (F : Family) (c : List Bool) :
    coefficientMass (F.specialized c) ≤ 2 ^ Nat.fromBitsLE (massCode F c) := by
  rw [massCode_value]
  exact DyadicPolynomial.mass_le _ _ _ _ _ (F.polynomial_degree c) (F.coefficient_degree c) (F.coefficient_mass c)

end LeanCanny.Algebra.DyadicPolynomialBits
