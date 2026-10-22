/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefreeSpace
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Square-free leaves as one-dimensional polynomial determinant tasks

The matrix contains the existing scaled square-free polynomial. Its entry
reader uses the certified square-free routine and ignores the two matrix
indices, which are necessarily zero in dimension one. Metadata and query
preparation are FP; square-free preprocessing may take arbitrary time in
polynomial space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.SeparableBits.LeafMatrix
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial MatrixPower

def modulus (c : List Bool) : ℕ := Nat.fromBitsLE (pairSnd c) + 1

noncomputable def family (F : Family) (degree : List Bool → ℕ) : BerkowitzPolynomial.ModularFamily where
  dimension _ := 1
  modulus := modulus
  degree c := degree (pairFst c)
  matrix c := fun _ _ => (ScaledSquarefree.polynomial (F.polynomial (pairFst c))).map (Int.castRingHom (ZMod (modulus c)))
  modulus_ne_zero _ := by unfold modulus; omega

def query (p : List Bool) : List Bool := pair (pairFst p) (pairSnd (pairSnd (pairSnd p)))

theorem query_FP : query ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

theorem squarefreeValue_packet (F : Family) (c : List Bool) (d : ℕ) :
    squarefreeValue F (pair c (BinaryNatCode.encode d)) =
      residueBits (((ScaledSquarefree.polynomial (F.polynomial (pairFst c))).coeff d : ℤ) : ZMod (modulus c)) := by
  unfold squarefreeValue
  have hc : ScaledQuotientBits.context (pair c (BinaryNatCode.encode d)) = pairFst c := by
    simp only [ScaledQuotientBits.context, pairFst_pair]
  have hm : ScaledQuotientBits.modulus (pair c (BinaryNatCode.encode d)) = modulus c := by
    simp only [ScaledQuotientBits.modulus, ScaledQuotientBits.modulusWord, pairFst_pair, modulus]
  rw [hc, hm]
  simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def access (F : Family) (degree : List Bool → ℕ) (degreeCode : List Bool → List Bool)
    (hd : ∀ c, degreeCode c = BinaryNatCode.encode (degree c)) :
    BerkowitzPolynomial.ModularAccess (family F degree) where
  dimension _ := [true]
  modulus := BinaryNat.succ ∘ pairSnd
  degree := degreeCode ∘ pairFst
  entry := squarefreeValue F ∘ query
  dimension_eq _ := by simp only [family, BinaryNatCode.encode, Nat.one_bits]
  modulus_eq _ := BinaryNat.succ_eq_bits _
  degree_eq c := hd (pairFst c)
  entry_eq := by
    intro c i j d
    change Fin 1 at i j
    simp only [Function.comp_apply, query, pairFst_pair, pairSnd_pair]
    rw [squarefreeValue_packet]
    change residueBits (((ScaledSquarefree.polynomial (F.polynomial (pairFst c))).coeff d : ℤ) : ZMod (modulus c)) =
      residueBits (((ScaledSquarefree.polynomial (F.polynomial (pairFst c))).map (Int.castRingHom (ZMod (modulus c)))).coeff d)
    simp only [Polynomial.coeff_map, Int.coe_castRingHom]

theorem controls (F : Family) (degree : List Bool → ℕ) (degreeCode : List Bool → List Bool)
    (hd : ∀ c, degreeCode c = BinaryNatCode.encode (degree c)) (hFP : degreeCode ∈ FP) :
    (access F degree degreeCode hd).ControlsPolyTime := by
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP hFP
  exact ⟨constFn_mem_FP [true], hm, hk⟩

theorem entry_space (F : Family) (A : Readers F) (degree : List Bool → ℕ)
    (degreeCode : List Bool → List Bool) (hd : ∀ c, degreeCode c = BinaryNatCode.encode (degree c)) :
    SpaceFunction (access F degree degreeCode hd).entry :=
  (squarefreeEvaluator F A).precompose query query_FP

theorem value_eq (F : Family) (degree : List Bool → ℕ) (c : List Bool) :
    (family F degree).value c = squarefreeValue F (pair c (BinaryNatCode.encode (degree (pairFst c)))) := by
  rw [squarefreeValue_packet]
  change residueBits ((Matrix.det (fun (_ _ : Fin 1) =>
    (ScaledSquarefree.polynomial (F.polynomial (pairFst c))).map (Int.castRingHom (ZMod (modulus c))))).coeff
      (degree (pairFst c))) = _
  rw [Matrix.det_fin_one, Polynomial.coeff_map]
  simp only [Int.coe_castRingHom]

end LeanCanny.Algebra.SeparableBits.LeafMatrix
