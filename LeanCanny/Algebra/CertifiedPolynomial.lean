/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeCoefficientSpace

/-! # Certified streamed integer polynomials

Coefficient residues and their native space certificate travel together. Height
and degree allowances are binary FP controls; exact degree is a separate
capability, needed by separability but not by coefficient transformations.
Correctness is required only on canonical index packets. The native functions
are retained on all other inputs, including by semantic congruence.
-/

@[expose] public section

namespace LeanCanny.Algebra.CertifiedPolynomial
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure Family where
  polynomial : List Bool → ℤ[X]
  height : List Bool → ℕ
  coefficient_bound : ∀ c k, ((polynomial c).coeff k).natAbs ≤ 2 ^ height c

structure Readers (F : Family) where
  height : List Bool → List Bool
  coefficient : List Bool → List Bool
  heightFP : height ∈ FP
  height_eq : ∀ c, height c = BinaryNatCode.encode (F.height c)
  coefficient_eq : ∀ q k, coefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.polynomial (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
  evaluator : SpaceFunction coefficient

structure DegreeAllowance (p : List Bool → ℤ[X]) where
  degree : List Bool → List Bool
  degreeFP : degree ∈ FP
  degree_le : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c)

structure ExactDegree (p : List Bool → ℤ[X]) where
  degree : List Bool → List Bool
  degreeFP : degree ∈ FP
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (p c).natDegree

def ExactDegree.allowance {p : List Bool → ℤ[X]} (D : ExactDegree p) : DegreeAllowance p where
  degree := D.degree
  degreeFP := D.degreeFP
  degree_le c := by rw [D.degree_eq]; simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, le_refl]

/-- The determinant backend's inner/outer index order, independent of matrices. -/
structure BivariateReader (p : List Bool → (ℤ[X])[X]) where
  coefficient : List Bool → List Bool
  evaluator : SpaceFunction coefficient
  coefficient_eq : ∀ q u v, coefficient
    (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits ((((p (pairFst q)).coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

/-- Change only semantic proofs; computational fields remain definitionally equal. -/
def Readers.congr {F G : Family} (A : Readers F)
    (hp : ∀ c, F.polynomial c = G.polynomial c) (hh : ∀ c, F.height c = G.height c) : Readers G where
  height := A.height
  coefficient := A.coefficient
  heightFP := A.heightFP
  height_eq c := (A.height_eq c).trans (congrArg BinaryNatCode.encode (hh c))
  coefficient_eq q k := by rw [← hp (pairFst q)]; exact A.coefficient_eq q k
  evaluator := A.evaluator

noncomputable def Family.reindex (F : Family) (input : List Bool → List Bool) : Family where
  polynomial c := F.polynomial (input c)
  height c := F.height (input c)
  coefficient_bound c := F.coefficient_bound (input c)

def reindexQuery (input : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pair (input (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)

theorem reindexQuery_FP (input : List Bool → List Bool) (hi : input ∈ FP) : reindexQuery input ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hi
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hc hm) pairSnd_mem_FP

noncomputable def Readers.reindex {F : Family} (A : Readers F) (input : List Bool → List Bool) (hi : input ∈ FP) :
    Readers (F.reindex input) where
  height := A.height ∘ input
  coefficient := A.coefficient ∘ reindexQuery input
  heightFP := mem_FP_comp hi A.heightFP
  height_eq c := A.height_eq (input c)
  coefficient_eq := by
    intro q k
    have h := A.coefficient_eq (pair (input (pairFst q)) (pairSnd q)) k
    rw [pairFst_pair, pairSnd_pair] at h
    simpa only [Family.reindex, reindexQuery, Function.comp_apply, pairFst_pair, pairSnd_pair] using h
  evaluator := A.evaluator.precompose (reindexQuery input) (reindexQuery_FP input hi)

def ExactDegree.reindex {p : List Bool → ℤ[X]} (D : ExactDegree p)
    (input : List Bool → List Bool) (hi : input ∈ FP) : ExactDegree (p ∘ input) where
  degree := D.degree ∘ input
  degreeFP := mem_FP_comp hi D.degreeFP
  degree_eq c := D.degree_eq (input c)

def DegreeAllowance.reindex {p : List Bool → ℤ[X]} (D : DegreeAllowance p)
    (input : List Bool → List Bool) (hi : input ∈ FP) : DegreeAllowance (p ∘ input) where
  degree := D.degree ∘ input
  degreeFP := mem_FP_comp hi D.degreeFP
  degree_le c := D.degree_le (input c)

theorem derivative_bound (p : ℤ[X]) (b d : ℕ) (hd : p.natDegree ≤ d)
    (h : ∀ k, (p.coeff k).natAbs ≤ 2 ^ b) (k : ℕ) :
    (p.derivative.coeff k).natAbs ≤ 2 ^ (b + d.size) := by
  rw [coeff_derivative, ← Nat.cast_add_one, Int.natAbs_mul, Int.natAbs_natCast]
  by_cases hk : k + 1 ≤ p.natDegree
  · calc
      _ ≤ 2 ^ b * 2 ^ d.size :=
        Nat.mul_le_mul (h _) ((hk.trans hd).trans (Nat.lt_size_self _).le)
      _ = _ := (pow_add _ _ _).symm
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), Int.natAbs_zero, zero_mul]
    exact Nat.zero_le _

def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)

theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

noncomputable def Family.derivative (F : Family) (D : DegreeAllowance F.polynomial) : Family where
  polynomial c := (F.polynomial c).derivative
  height c := F.height c + (Nat.fromBitsLE (D.degree c)).size
  coefficient_bound c := derivative_bound _ _ _ (D.degree_le c) (F.coefficient_bound c)

/-- Normalize the degree word before taking its length: allowances may have padding. -/
def derivativeHeight {F : Family} (A : Readers F) (D : DegreeAllowance F.polynomial) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (A.height c) (BinaryNatCode.encode (BinaryNat.normalize (D.degree c)).length))

noncomputable def Readers.derivative {F : Family} (A : Readers F) (D : DegreeAllowance F.polynomial) :
    Readers (F.derivative D) where
  height := derivativeHeight A D
  coefficient := DerivativeBits.value modulus A.coefficient
  heightFP := by
    have hl := bits_mem_FP (UnaryFn.length (mem_FP_comp D.degreeFP BinaryNat.normalize_mem_FP))
    exact mem_FP_comp (mem_FP_pair A.heightFP hl) BinaryNat.add_mem_FP
  height_eq c := by
    simp only [derivativeHeight, A.height_eq, BinaryNat.add_pair, BinaryNat.normalize_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ← Nat.size_eq_bits_len, Family.derivative]
  coefficient_eq q k := by
    have h := DerivativeBits.packet modulus A.coefficient q _
      ((F.polynomial (pairFst q)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))
      (by simp only [modulus, BinaryNat.succ_eq_bits, BinaryNatCode.encode])
      (fun j => by simpa only [coeff_map, Int.coe_castRingHom] using A.coefficient_eq q j) k
    simpa only [derivative_map, coeff_map, Int.coe_castRingHom, Family.derivative] using h
  evaluator := DerivativeBits.evaluator A.evaluator modulus modulus_FP

def DegreeAllowance.derivative {p : List Bool → ℤ[X]} (D : DegreeAllowance p) :
    DegreeAllowance (fun c => (p c).derivative) where
  degree c := BinaryNat.sub (pair (D.degree c) (BinaryNatCode.encode 1))
  degreeFP := mem_FP_comp (mem_FP_pair D.degreeFP (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  degree_le c := by
    simp only [BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [natDegree_derivative]
    exact Nat.sub_le_sub_right (D.degree_le c) 1

end LeanCanny.Algebra.CertifiedPolynomial
