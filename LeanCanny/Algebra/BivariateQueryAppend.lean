/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateQueryProductBounds

/-! # Concatenation of native indexed bivariate families

Factor addresses are shifted in binary. A single coefficient query selects
one original reader; no polynomial list is materialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateQueryProductBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) : BinaryFn (fun c => max (f c) (g c)) :=
  (BinaryFn.ite (hf.le hg) hg hf).of_eq (fun _ => by simp only [max_def])

noncomputable def Family.append (F G : Family) : Family where
  polynomial c i := if i < F.count c then F.polynomial c i else G.polynomial c (i - F.count c)
  exponent c i := if i < F.count c then F.exponent c i else G.exponent c (i - F.count c)
  count c := F.count c + G.count c
  degree c := max (F.degree c) (G.degree c)
  parameterDegree c := max (F.parameterDegree c) (G.parameterDegree c)
  mass c := max (F.mass c) (G.mass c)
  polynomial_degree c i := by
    split_ifs
    · exact (F.polynomial_degree c i).trans (Nat.le_max_left _ _)
    · exact (G.polynomial_degree c _).trans (Nat.le_max_right _ _)
  coefficient_degree c i j := by
    split_ifs
    · exact (F.coefficient_degree c i j).trans (Nat.le_max_left _ _)
    · exact (G.coefficient_degree c _ j).trans (Nat.le_max_right _ _)
  coefficient_mass c i j := by
    split_ifs
    · exact (F.coefficient_mass c i j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
    · exact (G.coefficient_mass c _ j).trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

noncomputable def appendIndex (F : Family) (w : List Bool) : List Bool :=
  pair (pairFst w) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd w) - F.count (pairFst w)))

theorem appendIndex_FP {F : Family} (A : Access F) : appendIndex F ∈ FP := by
  have hi := (BinaryFn.fromBits pairSnd_mem_FP).sub (A.count_binary.comp pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP hi.bits_mem_FP

noncomputable def appendQuery (F : Family) (z : List Bool) : List Bool :=
  pair (pair (appendIndex F (pairFst (pairFst z))) (pairSnd (pairFst z))) (pairSnd z)

theorem appendQuery_FP {F : Family} (A : Access F) : appendQuery F ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (appendIndex_FP A))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def Access.append {F G : Family} (A : Access F) (B : Access G) : Access (F.append G) where
  reader := {
    coefficient z := if Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) < F.count (pairFst (pairFst (pairFst z)))
      then A.reader.coefficient z else B.reader.coefficient (appendQuery F z)
    evaluator := by
      have hi := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
      have hn := A.count_binary.comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
      have H := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) < F.count (pairFst (pairFst (pairFst z)))))
        (hi.lt hn).flag_mem_FP A.reader.evaluator (B.reader.evaluator.precompose (appendQuery F) (appendQuery_FP A))
      exact H.congr (funext fun _ => by simp only [decide_eq_true_eq, Function.comp_apply])
    coefficient_eq q u v := by
      simp only [pairFst_pair]
      by_cases hi : Nat.fromBitsLE (pairSnd (pairFst q)) < F.count (pairFst (pairFst q))
      · rw [ite_eq_left hi, A.reader.coefficient_eq]
        simp only [Family.append, hi, ite_true]
      · rw [ite_eq_right hi]
        simp only [appendQuery, pairFst_pair, pairSnd_pair]
        rw [B.reader.coefficient_eq]
        exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
          (by simp only [Family.append, hi, ite_false, appendIndex, pairFst_pair, pairSnd_pair,
            BinaryNatCode.encode, Nat.fromBitsLE_bits])
          (by rw [pairSnd_pair]) }
  exponent w := if Nat.fromBitsLE (pairSnd w) < F.count (pairFst w) then A.exponent w else B.exponent (appendIndex F w)
  exponent_eq c i := by
    have hc : Nat.fromBitsLE (BinaryNatCode.encode i) = i := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [pairFst_pair, pairSnd_pair, hc]
    by_cases hi : i < F.count c
    · rw [ite_eq_left hi, A.exponent_eq]
      simp only [Family.append, hi, ite_true]
    · rw [ite_eq_right hi]
      simp only [appendIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      change B.exponent (pair c (BinaryNatCode.encode (i - F.count c))) = _
      rw [B.exponent_eq]
      simp only [Family.append, hi, ite_false, BinaryNatCode.encode]
  exponent_FP := by
    have hp := (BinaryFn.fromBits pairSnd_mem_FP).lt (A.count_binary.comp pairFst_mem_FP)
    exact hp.ite_mem_FP A.exponent_FP (mem_FP_comp (appendIndex_FP A) B.exponent_FP)
  count_binary := A.count_binary.add B.count_binary
  degree_binary := max_binary A.degree_binary B.degree_binary
  parameterDegree_binary := max_binary A.parameterDegree_binary B.parameterDegree_binary
  mass_binary := max_binary A.mass_binary B.mass_binary

end LeanCanny.Algebra.BivariateQueryProductBits
