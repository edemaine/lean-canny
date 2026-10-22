/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BivariateDeterminantInteger

/-! # Native integer coefficients of a matrix determinant over ℤ[alpha] -/
@[expose] public section
namespace LeanCanny.Algebra.PolynomialDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def strip (q : List Bool) : List Bool := pair (pairFst q)
  (pair (pairFst (pairSnd q)) (pair (pairFst (pairSnd (pairSnd q)))
    (pairFst (pairSnd (pairSnd (pairSnd q))))))
def outer (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd q)))

theorem strip_FP : strip ∈ FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
      (mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP)))
theorem outer_FP : outer ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

noncomputable def liftEntry (coefficient : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (outer q) = 0 then coefficient (strip q) else []

theorem liftEntryEvaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient) :
    SpaceFunction (liftEntry coefficient) := by
  have hg := BinaryNat.lt_fppred outer_FP (constFn_mem_FP (BinaryNatCode.encode 1))
  have hz : FPPred (fun q => Nat.fromBitsLE (outer q) = 0) := hg.of_iff (fun q => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  have EB := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (outer q) = 0)) hz.flag_mem_FP
    (E.precompose strip strip_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact EB.congr (funext fun q => by simp only [liftEntry, decide_eq_true_eq, Function.comp_apply])

noncomputable def value (N : List Bool → ℕ) (modulus target : List Bool → List Bool)
    (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ)) (c : List Bool) : List Bool :=
  residueBits ((((P c).det.coeff (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))

theorem evaluator (N : List Bool → ℕ) (modulus target bound coefficient : List Bool → List Bool)
    (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hN : ∀ c, 0 < N c) (hP : ∀ c i j, (P c i j).natDegree ≤ Nat.fromBitsLE (bound c))
    (hc : ∀ c (i j : Fin (N c)) k,
      coefficient (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
        residueBits ((((P c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)))
    (E : SpaceFunction coefficient) (hn : (fun c => BinaryNatCode.encode (N c)) ∈ FP)
    (hm : modulus ∈ FP) (ht : target ∈ FP) (hb : bound ∈ FP) : SpaceFunction (value N modulus target P) := by
  let Q := fun c => (P c).map Polynomial.C
  have hQ c (i j : Fin (N c)) k : ((Q c i j).coeff k).natDegree ≤ Nat.fromBitsLE (bound c) := by
    simp only [Q, Matrix.map_apply, Polynomial.coeff_C]
    split_ifs
    · exact hP c i j
    · simp
  have hread c (i j : Fin (N c)) u v :
      liftEntry coefficient (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val)
        (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      residueBits (((((Q c i j).coeff v).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
    simp only [liftEntry, outer, strip, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Q, Matrix.map_apply, Polynomial.coeff_C]
    by_cases hv : v=0
    · simp only [hv, ite_true]
      exact hc c i j u
    · simp [hv, residueBits, BinaryNatCode.encode]
  have ED := BivariateDeterminantBits.integerEvaluator N modulus target (fun _ => []) bound Q
    (liftEntry coefficient) hN hQ hread (liftEntryEvaluator E) hn hm ht (constFn_mem_FP []) hb
  refine ED.congr (funext fun c => ?_)
  change residueBits ((((((P c).map Polynomial.C).det).coeff 0).coeff
    (Nat.fromBitsLE (target c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) = _
  have hd := (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ)).map_det (P c)
  rw [RingHom.mapMatrix_apply] at hd
  rw [← hd, Polynomial.coeff_C_zero]
  rfl

end LeanCanny.Algebra.PolynomialDeterminantBits
