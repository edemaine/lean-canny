/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockFactorSpace

/-! # Actual algebra values of relative Berkowitz factor branches

The unit, diagonal, and moment branches use the same original algebra and
the same pair of old basis ranks. Negation operates on the requested
integer coefficient entry, with the original caller modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientValue (S : Source) (p : List Bool) (x : S.carrier (original p)) : List Bool := by
  letI := S.ring (original p)
  exact residueBits ((Algebra.leftMulMatrix (S.basis (original p)) x
    (basisIndex S basisRowCode p) (basisIndex S basisColCode p) : ℤ) : ZMod (S.modulus (original p)))

noncomputable def referenceValue (S : Source) (p : List Bool) : List Bool := by
  letI := S.ring (original p)
  exact coefficientValue S p (Berkowitz.FactorChild.value (S.matrix (original p))
    (stage S p) (targetStage S p) (sourceDegree S p) (targetDegree S p))

theorem zero_value (S : Source) (p : List Bool) :
    letI := S.ring (original p)
    coefficientValue S p 0 = [] := by
  let := S.ring (original p)
  simp only [coefficientValue, map_zero, Matrix.zero_apply, Int.cast_zero, residueBits,
    ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem negative_value (S : Source) (p : List Bool) (x : S.carrier (original p)) :
    letI := S.ring (original p)
    negative S (pair p (coefficientValue S p x)) = coefficientValue S p (-x) := by
  let := S.ring (original p)
  let : NeZero (S.modulus (original p)) := ⟨S.modulus_ne_zero (original p)⟩
  rw [negative, pairFst_pair, pairSnd_pair]
  change ArithmeticBits.negate (pair (BinaryNatCode.encode (S.modulus (original p)))
    (residueBits ((Algebra.leftMulMatrix (S.basis (original p)) x
      (basisIndex S basisRowCode p) (basisIndex S basisColCode p) : ℤ) : ZMod (S.modulus (original p))))) = _
  simp only [coefficientValue, map_neg, Matrix.neg_apply, Int.cast_neg]
  exact ArithmeticBits.negate_residueBits _ _

theorem one_value (S : Source) (p : List Bool) :
    letI := S.ring (original p)
    oneWord S p = coefficientValue S p 1 := by
  let := S.ring (original p)
  let : NeZero (S.modulus (original p)) := ⟨S.modulus_ne_zero (original p)⟩
  by_cases h : (basisIndex S basisRowCode p).val = (basisIndex S basisColCode p).val
  · have HE : basisIndex S basisRowCode p = basisIndex S basisColCode p := Fin.ext h
    rw [oneWord, ite_eq_left h]
    simp only [coefficientValue, map_one, Matrix.one_apply, ite_eq_left HE, Int.cast_one]
    exact ArithmeticBits.one_residueBits _
  · have HE : basisIndex S basisRowCode p ≠ basisIndex S basisColCode p := fun H => h (congrArg Fin.val H)
    rw [oneWord, ite_eq_right h]
    simp only [coefficientValue, map_one, Matrix.one_apply, ite_eq_right HE, Int.cast_zero,
      residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem diagonal_value (S : Source) (a : Access S) (p : List Bool) (hs : stage S p < S.dimension (original p)) :
    a.entry (diagonalQuery S p) = coefficientValue S p
      (S.matrix (original p) ⟨stage S p, hs⟩ ⟨stage S p, hs⟩) :=
  a.entry_eq (original p) ⟨stage S p, hs⟩ ⟨stage S p, hs⟩ (basisIndex S basisRowCode p) (basisIndex S basisColCode p)

theorem moment_value (S : Source) (p : List Bool) (hs : stage S p < S.dimension (original p)) :
    letI := S.ring (original p)
    (momentFamily S).value p = coefficientValue S p
      (borderMoment (fun i => Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs 0 i.succ)
        (fun i => Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs i.succ 0)
        ((Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs).submatrix Fin.succ Fin.succ)
        (targetDegree S p - (sourceDegree S p + 1))) := by
  let := S.ring (original p)
  have HR : (momentFamily S).row p =
      (fun i => Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs 0 i.succ) := by
    funext i
    simp only [momentFamily, Berkowitz.principalBlock, Fin.val_zero, Fin.val_succ]
    congr 1; apply Fin.ext; dsimp only; omega
  have HC : (momentFamily S).column p =
      (fun i => Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs i.succ 0) := by
    funext i
    simp only [momentFamily, Berkowitz.principalBlock, Fin.val_zero, Fin.val_succ]
    congr 1; apply Fin.ext; dsimp only; omega
  have HM : (momentFamily S).matrix p =
      (Berkowitz.principalBlock (S.matrix (original p)) (stage S p) hs).submatrix Fin.succ Fin.succ := by
    funext i j
    simp only [momentFamily, Berkowitz.principalBlock, Matrix.submatrix_apply, Fin.val_succ]
    congr 1 <;> apply Fin.ext <;> dsimp only <;> omega
  change coefficientValue S p (borderMoment ((momentFamily S).row p) ((momentFamily S).column p)
    ((momentFamily S).matrix p) (momentExponent S p)) = _
  rw [HR, HC, HM]
  rfl

attribute [local irreducible] coefficientValue IntegralBlockMomentBits.Family.value

theorem factor_reference (S : Source) (a : Access S) : factorValue S a = referenceValue S := by
  funext p
  let := S.ring (original p)
  let T := S.matrix (original p)
  let s := stage S p
  let t := targetStage S p
  let d := sourceDegree S p
  let k := targetDegree S p
  have Hsel : selector S p = Berkowitz.QueryBits.select (S.dimension (original p)) s t d k := selector_eq S p
  change factorValue S a p = coefficientValue S p (Berkowitz.FactorChild.value T s t d k)
  have HZ (hz : selector S p = []) (hv : Berkowitz.FactorChild.value T s t d k = 0) :
      factorValue S a p = coefficientValue S p (Berkowitz.FactorChild.value T s t d k) := by
    rw [hv, zero_value]
    simp only [factorValue, hz, reduceCtorEq, ite_false]
  by_cases hedge : s + 1 = t
  · by_cases hs : s < (S.dimension (original p))
    · by_cases hshift : k + 1 = d
      · have hm : selector S p = [true] := Hsel.trans ((Berkowitz.QueryBits.select_one_iff (S.dimension (original p)) s t d k).mpr ⟨hedge, hs, hshift⟩)
        rw [factorValue, ite_eq_left hm, one_value]
        simp only [Berkowitz.FactorChild.value, ite_eq_left hedge, dite_eq_left hs,
          Berkowitz.coefficientKernel_cases, ite_eq_left hshift]
      · by_cases hdiag : k = d
        · have hm : selector S p = [false, true] := Hsel.trans ((Berkowitz.QueryBits.select_diagonal_iff (S.dimension (original p)) s t d k).mpr ⟨hedge, hs, hdiag⟩)
          have hnot : selector S p ≠ [true] := by rw [hm]; decide
          rw [factorValue, ite_eq_right hnot, ite_eq_left hm, diagonal_value S a p hs, negative_value]
          simp only [Berkowitz.FactorChild.value, ite_eq_left hedge, dite_eq_left hs,
            Berkowitz.coefficientKernel_cases, ite_eq_right hshift, ite_eq_left hdiag,
            Berkowitz.principalBlock, Fin.val_zero, Nat.add_zero]
          rfl
        · by_cases hmoment : d < k ∧ k ≤ (S.dimension (original p)) - s - 1
          · have hm : selector S p = [true, true] := Hsel.trans ((Berkowitz.QueryBits.select_moment_iff (S.dimension (original p)) s t d k).mpr
                ⟨hedge, hs, hmoment.1, hmoment.2⟩)
            have hnot₁ : selector S p ≠ [true] := by rw [hm]; decide
            have hnot₂ : selector S p ≠ [false, true] := by rw [hm]; decide
            rw [factorValue, ite_eq_right hnot₁, ite_eq_right hnot₂, ite_eq_left hm, moment_value S p hs, negative_value]
            simp only [Berkowitz.FactorChild.value, ite_eq_left hedge, dite_eq_left hs,
              Berkowitz.coefficientKernel_cases, ite_eq_right hshift, ite_eq_right hdiag, ite_eq_left hmoment]
            rfl
          · apply HZ
            · rw [Hsel]
              simp only [Berkowitz.QueryBits.select, ite_eq_left hedge, ite_eq_left hs,
                ite_eq_right hshift, ite_eq_right hdiag]
              by_cases hk : d < k
              · rw [ite_eq_left hk, ite_eq_right (fun H => hmoment ⟨hk, H⟩)]
              · rw [ite_eq_right hk]
            · simp only [Berkowitz.FactorChild.value, ite_eq_left hedge, dite_eq_left hs,
                Berkowitz.coefficientKernel_cases, ite_eq_right hshift, ite_eq_right hdiag, ite_eq_right hmoment]
    · apply HZ
      · rw [Hsel]
        simp only [Berkowitz.QueryBits.select, ite_eq_left hedge, ite_eq_right hs]
      · simp only [Berkowitz.FactorChild.value, ite_eq_left hedge, dite_eq_right hs]
  · apply HZ
    · rw [Hsel]
      simp only [Berkowitz.QueryBits.select, ite_eq_right hedge]
    · simp only [Berkowitz.FactorChild.value, ite_eq_right hedge]

theorem reference_evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction (referenceValue S) :=
  (factor_evaluator S a E).congr (factor_reference S a)

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
