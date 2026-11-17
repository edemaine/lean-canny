/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledRelativeCharacteristic
public import LeanCanny.CountingHierarchy.PowerSectionPolynomial
public import LeanCanny.CountingHierarchy.RelativeCriticalMinimum
public import LeanCanny.CountingHierarchy.FirstVariableCoefficients

/-! # Uniform fixed-power sections of actual relative critical polynomials -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

variable {n m : ℕ}

noncomputable def finiteRelativeSection (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) : MvPolynomial (Fin (m + 1)) ℤ :=
  powerSectionPolynomial ((d + 1) ^ n + 1) (finiteRelativeCharacteristic d P hP)

theorem eval_finiteRelativeCharacteristic_point {S : Type*} [CommRing S]
    (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (t u : S) (x : Fin m → S) :
    MvPolynomial.eval₂ (Int.castRingHom S) (Fin.cons t (Fin.cons u x))
      (finiteRelativeCharacteristic d P hP) =
    (LeanCanny.CountingHierarchy.relativeCharacteristic d (MvPolynomial.rename finSumFinEquiv.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hP)).eval₂
      (relativeParameterEvaluation u x) t := by
  rw [finiteRelativeCharacteristic, MvPolynomial.eval₂_rename]
  unfold flattenedRelativeCharacteristic
  have hcoords : (Fin.cons t (Fin.cons u x) ∘ relativeVariable) =
      (fun i : Option (Option (Fin m)) => i.elim t (fun j => j.elim u x)) := by
    funext i
    cases i with
    | none => rfl
    | some i => cases i <;> rfl
  rw [hcoords]
  exact eval_flattenParameterPolynomial (Int.castRingHom S) _ _ _

theorem eval_finiteRelativeSection (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (v : ℝ) (x : Fin m → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons v x) (finiteRelativeSection d P hP) =
      (relativeBivariate d (MvPolynomial.rename finSumFinEquiv.symm P)
        ((MvPolynomial.totalDegree_rename_le _ _).trans hP) x).eval₂
        (Polynomial.evalRingHom (v ^ ((d + 1) ^ n + 1))) v := by
  change MvPolynomial.eval₂ _ _ (MvPolynomial.eval₂ MvPolynomial.C _ _) = _
  rw [← MvPolynomial.eval₂_assoc]
  have hcoords : (fun i : Fin (m + 2) => MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons v x)
      (powerSectionImage ((d + 1) ^ n + 1) i)) = Fin.cons v (Fin.cons (v ^ ((d + 1) ^ n + 1)) x) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
      simp only [powerSectionImage, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ,
        MvPolynomial.eval₂_X, MvPolynomial.eval₂_pow]
  rw [hcoords, eval_finiteRelativeCharacteristic_point, ← Polynomial.eval_map, ← relativeBivariate_map,
    Polynomial.eval_map]

namespace Controlled

noncomputable def relativeSection {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => finiteRelativeSection (2 * (C.degreeBound w + 1)) (P w)
      ((C.degree_le w).trans (by omega))) enc (a + 10) := by
  have hd := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.binary_add' C.degree_computable (.const 1))
  exact (C.relativeCharacteristic E hn hm).powerSection hm _
    (ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn) (.const 1))

end Controlled
end LeanCanny.CountingHierarchy
