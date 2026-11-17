/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SplitPolynomialEvaluation
public import LeanCanny.CountingHierarchy.PointBlocks
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite variable blocks and exact evaluation at padded joined points -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial

variable {n m : ℕ}

noncomputable def splitFinitePolynomial (P : MvPolynomial (Fin (n + m)) ℤ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ) :=
  splitIntegerPolynomial (MvPolynomial.rename finSumFinEquiv.symm P)

theorem eval_splitFinitePolynomial {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (x : Fin n → S) (z : Fin m → S) (P : MvPolynomial (Fin (n + m)) ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval₂Hom phi z) x (splitFinitePolynomial P) =
      MvPolynomial.eval₂ phi (Fin.addCases x z) P := by
  rw [splitFinitePolynomial, eval_splitIntegerPolynomial, MvPolynomial.eval₂_rename]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem splitFinitePolynomial_mass_le (P : MvPolynomial (Fin (n + m)) ℤ) :
    MultivariateParameterMass.mass (splitFinitePolynomial P) ≤ LeanCanny.Algebra.MvMass.mass P :=
  (splitIntegerPolynomial_mass_le _).trans (LeanCanny.Algebra.MvMass.rename_le _ _)

theorem splitFinitePolynomial_mainDegree_le (P : MvPolynomial (Fin (n + m)) ℤ) :
    (splitFinitePolynomial P).totalDegree ≤ P.totalDegree :=
  (splitIntegerPolynomial_mainDegree_le _).trans (MvPolynomial.totalDegree_rename_le _ _)

theorem splitFinitePolynomial_parameterDegree_le (P : MvPolynomial (Fin (n + m)) ℤ) :
    HasMultivariateParameterDegree (splitFinitePolynomial P) P.totalDegree :=
  (splitIntegerPolynomial_parameterDegree_le _).mono (MvPolynomial.totalDegree_rename_le _ _)

noncomputable def specializeFinitePolynomial {S : Type*} [CommRing S]
    (P : MvPolynomial (Fin (n + m)) ℤ) (phi : ℤ →+* S) (z : Fin m → S) : MvPolynomial (Fin n) S :=
  (splitFinitePolynomial P).map (MvPolynomial.eval₂Hom phi z)

theorem eval_specializeFinitePolynomial {S : Type*} [CommRing S]
    (P : MvPolynomial (Fin (n + m)) ℤ) (phi : ℤ →+* S) (x : Fin n → S) (z : Fin m → S) :
    MvPolynomial.eval x (specializeFinitePolynomial P phi z) = MvPolynomial.eval₂ phi (Fin.addCases x z) P := by
  rw [specializeFinitePolynomial, MvPolynomial.eval_map, eval_splitFinitePolynomial]

theorem eval_joinedPoint {S : Type*} [CommRing S] (P : MvPolynomial (Fin (n + m)) ℤ)
    (phi : ℤ →+* S) (x z : List ℕ) :
    MvPolynomial.eval₂ phi (fun i : Fin (n + m) => ((joinedPoint n m x z)[i.val]?.getD 0 : S)) P =
      MvPolynomial.eval (fun i : Fin n => (x[i.val]?.getD 0 : S))
        (specializeFinitePolynomial P phi (fun i : Fin m => (z[i.val]?.getD 0 : S))) := by
  rw [eval_specializeFinitePolynomial]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left, Fin.val_castAdd] using congrArg (Nat.cast : ℕ → S) (joinedPoint_left n m x z j)
  · simpa only [Fin.addCases_right, Fin.val_natAdd] using congrArg (Nat.cast : ℕ → S) (joinedPoint_right n m x z j)

end LeanCanny.CountingHierarchy
