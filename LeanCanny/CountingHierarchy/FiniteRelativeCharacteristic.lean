/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCharacteristicBounds
public import LeanCanny.CountingHierarchy.RelativeCriticalSpecialization
public import LeanCanny.CountingHierarchy.FinitePolynomialBlocks

/-! # A finite-variable presentation of the relative characteristic polynomial -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial

variable {n m : ℕ}

def relativeVariable : Option (Option (Fin m)) → Fin (m + 2)
  | none => ⟨0, by omega⟩
  | some none => ⟨1, by omega⟩
  | some (some i) => ⟨i.val + 2, by omega⟩

noncomputable def finiteRelativeCharacteristic (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) : MvPolynomial (Fin (m + 2)) ℤ :=
  MvPolynomial.rename relativeVariable
    (flattenedRelativeCharacteristic d (MvPolynomial.rename finSumFinEquiv.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hP))

theorem finiteRelativeCharacteristic_degree_le (d : ℕ) (hd : 1 ≤ d)
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1) :
    (finiteRelativeCharacteristic d P hP).totalDegree ≤
      (d + 1) ^ n + relativeCharacteristicParameterDegreeBound n d :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (flattenedRelativeCharacteristic_degree_le d hd _ _)

theorem finiteRelativeCharacteristic_mass_le (d b : ℕ) (hd : 1 ≤ d)
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (hM : LeanCanny.Algebra.MvMass.mass P ≤ 2 ^ b) :
    LeanCanny.Algebra.MvMass.mass (finiteRelativeCharacteristic d P hP) ≤
      2 ^ relativeCharacteristicMassExponent n d b :=
  (LeanCanny.Algebra.MvMass.rename_le _ _).trans
    (flattenedRelativeCharacteristic_mass_le d b hd _ _
      ((LeanCanny.Algebra.MvMass.rename_le _ _).trans hM))

theorem eval_finiteRelativeCharacteristic {S : Type*} [CommRing S]
    (phi : ℤ →+* S) (d : ℕ) (P : MvPolynomial (Fin (n + m)) ℤ)
    (hP : P.totalDegree ≤ d + 1) (z : List ℕ) :
    MvPolynomial.eval₂ phi (fun i : Fin (m + 2) => (z[i.val]?.getD 0 : S))
      (finiteRelativeCharacteristic d P hP) =
    (relativeCharacteristic d (MvPolynomial.rename finSumFinEquiv.symm P)
      ((MvPolynomial.totalDegree_rename_le _ _).trans hP)).eval₂
      (MvPolynomial.eval₂Hom phi (fun i : Option (Fin m) => i.elim
        ((z[1]?.getD 0 : ℕ) : S) (fun j => ((z.drop 2)[j.val]?.getD 0 : S))))
      ((z[0]?.getD 0 : ℕ) : S) := by
  rw [finiteRelativeCharacteristic, MvPolynomial.eval₂_rename]
  unfold flattenedRelativeCharacteristic
  simp only [Function.comp_def]
  rw [show (fun i : Option (Option (Fin m)) =>
      (z[(relativeVariable i).val]?.getD 0 : S)) =
      (fun i => i.elim ((z[0]?.getD 0 : ℕ) : S)
        (fun j => j.elim ((z[1]?.getD 0 : ℕ) : S)
          (fun k => ((z.drop 2)[k.val]?.getD 0 : S)))) by
    funext i
    cases i with
    | none => rfl
    | some i =>
      cases i with
      | none => rfl
      | some i => simp [relativeVariable, List.getElem?_drop, Nat.add_comm]]
  exact eval_flattenParameterPolynomial phi _ _ _

end LeanCanny.CountingHierarchy
