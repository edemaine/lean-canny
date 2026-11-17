/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledPreprocessing
public import LeanCanny.CountingHierarchy.SourceNormDeterminantCorrectness
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign

/-! # Integer residue access to the final norm of a controlled source family -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

@[expose] noncomputable def normInteger (C : Controlled P enc a) (d : α → ℕ)
    (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1) (data : α → List (ℕ × ℕ)) (e : α → ℕ) (w : α) : ℤ :=
  codedFiniteCriticalDeterminant (d w) (C.massExponent w) (P w) (hdeg w) (data w) (e w)

@[expose] def normCutoff (C : Controlled P enc a) (d : α → ℕ) (w : α) : ℕ :=
  max (C.cutoff w) (sourceNormPrimeCutoff (n w) (d w) (C.massExponent w))

/-- The access contract needs no recognizer for admissible primes or expanded
integer value; its one total residue program is explicitly constructed. -/
@[expose] noncomputable def normAccess (C : Controlled P enc a) (d : α → ℕ)
    (hd : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    (data : α → List (ℕ × ℕ)) (e : α → ℕ) :
    IntegerResidueAccess (C.normInteger d hdeg data e) where
  magnitudeExponent := fun w => criticalNormMassExponent (n w) (d w) (C.massExponent w)
  admissible := fun w p => p.Prime ∧ C.normCutoff d w < p
  modulus_pos := fun _ _ hp => hp.1.pos
  residue := fun q => sourceNormDeterminantValue q.2 (n q.1) (d q.1) (C.massExponent q.1)
    (e q.1) (data q.1) (fun y => C.evaluate (q.1, q.2, y))
  magnitude_le w := codedFiniteCriticalDeterminant_natAbs_le (d w) (hd w) (C.massExponent w)
    (P w) (hdeg w) (C.mass_le w) (data w) (e w)
  residue_eq w p hp := by
    let : Fact p.Prime := ⟨hp.1⟩
    let : NeZero p := ⟨hp.1.ne_zero⟩
    have hsource : C.cutoff w < p := (le_max_left _ _).trans_lt hp.2
    have hnorm : sourceNormPrimeCutoff (n w) (d w) (C.massExponent w) < p :=
      (le_max_right _ _).trans_lt hp.2
    have hvalue (y : List ℕ) : (C.evaluate (w, p, y) : ZMod p) =
        eval (fun i : Fin (n w) => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) ((P w).map (Int.castRingHom (ZMod p))) := by
      rw [C.evaluate_eq w p y hp.1 hsource, evaluation, ZMod.natCast_zmod_val, MvPolynomial.eval_map]
    have hcast := sourceNormDeterminantValue_cast (d w) (hd w) (C.massExponent w) (e w)
      (P w) (hdeg w) (C.mass_le w) hnorm (data w) (fun y => C.evaluate (w, p, y)) hvalue
    have hsmall : sourceNormDeterminantValue p (n w) (d w) (C.massExponent w) (e w) (data w)
        (fun y => C.evaluate (w, p, y)) < p := by
      unfold sourceNormDeterminantValue quotientDeterminantValue
      exact Nat.mod_lt _ hp.1.pos
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hsmall] at hv
    exact hv.trans (by
      simpa only [Int.toNat_natCast, normInteger] using
        (congrArg Int.toNat (ZMod.val_intCast (n := p)
          (codedFiniteCriticalDeterminant (d w) (C.massExponent w) (P w) (hdeg w) (data w) (e w)))))

end LeanCanny.CountingHierarchy.Controlled
