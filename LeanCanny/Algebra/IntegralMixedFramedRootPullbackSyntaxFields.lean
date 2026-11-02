/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
public import LeanCanny.Algebra.IntegralMixedFramedNativeSyntax

/-! # Literal integer and LOW polynomial transport through the projected key -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open scoped Classical

noncomputable def integerAt {n B : ℕ} (I : Instruction n B) : Polynomial ℤ :=
  match I.command with
  | .integer p _ _ => p
  | _ => Polynomial.X

theorem integerAt_eq (P : Parameters) (D : Plan P) (q : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D q=integerAt (IntegralMixedFramedHistoryFamilyBits.instruction P D q) := by
  unfold IntegralMixedFramedIntegerBits.polynomial integerAt
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D q).command <;> rfl

theorem integer_polynomial (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial (parameters P project extra) (plan P D project extra) q=
      IntegralMixedFramedIntegerBits.polynomial P D (key project q) := by
  have HS := instruction_read (fun _ _ I=>integerAt I) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)
  exact (integerAt_eq _ _ _).trans (HS.trans (integerAt_eq P D _).symm)

noncomputable def lowAt (n : ℕ) (t : ETR.Term) (k u E : ℕ) : MvPolynomial (Fin (n+1)) ℤ :=
  MvPolynomial.rename Fin.castSucc ((FixedLeadingTiltedSource.lowTerm k t.toData.size u t).finitePolynomial n)-
    MvPolynomial.C ((2 : ℤ)^E)*MvPolynomial.X (Fin.last n)

theorem lowAt_congr (n m : ℕ) (t : ETR.Term) (k u E : ℕ) (h : n=m) :
    HEq (lowAt n t k u E) (lowAt m t k u E) := by cases h; rfl

theorem low_formula_heq (P : Parameters) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (t : List Bool→ETR.Term) (k u E : List Bool→ℕ) (q : List Bool) :
    HEq (FermatLevelFramedTiltedSyntax.low (parameters P project extra)
      (t ∘ key project) (k ∘ key project) (u ∘ key project) (E ∘ key project) q)
      (FermatLevelFramedTiltedSyntax.low P t k u E (key project q)) :=
  lowAt_congr _ _ _ _ _ _ (congrArg P.ambient (key_root project q).symm)

theorem source_low_heq (P : Parameters) (D : Plan P) (project : List Bool→List Bool)
    (extra : List Bool→ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction (parameters P project extra) (plan P D project extra) q).source.low
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (key project q)).source.low :=
  instruction_read_heq (fun _ _ I=>I.source.low) _ _
    (congrArg P.ambient (key_root project q).symm) (congrArg P.width (key_root project q).symm)
    (instruction_heq P D project extra q)

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
