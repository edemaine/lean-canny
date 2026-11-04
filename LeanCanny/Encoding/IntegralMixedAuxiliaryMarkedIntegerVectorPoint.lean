/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVector
public import LeanCanny.Geometry.BoundedMarkedLiftCoordinates
/-! # The first spatial fields are the canonical marked lift -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem values_markedLift (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ)
    (ctx : List Bool) (q : MvPolynomial (Fin (number n ctx)) ℤ) (D b : ℕ)
    (a : BoundedZeroSource.Bounded q (R ctx)) (x : ℕ→ℝ)
    (hx : ∀i,∀hi : i<number n ctx,x i=a.val ⟨i,hi⟩) :
    (fun i : Fin (number n ctx+4)=>values n t R ctx x
      (BoundedRegularSource.sphereSlack q (R ctx) a)
      (BoundedRegularSource.regularSlack q D b (R ctx) a).re i.val)=
      (BoundedRegularSource.markedLift q D b (R ctx) a).val.val :=by
  let U:=BoundedRegularSource.sphereSlack q (R ctx) a
  let V:=(BoundedRegularSource.regularSlack q D b (R ctx) a).re
  funext i
  change values n t R ctx x U V i.val=(BoundedRegularSource.lift q D b (R ctx) a).val i
  rw [BoundedRegularSource.lift_coordinates]
  refine Fin.addCases (fun j : Fin (number n ctx)=>?_) (fun k : Fin 4=>?_) i
  · change values n t R ctx x U V j.val=
      (Fin.append (Fin.append a.val ![U,0]) ![V,0]) ((j.castAdd 2).castAdd 2)
    rw [Fin.append_left,Fin.append_left]
    simp only [values,ite_eq_left j.isLt]
    exact hx j.val j.isLt
  · fin_cases k
    · change values n t R ctx x U V (number n ctx)=
        (Fin.append (Fin.append a.val ![U,0]) ![V,0]) ((Fin.natAdd (number n ctx) (0 : Fin 2)).castAdd 2)
      rw [Fin.append_left,Fin.append_right]
      simp only [Matrix.cons_val_zero]
      unfold values
      split_ifs <;> first | rfl | omega
    · change values n t R ctx x U V (number n ctx+1)=
        (Fin.append (Fin.append a.val ![U,0]) ![V,0]) ((Fin.natAdd (number n ctx) (1 : Fin 2)).castAdd 2)
      rw [Fin.append_left,Fin.append_right]
      simp only [Matrix.cons_val_one]
      unfold values
      split_ifs <;> first | rfl | omega
    · change values n t R ctx x U V (number n ctx+2)=
        (Fin.append (Fin.append a.val ![U,0]) ![V,0]) (Fin.natAdd (number n ctx+2) (0 : Fin 2))
      rw [Fin.append_right]
      simp only [Matrix.cons_val_zero]
      unfold values
      split_ifs <;> first | rfl | omega
    · change values n t R ctx x U V (number n ctx+3)=
        (Fin.append (Fin.append a.val ![U,0]) ![V,0]) (Fin.natAdd (number n ctx+2) (1 : Fin 2))
      rw [Fin.append_right]
      simp only [Matrix.cons_val_one]
      unfold values
      split_ifs <;> first | rfl | omega

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
