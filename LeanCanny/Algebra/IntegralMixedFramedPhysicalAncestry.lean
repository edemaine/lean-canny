/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
/-! # Physical block coordinates keep their columns in every later prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFramedHistoryScript (Instruction Index)
open scoped Classical
variable {n B : ℕ}

theorem step_ambient {P : SpatialSource n} {ι : Type} {m : ℕ} (r : CriticalRule n)
    (e : ι≃Fin m) (j : Fin (n+1)) :
    (stepEquiv (.critical r : Command P B) e (Sum.inl (Sum.inr (Sum.inl j)))).val=m+j.val := rfl

theorem step_multiplier {P : SpatialSource n} {ι : Type} {m : ℕ} (r : CriticalRule n)
    (e : ι≃Fin m) (j : Fin (n+2)) :
    (stepEquiv (.critical r : Command P B) e (Sum.inl (Sum.inr (Sum.inr j)))).val=m+((n+1)+j.val) := rfl

/-- The full-carrier column of a selected physical coordinate is its
creating older-prefix arity plus its actual original coordinate number. -/
theorem creating_ambient (P : SpatialSource n) (hcap : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (r : CriticalRule n) (cs : List (Instruction n B)) (j : Fin (n+1)) :
    (enumerate (⟨P,hcap,.critical r⟩::cs) (Sum.inl (Sum.inr (Sum.inl j)))).val=arity cs+j.val :=
  step_ambient r (enumerate cs) j
theorem retained_creating_ambient (P : SpatialSource n)
    (hcap : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (r : CriticalRule n) (newer cs : List (Instruction n B)) (j : Fin (n+1)) :
    (enumerate (newer++⟨P,hcap,.critical r⟩::cs)
      (IntegralMixedFramedPhysicalPersistence.embed newer (⟨P,hcap,.critical r⟩::cs)
        (Sum.inl (Sum.inr (Sum.inl j))))).val=arity cs+j.val :=
  (IntegralMixedFramedPhysicalPersistence.enumerate_embed newer (⟨P,hcap,.critical r⟩::cs) _).trans
    (creating_ambient P hcap r cs j)
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
