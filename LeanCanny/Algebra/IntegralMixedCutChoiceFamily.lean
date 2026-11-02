/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
public import LeanCanny.Algebra.IntegralMixedRawKindSquarefreeSelection
public import LeanCanny.Algebra.IntegralMixedRawKindValueSelection
public import LeanCanny.Algebra.IntegralMixedRawKindLimitSelection
public import LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientSnapshot
/-! # Snapshot kind identities for finite choice probes

The auxiliary family changes only Kind, so every old state, source, rule
and basis remains literal. It is used to prove the snapshot identities;
native coefficient programs continue to query the original family.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutChoiceFamilyBits
open IntegralMixedCutSource IntegralMixedRawKindBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family (F : Family) (k : ℕ) : Family :=
  {F with kind key:=IntegralMixedRelativeCuts.atChoice (F.rule key) (F.kind key) k}

theorem tag_family (F : Family) (k : ℕ) (key : List Bool) : tag (family F k) key=tag F key := by
  cases he : F.kind key <;> simp only [tag,family,IntegralMixedRelativeCuts.atChoice,he]
theorem coordinate_family (F : Family) (k : ℕ) (key : List Bool) : coordinate (family F k) key=coordinate F key := by
  cases he : F.kind key <;> simp only [coordinate,family,IntegralMixedRelativeCuts.atChoice,he]
theorem choice_family (F : Family) (k : ℕ) (key : List Bool) : choice (family F k) key=min k (choice F key) := by
  cases he : F.kind key <;> simp only [choice,family,IntegralMixedRelativeCuts.atChoice,he]

private theorem coordinate_snapshot (F : Family) (k : ℕ) (key : List Bool) (j c : ℕ) :
    IntegralMixedCoordinateCoefficientSnapshot.kind (family F k) key j c=IntegralMixedCoordinateCoefficientSnapshot.kind F key j c := by rfl

private theorem squarefree_snapshot (F : Family) (k : ℕ) (key : List Bool) (j c : ℕ) :
    IntegralMixedRawKindBits.squarefreeKind (family F k) key j c=IntegralMixedRawKindBits.squarefreeKind F key j c := by rfl

private theorem value_snapshot (F : Family) (k : ℕ) (key : List Bool) (j c : ℕ) :
    IntegralMixedValueCoefficientSnapshot.kind (family F k) key j c=IntegralMixedValueCoefficientSnapshot.kind F key j c := by rfl

private theorem limit_snapshot (F : Family) (k : ℕ) (key : List Bool) (j c : ℕ) :
    IntegralMixedRawKindBits.limitKind (family F k) key j c=IntegralMixedRawKindBits.limitKind F key j c := by rfl

theorem coordinate_kind (F : Family) (key : List Bool) (k : ℕ) (ht : tag F key=2) :
    IntegralMixedRelativeCuts.atChoice (F.rule key) (F.kind key) k=
      IntegralMixedCoordinateCoefficientSnapshot.kind F key (coordinate F key) (min k (choice F key)) := by
  have HE:=IntegralMixedRawKindBits.coordinate_kind (family F k) key ((tag_family F k key).trans ht)
  rw [coordinate_family,choice_family,coordinate_snapshot] at HE
  exact HE

theorem squarefree_kind (F : Family) (key : List Bool) (k : ℕ) (ht : tag F key=3) :
    IntegralMixedRelativeCuts.atChoice (F.rule key) (F.kind key) k=
      IntegralMixedSquarefreeCoefficientSnapshot.kind F key (coordinate F key) (min k (choice F key)) := by
  have HE:=IntegralMixedRawKindBits.squarefree_kind (family F k) key ((tag_family F k key).trans ht)
  rw [coordinate_family,choice_family,squarefree_snapshot] at HE
  exact HE

theorem value_kind (F : Family) (key : List Bool) (k : ℕ) (ht : tag F key=4) :
    IntegralMixedRelativeCuts.atChoice (F.rule key) (F.kind key) k=
      IntegralMixedValueCoefficientSnapshot.kind F key (coordinate F key) (min k (choice F key)) := by
  have HE:=IntegralMixedRawKindBits.value_kind (family F k) key ((tag_family F k key).trans ht)
  rw [coordinate_family,choice_family,value_snapshot] at HE
  exact HE

theorem limit_kind (F : Family) (key : List Bool) (k : ℕ) (ht : tag F key=5) :
    IntegralMixedRelativeCuts.atChoice (F.rule key) (F.kind key) k=
      IntegralMixedRawKindBits.limitKind F key (coordinate F key) (min k (choice F key)) := by
  have HE:=IntegralMixedRawKindBits.limit_kind (family F k) key ((tag_family F k key).trans ht)
  rw [coordinate_family,choice_family,limit_snapshot] at HE
  exact HE

end LeanCanny.Algebra.IntegralMixedCutChoiceFamilyBits
