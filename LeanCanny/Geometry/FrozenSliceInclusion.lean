/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenAuxiliaryComponentSampling

/-! # Literal inclusion of a newly frozen original slice

A point in the old slice supplies all previous frozen values. Freezing one
more of its original coordinates gives a subspace of that same old slice.
Clopen labels pull back continuously, and the selected point survives.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenAuxiliaryComponentSampling
open MvPolynomial Set
variable {n k l : ℕ} {q : MvPolynomial (Fin n) ℝ} {a : Fin n → ℝ}

noncomputable def includeLater (hkl : k≤l) (b : slice q k a) : slice q l b.val → slice q k a :=
  fun y => ⟨y.val,by
    refine ⟨y.property.1,?_⟩
    intro i hi
    exact (y.property.2 i (hi.trans_le hkl)).trans (b.property.2 i hi)⟩

theorem includeLater_val (hkl : k≤l) (b : slice q k a) (y : slice q l b.val) :
    (includeLater hkl b y).val=y.val := rfl

theorem continuous_includeLater (hkl : k≤l) (b : slice q k a) : Continuous (includeLater hkl b) :=
  continuous_subtype_val.subtype_mk _

theorem includeLater_injective (hkl : k≤l) (b : slice q k a) : Function.Injective (includeLater hkl b) := by
  intro x y h
  have HE := congrArg (fun z : slice q k a => z.val) h
  exact Subtype.ext HE

noncomputable def includeNext (b : slice q k a) : slice q (k+1) b.val → slice q k a :=
  includeLater (Nat.le_succ k) b

theorem continuous_includeNext (b : slice q k a) : Continuous (includeNext b) :=
  continuous_includeLater (Nat.le_succ k) b

noncomputable def nextPoint (b : slice q k a) : slice q (k+1) b.val :=
  ⟨b.val,b.property.1,fun _ _ => rfl⟩

theorem includeNext_nextPoint (b : slice q k a) : includeNext b (nextPoint b)=b := Subtype.ext rfl

noncomputable def nextLabel (b : slice q k a) (C : Set (slice q k a)) : Set (slice q (k+1) b.val) :=
  includeNext b ⁻¹' C

theorem nextLabel_clopen (b : slice q k a) (C : Set (slice q k a)) (hC : IsClopen C) :
    IsClopen (nextLabel b C) := hC.preimage (continuous_includeNext b)

theorem nextPoint_mem_nextLabel (b : slice q k a) (C : Set (slice q k a)) (hb : b∈C) :
    nextPoint b∈nextLabel b C := by
  change includeNext b (nextPoint b)∈C
  rw [includeNext_nextPoint]
  exact hb

theorem nextLabel_preserves_point (b : slice q k a) (C : Set (slice q k a))
    (y : slice q (k+1) b.val) (hy : y∈nextLabel b C) :
    ∃ old : slice q k a, old∈C ∧ old.val=y.val := ⟨includeNext b y,hy,rfl⟩

theorem terminal_value (a : Fin n → ℝ) (x : slice q n a) : x.val=a := by
  funext i
  exact x.property.2 i i.isLt

theorem terminal_unique (a : Fin n → ℝ) (x y : slice q n a) : x=y := by
  apply Subtype.ext
  exact (terminal_value a x).trans (terminal_value a y).symm

theorem terminal_nonempty_iff (a : Fin n → ℝ) : (slice q n a).Nonempty ↔ q.eval a=0 := by
  constructor
  · rintro ⟨x,hx⟩
    have H := terminal_value a ⟨x,hx⟩
    exact H ▸ hx.1
  · intro h
    exact ⟨a,h,fun _ _ => rfl⟩

end LeanCanny.Geometry.FrozenAuxiliaryComponentSampling
