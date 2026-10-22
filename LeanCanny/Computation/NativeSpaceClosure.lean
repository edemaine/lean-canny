/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-! # Lightweight native polynomial-space interfaces

Encoding-parametric tidy equivalence and reduction closure require only native
space and reduction modules. Keeping them here avoids the unrelated hierarchy,
probability, and Savitch imports of the broad upstream inclusions module. The
namespace prevents collisions if that module is imported by a downstream user.
-/

@[expose] public section
namespace LeanCanny.Computation.NativeSpace
open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Native class membership agrees with a tidy Boolean polynomial-space decider. -/
theorem mem_iff : A ∈ Cslib.Complexity.PSPACE enc ↔
    ∃ f : α → Bool, ComputableTidilyInPolySpace f enc encBool ∧
      ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain ⟨c, hf⟩ := hf.exists_computableTidilyInTimeAndSpace
    refine ⟨f, ⟨(fun a => 2 * t a + 3 * s a + c),
      (fun a => c * (s a + 1) + 1),
      ((PolyBounded.const c).mul (hs.add (.const 1))).add (.const 1),
      ComputableTidilyInO.of_bounds hf 1 ?_ ?_ ?_⟩, hA⟩
    · intro a; omega
    · intro a; omega
    · intro a
      simp only [encBool_apply, List.length_singleton, one_mul]
      omega
  · rintro ⟨f, ⟨T, S, hS, c, h, -⟩, hA⟩
    exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)),
      h.computableInTimeAndSpace⟩, hA⟩

/-- A tidy Boolean space certificate gives native class membership. -/
theorem of_computable {f : α → Bool} (hf : ComputableTidilyInPolySpace f enc encBool)
    (hA : ∀ a, a ∈ A ↔ f a = true) : A ∈ Cslib.Complexity.PSPACE enc :=
  mem_iff.mpr ⟨f, hf, hA⟩

/-- Polynomial-time preimages preserve native polynomial space, for any encodings. -/
theorem preimage {β : Type} {encB : β ↪ List Bool} {B : Set β} {g : α → β}
    (hg : ComputableTidilyInPolyTime g enc encB) (hB : B ∈ Cslib.Complexity.PSPACE encB) :
    g ⁻¹' B ∈ Cslib.Complexity.PSPACE enc := by
  obtain ⟨f, hf, hB⟩ := mem_iff.mp hB
  exact of_computable (hf.comp (.of_polyTime hg)) (fun a => hB (g a))

/-- Closure under native many-one reductions with their specified encodings. -/
theorem of_reduction {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : Cslib.Complexity.PolyTimeReducible enc encB A B)
    (hB : B ∈ Cslib.Complexity.PSPACE encB) : A ∈ Cslib.Complexity.PSPACE enc := by
  obtain ⟨g, hg, hAB⟩ := h
  have hA : A = g ⁻¹' B := Set.ext hAB
  rw [hA]
  exact preimage hg hB

end LeanCanny.Computation.NativeSpace
