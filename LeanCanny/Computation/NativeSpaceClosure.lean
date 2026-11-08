/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! # Lightweight native polynomial-space interfaces

Encoding-parametric decider equivalence and reduction closure use the native
plain space calculus. A polynomial-time tidy certificate can be passed through
the library's conversion to plain polynomial time.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolySpace

/-- Include tidy polynomial time in plain space with one automation transition. -/
@[fun_prop]
theorem of_tidyPolyTime {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ComputableTidilyInPolyTime f encIn encOut) :
    ComputableInPolySpace f encIn encOut :=
  of_polyTime hf.computableInPolyTime

end Turing.MultiTapeTM.ComputableInPolySpace

namespace LeanCanny.Computation.NativeSpace
open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Native class membership agrees with a Boolean polynomial-space decider. -/
theorem mem_iff : A ∈ Cslib.Complexity.PSPACE enc ↔
    ∃ f : α → Bool, ComputableInPolySpace f enc encBool ∧
      ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain ⟨c, d, hcd⟩ := hs.exists_le
    refine ⟨f, ⟨t, fun n => c * (n + 1) ^ d + 1, by fun_prop,
      hf.mono (fun _ => le_rfl) (fun a => (hcd a).trans (Nat.le_succ _)),
      fun _ => by simp⟩, hA⟩
  · rintro ⟨f, ⟨t, s, hs, hf, _⟩, hA⟩
    exact ⟨f, ⟨t, _, .of_polynomiallyBounded _ hs, hf⟩, hA⟩

/-- A Boolean space certificate gives native class membership. -/
theorem of_computable {f : α → Bool} (hf : ComputableInPolySpace f enc encBool)
    (hA : ∀ a, a ∈ A ↔ f a = true) : A ∈ Cslib.Complexity.PSPACE enc :=
  mem_iff.mpr ⟨f, hf, hA⟩

/-- Polynomial-time preimages preserve native polynomial space, for any encodings. -/
theorem preimage {β : Type} {encB : β ↪ List Bool} {B : Set β} {g : α → β}
    (hg : ComputableTidilyInPolyTime g enc encB) (hB : B ∈ Cslib.Complexity.PSPACE encB) :
    g ⁻¹' B ∈ Cslib.Complexity.PSPACE enc := by
  obtain ⟨f, hf, hB⟩ := mem_iff.mp hB
  exact of_computable (hf.comp (.of_tidyPolyTime hg)) (fun a => hB (g a))

/-- Closure under native many-one reductions with their specified encodings. -/
theorem of_reduction {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : Cslib.Complexity.PolyTimeReducible enc encB A B)
    (hB : B ∈ Cslib.Complexity.PSPACE encB) : A ∈ Cslib.Complexity.PSPACE enc := by
  obtain ⟨g, hg, hAB⟩ := h
  have hA : A = g ⁻¹' B := Set.ext hAB
  rw [hA]
  exact preimage hg.tidy hB

end LeanCanny.Computation.NativeSpace
