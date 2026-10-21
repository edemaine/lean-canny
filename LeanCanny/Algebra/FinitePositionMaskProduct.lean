/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FinitePositionMasks
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators

/-! # Products of position masks grouped by their greatest position -/

@[expose] public section

namespace LeanCanny.Algebra.FinitePositionMasks
open scoped BigOperators Classical

noncomputable def lastMasksUnionEquiv (q k : ℕ) :
    ((j : Fin q) × ↥(lastMasks q k j)) ≃ PositionMask q (k + 1) :=
  Equiv.ofBijective (fun a => ⟨a.2.val, ((mem_lastMasks q k a.1 a.2.val).mp a.2.property).2.1⟩)
    ⟨by
      rintro ⟨a, u⟩ ⟨b, v⟩ he
      have hv := congrArg (fun s : PositionMask q (k + 1) => s.val) he
      change u.val = v.val at hv
      have hb : u.val ∈ lastMasks q k b := by simpa only [hv] using v.property
      have hab := (exists_unique_last q k
        ⟨u.val, ((mem_lastMasks q k a u.val).mp u.property).2.1⟩).unique u.property hb
      subst b
      exact congrArg (Sigma.mk a) (Subtype.ext hv),
      by
        intro s
        obtain ⟨j, hj, _⟩ := exists_unique_last q k s
        exact ⟨⟨j, ⟨s.val, hj⟩⟩, Subtype.ext rfl⟩⟩

theorem prod_lastMasks {M : Type*} [CommMonoid M] (q k : ℕ) (f : Finset (Fin q) → M)
    (hf : ∀ m, m.card ≠ k + 1 → f m = 1) :
    (∏ m : Finset (Fin q), f m) = ∏ j : Fin q, ∏ m : lastMasks q k j, f m.val := by
  have hr := Fintype.prod_of_injective (Subtype.val : PositionMask q (k + 1) → Finset (Fin q))
    Subtype.val_injective (fun s => f s.val) f
    (by
      intro m hm
      apply hf m
      intro hc
      exact hm ⟨⟨m, hc⟩, rfl⟩)
    (fun _ => rfl)
  rw [← hr]
  have he := Fintype.prod_equiv (lastMasksUnionEquiv q k)
    (fun a => f a.2.val) (fun s => f s.val) (fun _ => rfl)
  rw [← he, Fintype.prod_sigma]

end LeanCanny.Algebra.FinitePositionMasks
