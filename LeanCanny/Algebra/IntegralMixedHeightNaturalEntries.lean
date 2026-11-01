/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightMatrix
/-! # Natural-index physical and virtual affine height matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (m B r : ℕ) : Fin (count m B) := ⟨r % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
def oldIndex (m B r : ℕ) : Fin (count m B) := ⟨(r / 2 ^ B) % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
def digit (B r : ℕ) : Fin (2 ^ B) := ⟨r % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem split_index (m B r : ℕ) : pairIndex m B (oldIndex m B r, digit B r) = index (m + 1) B r := by
  apply Fin.ext
  change r % 2 ^ B + 2 ^ B * ((r / 2 ^ B) % count m B) = r % count (m + 1) B
  have hc : count (m + 1) B = 2 ^ B * count m B := by
    unfold count
    rw [pow_succ, Nat.mul_comm]
  rw [hc]
  have he := Nat.mod_add_div (r % (2 ^ B * count m B)) (2 ^ B)
  rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at he
  exact he

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def physical (x : State P S B m ι) (hm : m ≤ S) (rule : CriticalRule n)
    (i : Fin (n + 1)) (r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
    (CoordinateFrozenCriticalElimination.numerators (data x hm rule).scales (data x hm rule).heights i.val)
      (index m B r) (index m B t)

theorem physical_eq (x : State P S B m ι) (hm : m ≤ S) (rule : CriticalRule n)
    (i : Fin (n + 1)) (r t : ℕ) : physical x hm rule i r t =
      IntegralMixedHeightCofactor.value x rule i *
        IntegralMixedHeightMatrix.affineEntry x (rule.heights i) (index m B r) (index m B t) :=
  IntegralMixedHeightMatrix.entry x hm rule i _ _

noncomputable def virtual (x : State P S B m ι) (hm : m ≤ S) (rule : IntegralMixedCriticalSweep.Rule n)
    (i : Fin (n + 1)) (r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
    (AdjoinRoot.mk (Polynomial.X ^ (2 ^ B))
      (CoordinateFrozenCriticalElimination.numerators (data x hm rule.critical).scales
        (IntegralMixedCriticalSweep.heights x rule) i.val))
      (index (m + 1) B r) (index (m + 1) B t)

theorem virtual_eq (x : State P S B m ι) (hm : m ≤ S) (rule : IntegralMixedCriticalSweep.Rule n)
    (i : Fin (n + 1)) (r t : ℕ) : virtual x hm rule i r t =
      if r % 2 ^ B = t % 2 ^ B then IntegralMixedHeightCofactor.value x rule.critical i *
        IntegralMixedHeightMatrix.affineEntry x (rule.critical.heights i) (oldIndex m B r) (oldIndex m B t)
      else if r % 2 ^ B = t % 2 ^ B + 1 then
        (if i = rule.height then rule.slope * IntegralMixedHeightCofactor.value x rule.critical i else 0) *
          (if oldIndex m B r = oldIndex m B t then 1 else 0) else 0 := by
  unfold virtual
  rw [← split_index m B r, ← split_index m B t, IntegralMixedVirtualHeight.matrix,
    IntegralMixedHeightMatrix.virtual_constant, IntegralMixedHeightMatrix.virtual_slope]
  rfl

end LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
