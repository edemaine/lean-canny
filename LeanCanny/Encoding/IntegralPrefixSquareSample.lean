/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareAccess
public import LeanCanny.Algebra.IntegralMixedFramedDegreeSchedule

/-! # Actual scalar prefixes instantiate complete native square sampling

The literal prefix rows and fixed birth-degree schedule provide infinity
exclusion and all degree controls. Original row mass and row coefficient
access remain charged frontend inputs; no annihilator or regularity oracle
is required. Positive birth count is explicit; an empty bank stays separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPrefixSquareSample
open LeanCanny.Algebra LeanCanny.Computation UniformIntegralPowerSchedule
open scoped Classical

structure Family where
  horizon : List Bool→ℕ
  width : List Bool→ℕ
  count : List Bool→ℕ
  mass : List Bool→ℕ
  prefixAt : (u : List Bool)→UniformIntegralPrefix.Prefix (horizon u) (2^width u) (count u)
  count_pos : ∀ u, 0<count u
  scheduled : ∀ u i, (prefixAt u).degrees i=2^width u*weights (horizon u) (2^width u) (count u) i
  row_mass : ∀ u i, MvMass.mass ((prefixAt u).rows i)≤2^mass u

def degree (F : Family) (u : List Bool) : ℕ := 2^F.width u*birth (F.horizon u) (2^F.width u) (F.count u-1)
def rowDegree (F : Family) (u : List Bool) (i : ℕ) : ℕ :=
  2^F.width u*birth (F.horizon u) (2^F.width u) (F.count u-1-i)

noncomputable def finite (F : Family) : NoInfinitySquareSample.Family where
  count := F.count
  degree := degree F
  mass := F.mass
  rowDegree := rowDegree F
  rows u := (F.prefixAt u).rows
  count_pos := F.count_pos
  degree_pos u := Nat.mul_pos (Nat.two_pow_pos _) (birth_pos _ _ _)
  row_degree u i := ((F.prefixAt u).row_degree i).trans_eq (F.scheduled u i)
  rowDegree_pos u i := Nat.mul_pos (Nat.two_pow_pos _) (birth_pos _ _ _)
  rowDegree_le u i := Nat.mul_le_mul_left _ (weights_le _ _ _ i)
  row_mass := F.row_mass
  noInfinity u := by
    have HD : (F.prefixAt u).degrees=(fun i=>rowDegree F u i.val) := funext (F.scheduled u)
    rw [←HD]
    exact (F.prefixAt u).noInfinity

noncomputable def input (F : Family) : SquareSampleInput.Inputs := NoInfinitySquareSample.input (finite F)

structure Access (F : Family) : Prop where
  horizon : UnaryFn F.horizon
  width : UnaryFn F.width
  count : UnaryFn F.count
  mass : BinaryFn F.mass
  row : SpaceFunction (SquareSampleInput.rowCoefficient (input F))

theorem degree_binary {F : Family} (h : Access F) : BinaryFn (degree F) :=
  ((BinaryFn.const 2).powUnary h.width).mul
    (birth_binary h.horizon ((BinaryFn.const 2).powUnary h.width) (h.count.sub (UnaryFn.const 1)))

theorem rowDegree_binary {F : Family} (h : Access F) :
    BinaryFn (fun q=>rowDegree F (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
  have HN := (BinaryFn.const 2).powUnary h.width
  have HP := BinaryFn.mul (HN.comp pairFst_mem_FP) (power_binary h.horizon HN h.count)
  apply BinaryFn.of_eq HP
  intro q
  unfold rowDegree power age
  have HE : F.count (pairFst q)-1-min (Nat.fromBitsLE (pairSnd q)) (F.count (pairFst q))=
      F.count (pairFst q)-1-Nat.fromBitsLE (pairSnd q) := by omega
  rw [HE]
  rfl

theorem finiteAccess {F : Family} (h : Access F) : NoInfinitySquareSample.Access (finite F) :=
  ⟨h.count,degree_binary h,h.mass,rowDegree_binary h,h.row⟩

theorem access {F : Family} (h : Access F) : (input F).Access := NoInfinitySquareSample.access (finiteAccess h)
theorem complete (F : Family) : SquareSampleComplete.Complete (input F) := NoInfinitySquareSample.complete (finite F)
theorem count_evaluator {F : Family} (h : Access F) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (input F) u)) :=
  SquareSampleComplete.count_evaluator (access h) (complete F)

end LeanCanny.Encoding.IntegralPrefixSquareSample
