/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalTower
public import LeanCanny.Encoding.BoundedCriticalProjection
public import LeanCanny.Encoding.BoundedFullCoefficient

/-! # Native controls for flat affine-height towers

Directions and level records are charged space-bounded readers. Signed
coefficients use two fixed-width unsigned blocks. Level records select a
constant, an earlier height, or a midpoint of two earlier heights. References
are clamped to existing stages; empty ancestry always selects a constant.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourceTower
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

structure Inputs where
  source : BoundedFullWriter.Readers
  depth : List Bool → ℕ
  width : List Bool → ℕ
  direction : List Bool → List Bool
  level : List Bool → List Bool

structure Inputs.Access (F : Inputs) : Prop where
  source : F.source.PolyTime
  depth : UnaryFn F.depth
  width : UnaryFn F.width
  direction : SpaceFunction F.direction
  level : SpaceFunction F.level
  sourceArity : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u

def stage (u : List Bool) (k : ℕ) : List Bool := pair u (BinaryNatCode.encode k)
def levelQuery (u : List Bool) (k j : ℕ) : List Bool := pair (stage u k) (BinaryNatCode.encode j)
def arity (F : Inputs) (u : List Bool) : ℕ := F.source.dim u + 4
def stageWidth (F : Inputs) (u : List Bool) : ℕ := FlatAffineCriticalTower.width (arity F u)
def count (F : Inputs) (u : List Bool) : ℕ := F.depth u * stageWidth F u

/-- Each signed entry is a difference of two unsigned width-bit words. -/
def integer (w : ℕ) (v : List Bool) (j : ℕ) : ℤ :=
  (Nat.fromBitsLE ((v.drop (j * (2 * w))).take w) : ℤ) -
    (Nat.fromBitsLE ((v.drop (j * (2 * w) + w)).take w) : ℤ)

theorem integer_bound (w : ℕ) (v : List Bool) (j : ℕ) : (integer w v j).natAbs ≤ 2 ^ (w + 1) := by
  have hp := ((Nat.fromBitsLE_lt_pow_length ((v.drop (j * (2 * w))).take w)).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))).le
  have hn := ((Nat.fromBitsLE_lt_pow_length ((v.drop (j * (2 * w) + w)).take w)).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))).le
  exact (Int.natAbs_sub_le _ _).trans (by
    simp only [Int.natAbs_natCast]
    rw [pow_succ]
    omega)

def flags (r : List Bool) : List Bool := pairFst r
def left (r : List Bool) : List Bool := pairFst (pairSnd r)
def right (r : List Bool) : List Bool := pairFst (pairSnd (pairSnd r))
def normal (r : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd r)))
def constant (r : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd r)))
def tag (r : List Bool) : ℕ := Nat.fromBitsLE (((flags r).drop 1).take 2)
def active (r : List Bool) : Bool := (flags r).headD false

def direction (F : Inputs) (u : List Bool) (k : ℕ) (r : Fin (arity F u + 1)) (i : Fin (arity F u)) : ℤ :=
  integer (F.width u) (F.direction (stage u k)) (r.val * arity F u + i.val)

noncomputable def free (F : Inputs) (u : List Bool) (k : ℕ) : Finset (Fin (arity F u)) :=
  Finset.univ.filter (fun j => active (F.level (levelQuery u k j.val)))

noncomputable def level (F : Inputs) (u : List Bool) (k : ℕ) (j : Fin (arity F u)) :
    FlatAffineCriticalTower.Level (arity F u) k ℤ :=
  let r := F.level (levelQuery u k j.val)
  let a := fun i : Fin (arity F u) => integer (F.width u) (normal r) i.val
  if hk : 0 < k then
    let l : Fin k := ⟨min (Nat.fromBitsLE (left r)) (k - 1), by omega⟩
    let h : Fin k := ⟨min (Nat.fromBitsLE (right r)) (k - 1), by omega⟩
    if tag r = 1 then .height l a else if tag r = 2 then .midpoint l h a
      else .constant (integer (F.width u) (constant r) 0)
  else .constant (integer (F.width u) (constant r) 0)

noncomputable def family (F : Inputs) (u : List Bool) : TriangularPolynomialTower.Family (stageWidth F u) ℤ :=
  FlatAffineCriticalTower.family (BoundedFullCriticalSamples.polynomial F.source u) (free F u)
    (direction F u) (level F u)

noncomputable def system (F : Inputs) (u : List Bool) : Fin (count F u) → MvPolynomial (Fin (count F u)) ℤ :=
  TriangularPolynomialIndexing.system (family F u) (F.depth u)

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ := BoundedFullWriter.degree F.source u + 1
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  BoundedCriticalProjection.sourceBits F.source u + (degree F u).size + (F.width u + 1) + (arity F u).size + 4

theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) := h.source.dim.add (UnaryFn.const 4)
theorem stageWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (stageWidth F) :=
  (arity_unary h).add ((arity_unary h).add (UnaryFn.const 1))
theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) := h.depth.mul (stageWidth_unary h)
theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (BoundedFullWriter.degree_binary h.source).add (BinaryFn.const 1)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  (((BoundedCriticalProjection.sourceBits_binary h.source).add (degree_binary h).size).add
    ((BinaryFn.ofUnary h.width).add (BinaryFn.const 1))).add
      ((BinaryFn.ofUnary (arity_unary h)).size) |>.add (BinaryFn.const 4)

theorem count_le (F : Inputs) (u : List Bool) (h : F.depth u ≤ arity F u) :
    count F u ≤ arity F u * (2 * arity F u + 1) := FlatAffineCriticalTower.variables_le _ h

theorem direction_bound (F : Inputs) (u : List Bool) (k : ℕ) (r : Fin (arity F u + 1)) (i : Fin (arity F u)) :
    (direction F u k r i).natAbs ≤ 2 ^ (F.width u + 1) := integer_bound _ _ _

theorem level_bound (F : Inputs) (u : List Bool) (k : ℕ) (j : Fin (arity F u)) :
    (level F u k j).Bounded (2 ^ (F.width u + 1)) (2 ^ (F.width u + 1)) := by
  unfold level
  dsimp only
  split_ifs <;> simp only [FlatAffineCriticalTower.Level.Bounded] <;>
    first | exact integer_bound _ _ _ | exact fun _ => integer_bound _ _ _

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (system F u i).totalDegree ≤ degree F u := by
  apply (FlatAffineCriticalTower.degree_le (BoundedFullCriticalSamples.polynomial F.source u)
    (free F u) (direction F u) (level F u) (F.depth u) i).trans
  apply max_le
  · exact (BoundedFullCriticalSamples.source_degree F.source u).trans (Nat.le_succ _)
  · unfold degree
    omega

theorem polynomial_mass (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    MvMass.mass (system F u i) ≤ 2 ^ mass F u := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let S := BoundedCriticalProjection.sourceBits F.source u
  let D := (degree F u).size
  let W := F.width u + 1
  let N := (arity F u).size
  let T := S + D + W + N + 2
  have hpow (a b : ℕ) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
  have hp : MvMass.mass p ≤ 2 ^ T := (BoundedCriticalProjection.source_mass F.source u).trans (hpow S T (by omega))
  have hd : p.totalDegree * MvMass.mass p ≤ 2 ^ T := by
    have hdegree : p.totalDegree ≤ 2 ^ D := (BoundedFullCriticalSamples.source_degree F.source u).trans
      ((Nat.le_succ _).trans (Nat.lt_size_self (degree F u)).le)
    exact ((Nat.mul_le_mul hdegree (BoundedCriticalProjection.source_mass F.source u)).trans_eq
      (pow_add 2 D S).symm).trans (hpow (D + S) T (by omega))
  have hn : arity F u + 1 ≤ 2 ^ (N + 1) := by
    have h := Nat.lt_size_self (arity F u)
    dsimp only [N]
    rw [pow_succ]
    omega
  have hnu : (arity F u + 1) * 2 ^ W ≤ 2 ^ T := by
    exact ((Nat.mul_le_mul_right (2 ^ W) hn).trans_eq (pow_add 2 (N + 1) W).symm).trans
      (hpow (N + 1 + W) T (by omega))
  have hsmall : arity F u * 2 ^ W ≤ 2 ^ T := (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans hnu
  have hU : 2 ^ W ≤ 2 ^ T := hpow W T (by omega)
  have htwice : 2 * arity F u * 2 ^ W ≤ 2 ^ T := by
    calc
      _ ≤ 2 * (2 ^ (N + 1)) * 2 ^ W := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ((Nat.le_succ _).trans hn))
      _ = 2 ^ (N + 1 + W + 1) := by rw [pow_add, pow_succ]; ring
      _ ≤ 2 ^ T := hpow _ _ (by omega)
  apply (FlatAffineCriticalTower.mass_le p (free F u) (direction F u) (level F u) (F.depth u)
    (2 ^ W) (2 ^ W) (fun k _ => direction_bound F u k) (fun k _ => level_bound F u k) i).trans
  unfold FlatAffineCriticalStage.massBound
  have hmass : mass F u = T + 2 := rfl
  rw [hmass]
  have hp4 : (2 : ℕ) ^ (T + 2) = 2 ^ T * 4 := by
    calc
      _ = 2 ^ T * 2 ^ 2 := pow_add 2 T 2
      _ = _ := rfl
  apply max_le
  · apply max_le
    · exact hp.trans (hpow _ _ (by omega))
    · calc
        _ ≤ 2 ^ T + 2 ^ T := Nat.add_le_add hd hnu
        _ ≤ 2 ^ (T + 2) := by rw [hp4]; omega
  · calc
      _ ≤ 2 ^ T + 2 ^ T + 1 := Nat.add_le_add_right (Nat.add_le_add hsmall (max_le hU htwice)) 1
      _ ≤ 2 ^ (T + 2) := by have := Nat.one_le_two_pow (n := T); rw [hp4]; omega

theorem degree_pos (F : Inputs) (u : List Bool) : 0 < degree F u := by
  unfold degree
  omega

end LeanCanny.Encoding.FlatAffineFullSourceTower
