/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelParameters
import Mathlib.Tactic.Ring

/-! # Packing rational parameter tuples without losing their values

The three fixed-width blocks recover signed numerators and positive
denominators exactly when they fit. A width derived from the component bit
lengths represents every rational tuple. This proves representability.
The exact packet-length formula gives a linear bound in source length and
coordinate count times the bit allowance. Bounding a suitable geometric
tuple in the source size remains separate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term

noncomputable def pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) : List Bool :=
  pair bits (pair (List.replicate W true)
    (pair (FixedWidthNatVector.encode (TubeParameter.parameterCount bits) W p)
      (pair (FixedWidthNatVector.encode (TubeParameter.parameterCount bits) W n)
        (FixedWidthNatVector.encode (TubeParameter.parameterCount bits) W d))))

@[simp] theorem source_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) :
    pairFst (pack bits W p n d) = bits := by simp only [pack, pairFst_pair]

@[simp] theorem width_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) :
    width (pack bits W p n d) = W := by
  simp only [width, widthWord, pack, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem positive_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) (i : ℕ)
    (hi : i < TubeParameter.parameterCount bits) (hp : p i < 2 ^ W) :
    positive (pack bits W p n d) i = p i := by
  simp only [positive, FixedWidthQuery.coordinate, width, widthWord, List.length_replicate, positiveWord, pack, pairFst_pair, pairSnd_pair]
  exact FixedWidthNatVector.decode_block _ _ _ _ hi hp

theorem negative_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) (i : ℕ)
    (hi : i < TubeParameter.parameterCount bits) (hn : n i < 2 ^ W) :
    negative (pack bits W p n d) i = n i := by
  simp only [negative, FixedWidthQuery.coordinate, width, widthWord, List.length_replicate, negativeWord, pack, pairFst_pair, pairSnd_pair]
  exact FixedWidthNatVector.decode_block _ _ _ _ hi hn

theorem denominatorNat_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) (i : ℕ)
    (hi : i < TubeParameter.parameterCount bits) (hd : d i < 2 ^ W) :
    denominatorNat (pack bits W p n d) i = d i + 1 := by
  simp only [denominatorNat, FixedWidthQuery.coordinate, width, widthWord, List.length_replicate, denominatorWord, pack, pairFst_pair, pairSnd_pair]
  rw [FixedWidthNatVector.decode_block _ _ _ _ hi hd]

noncomputable def rationalPack (bits : List Bool) (W : ℕ) (q : ℕ → ℚ) : List Bool :=
  pack bits W (fun i => (q i).num.toNat) (fun i => (-(q i).num).toNat) (fun i => (q i).den - 1)

theorem rationalValue_rationalPack (bits : List Bool) (W : ℕ) (q : ℕ → ℚ) (i : ℕ)
    (hi : i < TubeParameter.parameterCount bits) (hp : (q i).num.toNat < 2 ^ W)
    (hn : (-(q i).num).toNat < 2 ^ W) (hd : (q i).den - 1 < 2 ^ W) :
    rationalValue (rationalPack bits W q) i = q i := by
  unfold rationalPack rationalValue integer
  rw [positive_pack _ _ _ _ _ _ hi hp, negative_pack _ _ _ _ _ _ hi hn,
    denominatorNat_pack _ _ _ _ _ _ hi hd, Int.toNat_sub_toNat_neg,
    Nat.sub_add_cancel (q i).den_pos]
  exact (q i).num_div_den

/-- Bits in the two signed-numerator parts and the positive denominator. -/
def rationalBits (q : ℚ) : ℕ := q.num.toNat.size + (-q.num).toNat.size + q.den.size

@[simp] theorem rationalBits_zero : rationalBits 0 = 1 := rfl

noncomputable def rationalWidth (bits : List Bool) (q : ℕ → ℚ) : ℕ :=
  Finset.univ.sup (fun i : Fin (TubeParameter.parameterCount bits) => rationalBits (q i.val))

theorem rationalValue_pack_width (bits : List Bool) (q : ℕ → ℚ) (i : ℕ)
    (hi : i < TubeParameter.parameterCount bits) :
    rationalValue (rationalPack bits (rationalWidth bits q) q) i = q i := by
  have hb : (q i).num.toNat.size + (-(q i).num).toNat.size + (q i).den.size ≤ rationalWidth bits q :=
    Finset.le_sup (f := fun j : Fin (TubeParameter.parameterCount bits) =>
      (q j.val).num.toNat.size + (-(q j.val).num).toNat.size + (q j.val).den.size) (Finset.mem_univ ⟨i, hi⟩)
  apply rationalValue_rationalPack _ _ _ _ hi
  · exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (Nat.sub_le _ _).trans_lt ((Nat.lt_size_self _).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem exists_packet (bits : List Bool) (q : ℕ → ℚ) :
    ∃ c : List Bool, pairFst c = bits ∧ ∀ i, i < TubeParameter.parameterCount bits → rationalValue c i = q i := by
  refine ⟨rationalPack bits (rationalWidth bits q) q, ?_, rationalValue_pack_width bits q⟩
  simp only [rationalPack, source_pack]

theorem length_pack (bits : List Bool) (W : ℕ) (p n d : ℕ → ℕ) :
    (pack bits W p n d).length =
      2 * bits.length + 2 * W + 5 * (TubeParameter.parameterCount bits * W) + 8 := by
  simp only [pack, pair_length, List.length_replicate, FixedWidthNatVector.length_encode]
  omega

theorem length_rationalPack (bits : List Bool) (W : ℕ) (q : ℕ → ℚ) :
    (rationalPack bits W q).length =
      2 * bits.length + (5 * TubeParameter.parameterCount bits + 2) * W + 8 := by
  rw [rationalPack, length_pack]
  ring

theorem rationalWidth_le (bits : List Bool) (q : ℕ → ℚ) (B : ℕ)
    (hB : ∀ i, i < TubeParameter.parameterCount bits →
      rationalBits (q i) ≤ B) :
    rationalWidth bits q ≤ B :=
  Finset.sup_le (fun i _ => hB i.val i.isLt)

theorem length_rationalPack_le (bits : List Bool) (q : ℕ → ℚ) (B : ℕ)
    (hB : ∀ i, i < TubeParameter.parameterCount bits →
      rationalBits (q i) ≤ B) :
    (rationalPack bits (rationalWidth bits q) q).length ≤
      2 * bits.length + (5 * TubeParameter.parameterCount bits + 2) * B + 8 := by
  rw [length_rationalPack]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (rationalWidth_le bits q B hB)) _) _

end LeanCanny.ETR.TubeLevelPacket
