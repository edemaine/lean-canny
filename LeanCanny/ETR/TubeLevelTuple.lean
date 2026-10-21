/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelPacking

/-! # Packing prescribed rational perturbations and directions

The native parameter-coordinate equivalence writes a rational tuple into the
packet's flat coordinate blocks. Every prescribed epsilon, delta, and rational
direction is recovered exactly, while preserving the original encoded source.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term

noncomputable def tupleValue (bits : List Bool) (eps del : ℚ)
    (v : TubeSource.Coordinate bits → ℚ) : TubeParameter.Parameter bits → ℚ
  | .inl i => v i
  | .inr none => 0
  | .inr (some false) => eps
  | .inr (some true) => del

noncomputable def tuple (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ) (i : ℕ) : ℚ :=
  if hi : i < TubeParameter.parameterCount bits then
    tupleValue bits eps del v ((TubeParameter.parameterEquiv bits).symm ⟨i, hi⟩) else 0

theorem tuple_parameterIndex (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ)
    (p : TubeParameter.Parameter bits) :
    tuple bits eps del v (TubeParameter.parameterEquiv bits p).val = tupleValue bits eps del v p := by
  simp only [tuple, (TubeParameter.parameterEquiv bits p).isLt, dite_true, Fin.eta, Equiv.symm_apply_apply]

theorem parameters_of_tuple (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ)
    (c : List Bool) (hc : pairFst c = bits)
    (hr : ∀ i, i < TubeParameter.parameterCount bits → rationalValue c i = tuple bits eps del v i) :
    epsilon c = eps ∧ delta c = del ∧
      ∀ i : TubeSource.Coordinate bits, rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val = v i := by
  have hp (p : TubeParameter.Parameter bits) : rationalValue c (TubeParameter.parameterEquiv bits p).val =
      tupleValue bits eps del v p :=
    (hr _ (TubeParameter.parameterEquiv bits p).isLt).trans (tuple_parameterIndex bits eps del v p)
  refine ⟨?_, ?_, fun i => hp (.inl i)⟩
  · have he : epsilon c = rationalValue c (TubeParameter.parameterEquiv bits (.inr (some false))).val := by
      unfold epsilon alphaIndex
      rw [hc]
      rfl
    exact he.trans (hp (.inr (some false)))
  · have he : delta c = rationalValue c (TubeParameter.parameterEquiv bits (.inr (some true))).val := by
      unfold delta alphaIndex
      rw [hc]
      rfl
    exact he.trans (hp (.inr (some true)))

theorem exists_packet_parameters (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ) :
    ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
      ∀ i : TubeSource.Coordinate bits, rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val = v i := by
  obtain ⟨c, hc, hr⟩ := exists_packet bits (tuple bits eps del v)
  exact ⟨c, hc, parameters_of_tuple bits eps del v c hc hr⟩

theorem rationalWidth_tuple_le (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ)
    (B : ℕ) (hB : 1 ≤ B) (he : rationalBits eps ≤ B) (hd : rationalBits del ≤ B)
    (hv : ∀ i, rationalBits (v i) ≤ B) : rationalWidth bits (tuple bits eps del v) ≤ B := by
  apply rationalWidth_le
  intro i hi
  rw [tuple, dite_eq_left hi]
  rcases (TubeParameter.parameterEquiv bits).symm ⟨i, hi⟩ with j | p
  · exact hv j
  · rcases p with _ | b
    · simpa only [tupleValue, rationalBits_zero] using hB
    · cases b
      · exact he
      · exact hd

theorem exists_packet_parameters_bounded (bits : List Bool) (eps del : ℚ) (v : TubeSource.Coordinate bits → ℚ)
    (B : ℕ) (hB : 1 ≤ B) (he : rationalBits eps ≤ B) (hd : rationalBits del ≤ B)
    (hv : ∀ i, rationalBits (v i) ≤ B) :
    ∃ c : List Bool, pairFst c = bits ∧ epsilon c = eps ∧ delta c = del ∧
      (∀ i : TubeSource.Coordinate bits, rationalValue c (pointEquiv (TubeIndexed.arity bits) i).val = v i) ∧
      c.length ≤ 2 * bits.length + (5 * TubeParameter.parameterCount bits + 2) * B + 8 := by
  let q := tuple bits eps del v
  let c := rationalPack bits (rationalWidth bits q) q
  have hc : pairFst c = bits := by simp only [c, rationalPack, source_pack]
  have hr (i : ℕ) (hi : i < TubeParameter.parameterCount bits) : rationalValue c i = q i :=
    rationalValue_pack_width bits q i hi
  obtain ⟨hce, hcd, hcv⟩ := parameters_of_tuple bits eps del v c hc hr
  refine ⟨c, hc, hce, hcd, hcv, ?_⟩
  rw [length_rationalPack]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (rationalWidth_tuple_le bits eps del v B hB he hd hv)) _) _

end LeanCanny.ETR.TubeLevelPacket
