/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedScanPSPACE
public import LeanCanny.Computation.SpaceFunctionComposition
public import LeanCanny.Encoding.BinarySubFP

/-! # Finding a bounded witness with arbitrary polynomial-space tests

The retained natural is zero when no witness has been found, and otherwise one
plus the latest successful index. Both the loop count and the witness are binary.
Child decision procedures need no time bound.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedChoice
open Turing.MultiTapeTM
open LeanCanny.Encoding
open scoped Classical

noncomputable def search (L : Language) (c : List Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if pair c (BinaryNatCode.encode k) ∈ L then k + 1 else search L c k

theorem search_le (L : Language) (c : List Bool) (n : ℕ) : search L c n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [search]; split_ifs <;> omega

theorem search_spec (L : Language) (c : List Bool) (n : ℕ) :
    (search L c n = 0 ∧ ∀ k < n, pair c (BinaryNatCode.encode k) ∉ L) ∨
      (0 < search L c n ∧ search L c n ≤ n ∧
        pair c (BinaryNatCode.encode (search L c n - 1)) ∈ L) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, by omega⟩
  | succ n ih =>
    by_cases h : pair c (BinaryNatCode.encode n) ∈ L
    · rw [search, ite_eq_left h]
      exact Or.inr ⟨by omega, le_rfl, by simpa only [Nat.add_sub_cancel] using h⟩
    · rw [search, ite_eq_right h]
      rcases ih with ⟨hz, hn⟩ | ⟨hp, hb, hm⟩
      · exact Or.inl ⟨hz, fun k hk => by
          by_cases he : k = n
          · simpa only [he] using h
          · exact hn k (by omega)⟩
      · exact Or.inr ⟨hp, by omega, hm⟩

theorem witness (L : Language) (c : List Bool) (n : ℕ)
    (hex : ∃ k < n, pair c (BinaryNatCode.encode k) ∈ L) :
    search L c n - 1 < n ∧ pair c (BinaryNatCode.encode (search L c n - 1)) ∈ L := by
  rcases search_spec L c n with ⟨_, hn⟩ | ⟨hp, hb, hm⟩
  · obtain ⟨k, hk, hm⟩ := hex
    exact False.elim (hn k hk hm)
  · exact ⟨by omega, hm⟩

theorem computable {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) :
    ComputableTidilyInPolySpace (fun c => search L c (Nat.fromBitsLE (bound c))) encBits encNat := by
  let child := fun p : List Bool × ℕ × ℕ =>
    if pair p.1 (BinaryNatCode.encode p.2.1) ∈ L then p.2.1 + 1 else p.2.2
  have hc := ComputableTidilyInPolyTime.fst encBits (encPair encNat encNat)
  have hr := ComputableTidilyInPolyTime.snd encBits (encPair encNat encNat)
  have hquery := pair_computable hc (natBits_computable.comp hr.fst')
  have hi := ComputableTidilyInPolySpace.of_polyTime hr.fst'
  have hs := TidyBoundedFold.of_linear
    (ComputableTidilyInSpace.natSucc.weaken ComputableTidilyInSpace.linear_succ)
  have hchild : ComputableTidilyInPolySpace child
      (TidyBoundedFold.encPacket encBits encNat) encNat := by
    have h := (D.computable.comp (ComputableTidilyInPolySpace.of_polyTime hquery)).ite
      (hs.comp hi) (ComputableTidilyInPolySpace.of_polyTime hr.snd')
    exact h.congr fun p => by
      dsimp +instances only [child, Function.comp_apply, BinaryNatCode.encode]
      by_cases hp : pair p.1 p.2.1.bits ∈ L <;> simp only [hp, decide_true, decide_false, Bool.false_eq_true,
        ite_true, ite_false]
  have hfold (c : List Bool) (k : ℕ) :
      TidyBoundedFold.fold child (fun _ => 0) c k = search L c k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [TidyBoundedFold.fold, child, search, ih]
  have hn := fromBitsLE_computable.comp (FP.computable hb)
  have h := TidyBoundedFold.evaluator hchild hn
    (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const 0))
    hn.polyBounded_length (fun c k hk => by
      rw [hfold]
      exact ComputableTidilyInO.length_encNat_mono ((search_le L c k).trans hk))
  exact h.congr fun c => hfold c _

theorem evaluator {L : Language} (D : SpaceDecider L)
    (bound : List Bool → List Bool) (hb : bound ∈ FP) :
    SpaceFunction (fun c => BinaryNatCode.encode (search L c (Nat.fromBitsLE (bound c)) - 1)) := by
  have h := (ComputableTidilyInPolySpace.of_polyTime natBits_computable).comp (computable D bound hb)
  have E : SpaceFunction (fun c => BinaryNatCode.encode (search L c (Nat.fromBitsLE (bound c)))) :=
    ⟨h.congr fun _ => rfl⟩
  have hf := mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  have R := E.postcompose (fun z => BinaryNat.sub (pair z (BinaryNatCode.encode 1))) hf
  refine R.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Computation.BoundedChoice
