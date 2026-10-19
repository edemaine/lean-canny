/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.TreeFoldFP
public import Complexitylib.Mathlib.NatBits
public import Mathlib.Data.Fintype.EquivFin

/-!
# Polynomial-time languages recognized by finite-frame tree folds

Every finite frame type admits a positive fixed-width code. A fixed test on the
final singleton stack is a finite lookup. Combining it with the certified outer
bracket test yields a polynomial-time predicate on exactly the accepted trees.
The implementation of the frame algebra remains the caller's responsibility.
-/

@[expose] public section

namespace LeanCanny.Encoding.TreeFold
open Complexity
open Brackets

variable {σ : Type*}

theorem stackBits_injective (code : σ → List Bool) (width : ℕ) (hwidth : 0 < width)
    (hlen : ∀ s, (code s).length = width) (hinj : Function.Injective code) :
    Function.Injective (stackBits code) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons x xs =>
          have he := congrArg List.length h
          simp only [stackBits_nil, stackBits_cons, List.length_append, hlen, List.length_nil] at he
          omega
  | cons x xs ih =>
      intro b h
      cases b with
      | nil =>
          have he := congrArg List.length h
          simp only [stackBits_nil, stackBits_cons, List.length_append, hlen, List.length_nil] at he
          omega
      | cons y ys =>
          have he := List.append_inj h ((hlen x).trans (hlen y).symm)
          exact congrArg₂ List.cons (hinj he.1) (ih he.2)

theorem encode_injective (code : σ → List Bool) (width : ℕ) (hwidth : 0 < width)
    (hlen : ∀ s, (code s).length = width) (hinj : Function.Injective code) :
    Function.Injective (encode code) := by
  intro a b h
  cases a with
  | none => cases b <;> simp_all [encode]
  | some xs =>
      cases b with
      | none => simp [encode] at h
      | some ys =>
          exact congrArg some (stackBits_injective code width hwidth hlen hinj (List.cons.inj h).2)

def acceptState (test : σ → Bool) : Option (List σ) → Bool
  | some [s] => test s
  | _ => false

theorem acceptedWords_fppred (keys : List σ) (code : σ → List Bool) (test : σ → Bool) :
    FPPred (fun bits => ∃ s ∈ keys, test s = true ∧ bits = encode code (some [s])) := by
  induction keys with
  | nil => exact (FPPred.const False).of_iff (by intro bits; simp)
  | cons s keys ih =>
      refine (((FPPred.const (test s = true)).and
        (stringEq_fppred id_mem_FP (constFn_mem_FP (encode code (some [s]))))).or ih).of_iff
        (fun bits => ?_)
      simp only [List.mem_cons]
      aesop

theorem acceptRun_fppred_of_code (empty : σ) (combine : σ → σ → σ) (test : σ → Bool)
    (code : σ → List Bool) (width : ℕ) (hwidth : 0 < width)
    (hlen : ∀ s, (code s).length = width) (hinj : Function.Injective code)
    (keys : List σ) (hkeys : ∀ s, s ∈ keys) :
    FPPred (fun bits => acceptState test (run empty combine bits) = true) := by
  have hrun := runEncoded_mem_FP empty combine code width hwidth hlen hinj keys hkeys
  refine ((acceptedWords_fppred keys code test).comp hrun).of_iff fun bits => ?_
  constructor
  · rintro ⟨s, _, hs, he⟩
    have hstate := encode_injective code width hwidth hlen hinj he
    rw [hstate]
    exact hs
  · intro hs
    cases hr : run empty combine bits with
    | none => simp [hr, acceptState] at hs
    | some stack =>
        cases stack with
        | nil => simp [hr, acceptState] at hs
        | cons s rest =>
            cases rest with
            | nil => exact ⟨s, hkeys s, by simpa only [hr, acceptState] using hs, rfl⟩
            | cons x xs => simp [hr, acceptState] at hs

/-- Finite frames suffice; their concrete machine code is chosen inside the proof. -/
theorem acceptRun_fppred [Fintype σ] (empty : σ) (combine : σ → σ → σ) (test : σ → Bool) :
    FPPred (fun bits => acceptState test (run empty combine bits) = true) := by
  classical
  let code : σ → List Bool := fun s => false :: (Fintype.equivFin σ s).toBits
  let width := 1 + Fin.bitWidth (Fintype.card σ)
  have hwidth : 0 < width := by dsimp [width]; omega
  have hlen : ∀ s, (code s).length = width := by
    intro s
    simp [code, width, Nat.add_comm]
  have hinj : Function.Injective code := by
    intro a b h
    have he := (List.cons.inj h).2
    have hd := congrArg (Fin.fromBits? (Fintype.card σ)) he
    rw [Fin.fromBits?_toBits, Fin.fromBits?_toBits] at hd
    exact (Fintype.equivFin σ).injective (Option.some.inj hd)
  exact acceptRun_fppred_of_code empty combine test code width hwidth hlen hinj
    (Finset.univ.toList) (by intro s; simp)

/-- A finite tree algebra recognizes a polynomial-time language of complete serializations. -/
theorem treeLanguage_fppred [Fintype σ] (empty : σ) (combine : σ → σ → σ) (test : σ → Bool) :
    FPPred (fun bits => ∃ d : Data, bits = d.toBits ∧
      test (combine (foldData empty combine d) empty) = true) := by
  refine (treeCode_fppred.and (acceptRun_fppred empty combine test)).of_iff fun bits => ?_
  constructor
  · rintro ⟨htree, htest⟩
    obtain ⟨d, rfl⟩ := (treeCode_iff bits).mp htree
    exact ⟨d, rfl, by simpa only [run_toBits, acceptState] using htest⟩
  · rintro ⟨d, rfl, htest⟩
    exact ⟨treeCode_toBits d, by simpa only [run_toBits, acceptState] using htest⟩

end LeanCanny.Encoding.TreeFold
