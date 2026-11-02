/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerOriginal
public import LeanCanny.Algebra.IntegralMixedHeaderMetadata
/-! # Initial integer-bank headers require no integer-polynomial evaluation -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open IntegralMixedCommandHeaderBits
open scoped Classical

def prepend (w : List Bool) : List Bool := pair (encode zero) w
theorem prepend_FP : prepend ∈ FP := mem_FP_pair (constFn_mem_FP (encode zero)) id_mem_FP

theorem prepend_length (n : ℕ) (w : List Bool) :
    (prepend^[n] w).length = (2 * (encode zero).length + 2) * n + w.length := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.zero_add]
  | succ n ih =>
    rw [Function.iterate_succ_apply', prepend, pair_length, ih, Nat.mul_succ]
    omega

theorem prepend_encode (n : ℕ) (ws : List (List Bool)) :
    prepend^[n] (WordList.encode ws) = WordList.encode (List.replicate n (encode zero) ++ ws) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem prepend_native (count : List Bool → ℕ) (hc : UnaryFn count)
    (tail : List Bool → List Bool) (ht : tail ∈ FP) : (fun q => prepend^[count q] (tail q)) ∈ FP := by
  let K := 2 * (encode zero).length + 2
  have HB : UnaryFn (fun q => K * count q + (tail q).length) :=
    ((UnaryFn.const K).mul hc).add (UnaryFn.length ht)
  have E := iterate_mem_FP prepend_FP ht (hc.replicate_mem_FP false) (HB.replicate_mem_FP false) (by
    intro q n hn
    simp only [List.length_replicate] at hn ⊢
    rw [prepend_length]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left K hn) _)
  exact mem_FP_of_eq E (fun q => by simp only [List.length_replicate])

theorem bank_headerList {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) :
    ((FlatAffineExceptionalIntegerCommands.commands P B F C h u hB).reverse.map (fun c => encode (command c))) =
      List.replicate (births F u) (encode zero) := by
  simp only [FlatAffineExceptionalIntegerCommands.commands, List.map_reverse, List.map_ofFn, Function.comp_def,
    FlatAffineExceptionalIntegerCommands.command, command, List.ofFn_const, List.reverse_replicate]

theorem bank_headers {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) :
    words (FlatAffineExceptionalIntegerCommands.commands P B F C h u hB) =
      WordList.encode (List.replicate (births F u) (encode zero)) :=
  congrArg WordList.encode (bank_headerList P B F C h u hB)

theorem data_headers (P : Parameters) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1) (root : List Bool) :
    words ((FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom).rules root) =
      prepend^[births F (input root)] (words (later root)) := by
  unfold FlatAffineExceptionalIntegerProducer.data words
  rw [List.reverse_append, List.map_append, bank_headerList, prepend_encode]

theorem data_headers_FP (P : Parameters) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (input : List Bool → List Bool) (hi : input ∈ FP)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hlater : (fun root => words (later root)) ∈ FP)
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1) :
    (fun root => words ((FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom).rules root)) ∈ FP :=
  mem_FP_of_eq (prepend_native _ ((FlatAffineExceptionalBankSource.births_unary hF).comp hi) _ hlater)
    (fun root => (data_headers P base F C h input later hW hroom root).symm)

end LeanCanny.Encoding.FlatAffineExceptionalIntegerHeaders
