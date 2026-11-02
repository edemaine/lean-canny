/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerSource
/-! # Initial-bank integer producers agree with their actual original source

The constructor writes every initial integer command from the actual bank
polynomial. Later commands are syntactically critical or normalized cuts.
Width and room remain explicit planning bounds on the complete history.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open scoped Classical

noncomputable def data (P : Parameters) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1) :
    IntegralMixedFullHistoryFamilyBits.Data P :=
  { base with
    rules root := later root ++ FlatAffineExceptionalIntegerCommands.commands (base.spatial root) (P.width root) F C h (input root) (hW root)
    room root := by rw [List.length_append, FlatAffineExceptionalIntegerCommands.length_commands]; exact hroom root }

def sourceQuery (P : Parameters) (F : Inputs) (input : List Bool → List Bool) (key : List Bool) : List Bool :=
  if IntegralMixedFullHistoryFamilyBits.prefixLength P key < births F (input (pairFst key)) then
    pair [true] (pair (input (pairFst key)) (BinaryNatCode.encode
      (births F (input (pairFst key)) - 1 - IntegralMixedFullHistoryFamilyBits.prefixLength P key)))
  else pair [] []

theorem sourceQuery_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (input : List Bool → List Bool) (hi : input ∈ FP) : sourceQuery P F input ∈ FP := by
  have HU := mem_FP_comp pairFst_mem_FP hi
  have HN : BinaryFn (fun key => births F (input (pairFst key))) :=
    (BinaryFn.ofUnary (FlatAffineExceptionalBankSource.births_unary hF)).comp HU
  have HB : BinaryFn (IntegralMixedFullHistoryFamilyBits.prefixLength P) :=
    BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)
  exact (HB.lt HN).ite_mem_FP
    (mem_FP_pair (constFn_mem_FP [true]) (mem_FP_pair HU ((HN.sub (BinaryFn.const 1)).sub HB).bits_mem_FP))
    (constFn_mem_FP (pair [] []))

theorem polynomial_source (P : Parameters) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1)
    (hno : ∀ root c, c ∈ later root → c.context ≠ 0) (key : List Bool) :
    IntegralMixedIntegerProducerBits.polynomial P (data P base F C h input later hW hroom) key =
      (FlatAffineExceptionalIntegerSource.source F C h).polynomial (sourceQuery P F input key) := by
  let b := IntegralMixedFullHistoryFamilyBits.prefixLength P key
  let u := input (pairFst key)
  by_cases hb : b < births F u
  · have HC : IntegralMixedFullHistoryFamilyBits.creating P (data P base F C h input later hW hroom) key =
        some (FlatAffineExceptionalIntegerCommands.command (base.spatial (pairFst key)) (P.width (pairFst key)) F C h u
          (hW (pairFst key)) (FlatAffineExceptionalIntegerCommands.index F u b hb)) :=
      FlatAffineExceptionalIntegerCommands.chronological_append _ _ F C h u _ (later (pairFst key)) b hb
    unfold IntegralMixedIntegerProducerBits.polynomial
    rw [HC]
    change finitePolynomial F C h u (FlatAffineExceptionalIntegerCommands.index F u b hb) = _
    simp only [sourceQuery, show IntegralMixedFullHistoryFamilyBits.prefixLength P key < births F (input (pairFst key)) from hb,
      ite_true, FlatAffineExceptionalIntegerSource.source, FlatAffineExceptionalIntegerSource.padded,
      pairFst_pair, pairSnd_pair, show Nat.fromBitsLE [true] = 1 from rfl, Nat.one_ne_zero, ite_false]
    rfl
  · have HM (c : Command (base.spatial (pairFst key)) (P.width (pairFst key)))
        (hc : IntegralMixedFullHistoryFamilyBits.creating P (data P base F C h input later hW hroom) key = some c) :
        c ∈ later (pairFst key) := by
      change ((later (pairFst key) ++ FlatAffineExceptionalIntegerCommands.commands _ _ F C h u (hW (pairFst key))).reverse)[b]? = some c at hc
      rw [List.reverse_append, List.getElem?_append_right (by
        rw [List.length_reverse, FlatAffineExceptionalIntegerCommands.length_commands]; exact Nat.le_of_not_gt hb)] at hc
      exact List.mem_reverse.mp (List.mem_of_getElem? hc)
    have HX : IntegralMixedIntegerProducerBits.polynomial P (data P base F C h input later hW hroom) key = Polynomial.X := by
      unfold IntegralMixedIntegerProducerBits.polynomial
      cases hc : IntegralMixedFullHistoryFamilyBits.creating P (data P base F C h input later hW hroom) key with
      | none => rfl
      | some c =>
        cases c with
        | integer p hp hd => exact False.elim (hno _ _ (HM _ hc) rfl)
        | critical => rfl
        | cut => rfl
    rw [HX]
    simp only [sourceQuery, show ¬IntegralMixedFullHistoryFamilyBits.prefixLength P key < births F (input (pairFst key)) from hb,
      ite_false, FlatAffineExceptionalIntegerSource.source, FlatAffineExceptionalIntegerSource.padded,
      pairFst_pair, show Nat.fromBitsLE ([] : List Bool) = 0 from rfl, ite_true]

end LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
