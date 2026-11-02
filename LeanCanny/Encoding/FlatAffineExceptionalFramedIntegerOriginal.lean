/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerPrelude
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
public import LeanCanny.Algebra.IntegralMixedIntegerFamilyOriginalSource
public import LeanCanny.Algebra.IntegralMixedFramedProducerDispatcher
/-! # Native integer leaves for the actual changing-source initial bank

The initial instructions contain the original finite-bank integer polynomials.
Later instructions keep their own spatial sources and are syntactically
noninteger. Exact degree and coefficient access are derived from the existing
original bank source; neither is assumed for an interpreted retained prefix.
The input projection, width, room and native header representation remain
explicit frontend obligations. No equality of different-width samplers is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerOriginal
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open FlatAffineExceptionalFramedIntegerPrelude (plan)
open FlatAffineExceptionalIntegerProducer (sourceQuery)
open scoped Classical

private noncomputable def integerPolynomial {n B : ℕ} (c : Instruction n B) : Polynomial ℤ :=
  match c.command with
  | .integer p _ _ => p
  | _ => Polynomial.X

private theorem polynomial_instruction (P : Parameters) (D : Plan P) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P D key=
      integerPolynomial (IntegralMixedFramedHistoryFamilyBits.instruction P D key) := by
  unfold IntegralMixedFramedIntegerBits.polynomial integerPolynomial
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

theorem polynomial_source (P : Parameters) (base : Plan P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0) (key : List Bool) :
    IntegralMixedFramedIntegerBits.polynomial P (plan P base F C h input later hW hroom) key=
      (FlatAffineExceptionalIntegerSource.source F C h).polynomial (sourceQuery P F input key) := by
  let b := IntegralMixedFramedHistoryFamilyBits.prefixLength P key
  let u := input (pairFst key)
  by_cases hb : b<births F u
  · have HC : IntegralMixedFramedHistoryScript.chronological
        ((plan P base F C h input later hW hroom).rules (pairFst key)) b=
        some (FlatAffineExceptionalFramedIntegerPrelude.command (base.initialSource (pairFst key))
          (P.width (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.initial P base (pairFst key)).critical_cap
          F C h u (hW (pairFst key)) (FlatAffineExceptionalIntegerCommands.index F u b hb)) :=
      FlatAffineExceptionalFramedIntegerPrelude.chronological_append _ _ _ F C h u _ (later (pairFst key)) b hb
    rw [polynomial_instruction]
    unfold IntegralMixedFramedHistoryFamilyBits.instruction
    rw [HC]
    change finitePolynomial F C h u (FlatAffineExceptionalIntegerCommands.index F u b hb)=_
    simp only [sourceQuery, show IntegralMixedFullHistoryFamilyBits.prefixLength P key<births F (input (pairFst key)) from hb,
      ite_true,FlatAffineExceptionalIntegerSource.source,FlatAffineExceptionalIntegerSource.padded,
      pairFst_pair,pairSnd_pair,show Nat.fromBitsLE [true]=1 from rfl,Nat.one_ne_zero,ite_false]
    rfl
  · have HM (c : Instruction (P.ambient (pairFst key)) (P.width (pairFst key)))
        (hc : IntegralMixedFramedHistoryScript.chronological
          ((plan P base F C h input later hW hroom).rules (pairFst key)) b=some c) :
        c∈later (pairFst key) := by
      change ((later (pairFst key)++FlatAffineExceptionalFramedIntegerPrelude.commands _ _ _ F C h u
        (hW (pairFst key))).reverse)[b]?=some c at hc
      rw [List.reverse_append,List.getElem?_append_right (by
        rw [List.length_reverse,FlatAffineExceptionalFramedIntegerPrelude.length_commands]
        exact Nat.le_of_not_gt hb)] at hc
      exact List.mem_reverse.mp (List.mem_of_getElem? hc)
    have HX : IntegralMixedFramedIntegerBits.polynomial P (plan P base F C h input later hW hroom) key=Polynomial.X := by
      rw [polynomial_instruction]
      unfold IntegralMixedFramedHistoryFamilyBits.instruction
      cases hc : IntegralMixedFramedHistoryScript.chronological
          ((plan P base F C h input later hW hroom).rules (pairFst key)) b with
      | none => rfl
      | some c =>
        have HN := hno _ c (HM c hc)
        rcases c with ⟨Q,hcap,cmd⟩
        cases cmd with
        | integer p hp hd => exact False.elim (HN rfl)
        | critical => rfl
        | cut => rfl
    rw [HX]
    simp only [sourceQuery,show ¬IntegralMixedFullHistoryFamilyBits.prefixLength P key<births F (input (pairFst key)) from hb,
      ite_false,FlatAffineExceptionalIntegerSource.source,FlatAffineExceptionalIntegerSource.padded,
      pairFst_pair,show Nat.fromBitsLE ([] : List Bool)=0 from rfl,ite_true]

theorem original (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0) :
    IntegralMixedIntegerFamilyBits.Original P
      (IntegralMixedFramedIntegerBits.polynomial P (plan P base F C h input later hW hroom)) :=
  IntegralMixedIntegerFamilyBits.original_of_source P a _ (FlatAffineExceptionalIntegerSource.source F C h)
    (FlatAffineExceptionalIntegerSource.access hF C h hh) (sourceQuery P F input)
    (FlatAffineExceptionalIntegerProducer.sourceQuery_FP P a hF input hi)
    (polynomial_source P base F C h input later hW hroom hno)

end LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerOriginal
