/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionActual
/-! # Creating companion matrices depend on the actual root and prefix

The actual creating instruction and retained older run are independent of
auxiliary key context. This transport uses literal framed sources and never
reinterprets earlier commands under the current spatial source.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

structure PrefixKey (P : Parameters) where
  root : List Bool
  birth : ℕ
  bounded : birth≤P.cap root+1

theorem PrefixKey.ext {P : Parameters} (x y : PrefixKey P)
    (hr : x.root=y.root) (hb : x.birth=y.birth) : x=y := by
  cases x
  cases y
  cases hr
  cases hb
  rfl

def profile (P : Parameters) (key : List Bool) : PrefixKey P :=
  ⟨pairFst key,prefixLength P key,min_le_right _ _⟩

noncomputable def atPrefix (P : Parameters) (D : Plan P) (k : PrefixKey P) :
    PaddedIntegralGeneratorSource.Source := by
  let cs := paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D k.root) (D.rules k.root) k.birth
  let I := (chronological (D.rules k.root) k.birth).getD
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D k.root)
  have hcs : cs.length≤P.cap k.root+1 := by
    dsimp only [cs]
    rw [paddedPast_length]
    exact k.bounded
  let x := reframe (run (IntegralMixedFramedHistoryFamilyBits.initial P D k.root) cs
    (hcs.trans (Nat.le_succ _))) I.source I.source_cap
  exact {
    arity _ := cs.length
    width _ := P.width k.root
    carrier _ := x.sampler.scalarPrefix.carrier
    ring _ := x.sampler.scalarPrefix.ring
    nontrivial _ := x.sampler.scalarPrefix.nontrivial
    basis _ := x.sampler.scalarPrefix.basis
    polynomial _ := IntegralMixedFullHistoryScript.polynomial x hcs I.command
    degree _ := IntegralMixedFullHistoryScript.degree x hcs I.command }

theorem source_matrix_atPrefix (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    HEq ((source P D H).matrix key) ((atPrefix P D (profile P key)).matrix []) := by
  rfl

private theorem dependent_congr {α : Sort u} {β : α → Sort v} {x y : α}
    (h : x=y) (f : (a : α) → β a) : HEq (f x) (f y) := by
  cases h
  rfl

theorem source_matrix_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (x y : List Bool) (hr : pairFst x=pairFst y) (hb : prefixLength P x=prefixLength P y) :
    HEq ((source P D H).matrix x) ((source P D H).matrix y) := by
  have HK : profile P x=profile P y := PrefixKey.ext _ _ hr hb
  have HS := congrArg (atPrefix P D) HK
  exact (source_matrix_atPrefix P D H x).trans
    ((dependent_congr HS (fun S => S.matrix [])).trans (source_matrix_atPrefix P D H y).symm)

theorem source_matrix_keyAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key context : List Bool) :
    HEq ((source P D H).matrix (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key) (prefixLength P key) context))
      ((source P D H).matrix key) :=
  source_matrix_congr P D H _ key (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (min_le_right _ _))

end LeanCanny.Algebra.IntegralMixedFramedCompanionBits
