/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutCoefficientPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
/-! # A full relative factor is indexed by its literal selected old prefix

The profile retains the whole selected rule and kind, not just the recorded
normalization degree. Its source contains the full relative polynomial.
This makes honest root/modulus transport independent of field decoders.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    PaddedIntegralGeneratorSource.Source where
  arity := (IntegralMixedFramedHistoryFamilyBits.family P D H).birth
  width := (IntegralMixedFramedHistoryFamilyBits.family P D H).width
  carrier key := ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.carrier
  ring key := ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.ring
  nontrivial key := ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.nontrivial
  basis key := ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.basis
  polynomial key := IntegralMixedRelativeCuts.factor ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) ((IntegralMixedFramedHistoryFamilyBits.family P D H).kind key)
  degree key := IntegralMixedExceptionalBounds.auxiliaryCap ((IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key+1)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).spatial key).degree

structure Profile (P : Parameters) (D : Plan P) where
  root : List Bool
  birth : ℕ
  bounded : birth≤P.cap root+1
  selection : IntegralMixedFullHistoryFamilyBits.Selection
    (IntegralMixedFramedRootPullback.instructionAt P D root birth).source

theorem Profile.ext (P : Parameters) (D : Plan P) (x y : Profile P D)
    (hr : x.root=y.root) (hb : x.birth=y.birth) (hs : HEq x.selection y.selection) : x=y := by
  cases x
  cases y
  cases hr
  cases hb
  have HS:=eq_of_heq hs
  cases HS
  rfl

noncomputable def profile (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Profile P D := ⟨pairFst key,prefixLength P key,min_le_right _ _,IntegralMixedFramedHistoryFamilyBits.selection P D H key⟩

noncomputable def atProfile (P : Parameters) (D : Plan P) (k : Profile P D) :
    PaddedIntegralGeneratorSource.Source := by
  let cs := paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D k.root) (D.rules k.root) k.birth
  let I := IntegralMixedFramedRootPullback.instructionAt P D k.root k.birth
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
    polynomial _ := IntegralMixedRelativeCuts.factor x hcs k.selection.rule k.selection.kind
    degree _ := IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient k.root+1) I.source.degree }

theorem coefficient_atProfile (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (k : ℕ) :
    HEq ((source P D H).coefficient key k) ((atProfile P D (profile P D H key)).coefficient [] k) := by
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCutSourceBits
