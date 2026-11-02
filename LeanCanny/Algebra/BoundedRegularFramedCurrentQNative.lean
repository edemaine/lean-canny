/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BoundedRegularFramedPermuted
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQScalarOriginal
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSyntax
/-! # Static regular-source native arithmetic with actual current-Q sweep slopes

Original syntax, native coordinate permutations and literal snapshots supply
all original leaves. Current bank denominators are reconstructed by charged
producer calls. Integer instructions, including defaults, are literally X.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularFramedCurrentQNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Original (P : Parameters) (D : Plan P) where
  readers : BoundedFullWriter.Readers
  native : readers.PolyTime
  scope : ∀ key,(ETR.TermView.term (readers.source key)).arity≤readers.dim key
  permutation : BoundedRegularFramedPermutedBits.Permutation readers
  source : BoundedRegularFramedPermutedBits.Snapshot P D readers permutation
  integerX : ∀ key,IntegralMixedFramedIntegerBits.polynomial P D key=Polynomial.X

noncomputable def Original.ofFrozen (P : Parameters) (D : Plan P)
    (n radius : List Bool → ℕ) (t : List Bool → ETR.Term)
    (hn : UnaryFn n) (ht : (fun key => (t key).toData.toBits)∈FP) (hR : BinaryFn radius)
    (ha : ∀ key,(t key).arity≤n key) (mask : List Bool → List Bool) (hm : mask∈FP)
    (hs : BoundedRegularFramedPermutedBits.Snapshot P D (BoundedRegularLowCoefficient.readers n t radius)
      (BoundedRegularFramedPermutedBits.frozen _ (BoundedRegularLowCoefficient.readers_native hn ht hR) mask hm))
    (hX : ∀ key,IntegralMixedFramedIntegerBits.polynomial P D key=Polynomial.X) : Original P D where
  readers := BoundedRegularLowCoefficient.readers n t radius
  native := BoundedRegularLowCoefficient.readers_native hn ht hR
  scope key := by simpa only [BoundedRegularLowCoefficient.readers,ETR.TermView.term_toBits] using ha key
  permutation := BoundedRegularFramedPermutedBits.frozen _ (BoundedRegularLowCoefficient.readers_native hn ht hR) mask hm
  source := hs
  integerX := hX

/-- Existing general-height/midpoint syntax writers discharge the original
body cost. The literal slope identity remains the charged current-Q mode. -/
noncomputable def rulesOfRecipe (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) {F : FlatAffineFullSourceTower.Inputs}
    (hF : F.Access) (L : FlatAffineExceptionalScalarRecipe.Layout F) (hL : FlatAffineExceptionalScalarRecipe.Access L)
    (pd vd : List Bool → Bool) (hp : (fun q => [pd q])∈FP) (hv : (fun q => [vd q])∈FP)
    (hphysical : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
      ((IntegralMixedFramedScalarCellsBits.physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).scales i=if pd q then 2 else 1)
    (hvirtual : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
      ((IntegralMixedFramedScalarCellsBits.virtualFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i=if vd q then 2 else 1)
    (haffine : ∀ q,IntegralMixedFramedScalarCellsBits.affine P D J q=FlatAffineExceptionalScalarRecipe.expression L q)
    (slope : IntegralMixedFramedCurrentQHeightBits.UnitSlope P D J) : IntegralMixedFramedCurrentQScalarBits.OriginalRules P D J where
  word := FlatAffineExceptionalScalarRecipe.word L
  word_space := FlatAffineExceptionalScalarRecipe.syntax_space hF L hL
  word_eq q := by rw [haffine q]; rfl
  physicalDouble := pd
  virtualDouble := vd
  physical_FP := hp
  virtual_FP := hv
  physicalScales := hphysical
  virtualScales := hvirtual
  slope := slope

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D)
    (tables : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J tables)
    (rules : IntegralMixedFramedCurrentQScalarBits.OriginalRules P D J)
    (nodes factor seed : List Bool → ℕ) (hn : BinaryFn nodes) (hf : BinaryFn factor) (hc : BinaryFn seed) :
    IntegralMixedFramedCurrentQNativeBits.Controls P D J where
  scalar := IntegralMixedFramedCurrentQScalarBits.Controls.ofOriginal P a D J tables ht hr
    (BoundedRegularFramedPermutedBits.leading P a D J s.readers s.native s.permutation s.source) rules
  critical := BoundedRegularFramedPermutedBits.controls P a D J tables ht hr
    s.readers s.native s.scope s.permutation s.source
  normalization := {
    tables := tables
    native := ht
    represents := hr
    nodes := nodes
    factor := factor
    seed := seed
    nodes_native := hn
    factor_native := hf
    seed_native := hc }
  producer := IntegralMixedFramedIntegerSyntaxBits.controls P a D J tables ht hr
    (fun _ => (ETR.Term.var 0).toData.toBits) (constFn_mem_FP _) (fun key => by
      rw [s.integerX key]
      simp only [ETR.IntegerUnivariateTermSource.polynomial,ETR.TermView.term_toBits,ETR.Term.eval])

theorem model_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D)
    (tables : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J tables)
    (rules : IntegralMixedFramedCurrentQScalarBits.OriginalRules P D J)
    (nodes factor seed : List Bool → ℕ) (hn : BinaryFn nodes) (hf : BinaryFn factor) (hc : BinaryFn seed)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J
      (controls P a D J s tables ht hr rules nodes factor seed hn hf hc)) :
    SpaceFunction (IntegralMixedFramedCurrentQNativeBits.machine P a D J
      (controls P a D J s tables ht hr rules nodes factor seed hn hf hc)).model :=
  IntegralMixedFramedCurrentQNativeBits.model_space P a D J _ hb
end LeanCanny.Algebra.BoundedRegularFramedCurrentQNativeBits
