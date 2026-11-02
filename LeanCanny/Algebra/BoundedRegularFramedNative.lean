/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BoundedRegularFramedOriginal
public import LeanCanny.Algebra.IntegralMixedFramedAffineScalarControls
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSyntax
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
/-! # Seven arithmetic routines from original regular sources and affine rules

Source and rule snapshots are literal syntax identities. Integer instructions,
including padded defaults, must be X. Native original costs supply every leaf;
the final space theorem retains only the explicit original script/budget bounds.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Original (P : Parameters) (D : Plan P) where
  dimension : List Bool → ℕ
  term : List Bool → ETR.Term
  radius : List Bool → ℕ
  dimension_native : UnaryFn dimension
  term_native : (fun key => (term key).toData.toBits)∈FP
  radius_native : BinaryFn radius
  scope : ∀ key,(term key).arity≤dimension key
  snapshot : BoundedRegularFramedOriginalBits.Snapshot P D (BoundedRegularLowCoefficient.readers dimension term radius)
  integerX : ∀ key,IntegralMixedFramedIntegerBits.polynomial P D key=Polynomial.X

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D)
    (tables : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H tables)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalScalarRecipe.Layout F) (hL : FlatAffineExceptionalScalarRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool)
    (hp : (fun q => [pd q])∈FP) (hv : (fun q => [vd q])∈FP)
    (hs : IntegralMixedFramedAffineScalarBits.Snapshot P D H L C pd vd)
    (nodes factor seed : List Bool → ℕ) (hn : BinaryFn nodes) (hf : BinaryFn factor) (hc : BinaryFn seed) :
    IntegralMixedFramedNativeBits.Controls P D H where
  scalar := IntegralMixedFramedAffineScalarBits.controls P a D H hF L hL C pd vd hp hv hs tables ht hr
    (BoundedRegularFramedOriginalBits.leading P a D H
      (BoundedRegularLowCoefficient.readers s.dimension s.term s.radius)
      (BoundedRegularLowCoefficient.readers_native s.dimension_native s.term_native s.radius_native) s.snapshot)
  critical := BoundedRegularFramedOriginalBits.original_controls P a D H tables ht hr
    s.dimension s.radius s.term s.dimension_native s.term_native s.radius_native s.scope s.snapshot
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
  producer := IntegralMixedFramedIntegerSyntaxBits.controls P a D H tables ht hr
    (fun _ => (ETR.Term.var 0).toData.toBits) (constFn_mem_FP _) (fun key => by
      rw [s.integerX key]
      simp only [ETR.IntegerUnivariateTermSource.polynomial,ETR.TermView.term_toBits,ETR.Term.eval])

theorem model_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : Original P D)
    (tables : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access tables)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H tables)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalScalarRecipe.Layout F) (hL : FlatAffineExceptionalScalarRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool)
    (hp : (fun q => [pd q])∈FP) (hv : (fun q => [vd q])∈FP)
    (hs : IntegralMixedFramedAffineScalarBits.Snapshot P D H L C pd vd)
    (nodes factor seed : List Bool → ℕ) (hn : BinaryFn nodes) (hf : BinaryFn factor) (hc : BinaryFn seed)
    (hb : IntegralMixedFramedNativeBits.Bounds P D H
      (controls P a D H s tables ht hr hF L hL C pd vd hp hv hs nodes factor seed hn hf hc)) :
    SpaceFunction (IntegralMixedFramedNativeBits.machine P a D H
      (controls P a D H s tables ht hr hF L hL C pd vd hp hv hs nodes factor seed hn hf hc)).model :=
  IntegralMixedFramedNativeBits.model_space P a D H _ hb
end LeanCanny.Algebra.BoundedRegularFramedNativeBits
