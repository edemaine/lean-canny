/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordControls
public import LeanCanny.Algebra.BoundedRegularFramedPermuted
/-! # Causal original-record arithmetic under a saved-source permutation

The native inverse permutation reads original metadata at the full saved key.
Affine bodies and current-bank-Q slopes keep their existing charged recursion;
no expanded renamed LOW or integer power is serialized.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)

noncomputable def currentQPermutedControls (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (e : BoundedRegularFramedPermutedBits.Permutation R)
    (snapshot : BoundedRegularFramedPermutedBits.Snapshot P (plan P S hn hd hcap N T hz hT hroom) R e)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls P (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) where
  scalar := scalarControls P S hn hd hcap N hq T hz hT hroom hW a hN
    (BoundedRegularFramedPermutedBits.leading P a (plan P S hn hd hcap N T hz hT hroom)
      (data P S hn hd hcap N hq T hz hT hroom hW) R hR e snapshot)
  critical := BoundedRegularFramedPermutedBits.controls P a (plan P S hn hd hcap N T hz hT hroom)
    (data P S hn hd hcap N hq T hz hT hroom hW)
    (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT))
    (tables_native P S hn hd hcap N hq T hz hT a hN) (tables_represent P S hn hd hcap N hq T hz hT hroom hW)
    R hR scope e snapshot
  normalization := {
    tables:=IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)
    native:=tables_native P S hn hd hcap N hq T hz hT a hN
    represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW
    nodes:=L
    factor:=F
    seed:=C
    nodes_native:=hL
    factor_native:=hF
    seed_native:=hC }
  producer := {
    tables:=IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap N hq T hz hT)
    native:=tables_native P S hn hd hcap N hq T hz hT a hN
    represents:=tables_represent P S hn hd hcap N hq T hz hT hroom hW
    integer:=integerOriginal P S hn hd hcap N T hz hT hroom a hA hN }

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
