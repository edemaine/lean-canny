/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerHeaders
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRules
public import LeanCanny.Algebra.BoundedRegularFramedOriginal
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
/-! # A native current-Q factory for original regular-source integer preludes

All polynomial costs come from the original integer Source and regular LOW
syntax. The represented zero/unit fallbacks supply scalar cells literally.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
  (count : List Bool → ℕ) (hc : UnaryFn count)
  (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,count root+2≤P.cap root+1)
  (hn : ∀root,0<P.ambient root) (hSW : ∀root,(P.degree root).size≤P.sourceWidth root)
  (R : BoundedFullWriter.Readers) (hR : R.PolyTime)

local notation "D" => plan P Q hdegree hcap S count hz hd hroom
local notation "J" => data P Q hdegree hcap S count hz hd hroom hn hSW
local notation "T" => tables P count
local notation "HT" => tables_native P a hc
local notation "HR" => tables_represents P Q hdegree hcap S count hz hd hroom hn hSW

noncomputable def currentQControls
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (snapshot : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (nodes factor seed : List Bool → ℕ) (hL : BinaryFn nodes) (hF : BinaryFn factor) (hC : BinaryFn seed) :
    IntegralMixedFramedCurrentQNativeBits.Controls P D J where
  scalar := IntegralMixedFramedCurrentQIndexedBits.controls P a D J
    (originalRules P Q hdegree hcap S count hz hd hroom hn hSW) T HT HR
    (BoundedRegularFramedOriginalBits.leading P a D J R hR snapshot)
  critical := BoundedRegularFramedOriginalBits.controls P a D J T HT HR R hR scope snapshot
  normalization := {
    tables:=T
    native:=HT
    represents:=HR
    nodes:=nodes
    factor:=factor
    seed:=seed
    nodes_native:=hL
    factor_native:=hF
    seed_native:=hC }
  producer := {
    tables:=T
    native:=HT
    represents:=HR
    integer:=original P a Q hdegree hcap S hS count hc hz hd hroom }

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
