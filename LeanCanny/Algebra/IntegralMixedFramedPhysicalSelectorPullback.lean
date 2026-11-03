/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowSelector
public import LeanCanny.Algebra.IntegralMixedFramedRootPullback
/-! # Original physical row selectors survive a caller-root pullback -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalSelectorPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalRowSelector IntegralMixedFramedPhysicalIndex
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedRootPullback (parameters plan key)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedCommandHeaderBits.lookup

theorem span_same (P : Parameters) (T : Tables) (s t : List Bool) (hr : pairFst s=pairFst t) (b : ℕ) :
    span P T (pair s (List.replicate b true))=span P T (pair t (List.replicate b true)) := by
  simp only [span,pairFst_pair,pairSnd_pair,List.length_replicate,hr]

theorem prefix_same (P : Parameters) (T : Tables) (s t : List Bool) (hr : pairFst s=pairFst t) (b : ℕ) :
    prefixArity P T (pair s (List.replicate b true))=prefixArity P T (pair t (List.replicate b true)) := by
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
  apply Finset.sum_congr rfl
  intro j _
  exact span_same P T s t hr j

theorem birth_same (P : Parameters) (T : Tables) (s t w : List Bool) (hr : pairFst s=pairFst t)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P s=IntegralMixedFramedHistoryFamilyBits.prefixLength P t) :
    rowBirth P T (pair s w)=rowBirth P T (pair t w) :=by
  simp only [rowBirth,pairFst_pair,pairSnd_pair]
  rw [hb]
  congr 1
  apply Finset.filter_congr
  intro b _
  rw [prefix_same P T s t hr (b+1)]

theorem full_same (P : Parameters) (T : Tables) (s t w : List Bool) (hr : pairFst s=pairFst t)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P s=IntegralMixedFramedHistoryFamilyBits.prefixLength P t) :
    fullArity P T (pair s w)=fullArity P T (pair t w) :=by
  simp only [fullArity,pairFst_pair]
  rw [hb]
  exact prefix_same P T s t hr _

theorem local_same (P : Parameters) (T : Tables) (s t w : List Bool) (hr : pairFst s=pairFst t)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P s=IntegralMixedFramedHistoryFamilyBits.prefixLength P t) :
    localRow P T (pair s w)=localRow P T (pair t w) :=by
  simp only [localRow,pairSnd_pair,full_same P T s t w hr hb,birthPacket,pairFst_pair,birth_same P T s t w hr hb]
  rw [prefix_same P T s t hr]

theorem scalar_same (P : Parameters) (T : Tables) (s t w : List Bool) (hr : pairFst s=pairFst t)
    (hb : IntegralMixedFramedHistoryFamilyBits.prefixLength P s=IntegralMixedFramedHistoryFamilyBits.prefixLength P t) :
    IsScalar P T (pair s w)↔IsScalar P T (pair t w) :=by
  simp only [IsScalar,pairSnd_pair,full_same P T s t w hr hb,local_same P T s t w hr hb,
    birthPacket,pairFst_pair,birth_same P T s t w hr hb]
  rw [span_same P T s t hr]

variable (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (project : List Bool→List Bool) (extra : List Bool→ℕ)
  (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra))
  (T U : Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
  (hU : IntegralMixedFramedHeaderBits.Represents (parameters P project extra) (plan P D project extra) Jnew U)

include hT hU in
theorem words_pull (r : List Bool) : U.commands r=T.commands (project r) :=by
  rw [hT.commands,hU.commands]
  rfl

include hT hU in
theorem span_pull (s : List Bool) (b : ℕ) :
    span (parameters P project extra) U (pair s (List.replicate b true))=
      span P T (pair (key project s) (List.replicate b true)) :=by
  simp only [span,pairFst_pair,pairSnd_pair,List.length_replicate,parameters,Function.comp_apply,
    IntegralMixedFramedRootPullback.key_root,words_pull P D J project extra Jnew T U hT hU]

include hT hU in
theorem prefix_pull (s : List Bool) (b : ℕ) :
    prefixArity (parameters P project extra) U (pair s (List.replicate b true))=
      prefixArity P T (pair (key project s) (List.replicate b true)) :=by
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
  apply Finset.sum_congr rfl
  intro j _
  exact span_pull P D J project extra Jnew T U hT hU s j

include hT hU in
theorem birth_pull (s w : List Bool) :
    rowBirth (parameters P project extra) U (pair s w)=rowBirth P T (pair (key project s) w) :=by
  have HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P (key project s)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters P project extra) s :=
    IntegralMixedFramedRootPullback.key_prefix P project extra s
  simp only [rowBirth,pairFst_pair,pairSnd_pair]
  rw [HB]
  congr 1
  apply Finset.filter_congr
  intro b _
  rw [prefix_pull P D J project extra Jnew T U hT hU s (b+1)]

include hT hU in
theorem full_pull (s w : List Bool) :
    fullArity (parameters P project extra) U (pair s w)=fullArity P T (pair (key project s) w) :=by
  have HB : IntegralMixedFramedHistoryFamilyBits.prefixLength P (key project s)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters P project extra) s :=
    IntegralMixedFramedRootPullback.key_prefix P project extra s
  simp only [fullArity,pairFst_pair]
  rw [HB]
  exact prefix_pull P D J project extra Jnew T U hT hU s _

include hT hU in
theorem local_pull (s w : List Bool) :
    localRow (parameters P project extra) U (pair s w)=localRow P T (pair (key project s) w) :=by
  simp only [localRow,pairSnd_pair,full_pull P D J project extra Jnew T U hT hU,
    birthPacket,pairFst_pair,birth_pull P D J project extra Jnew T U hT hU]
  rw [prefix_pull P D J project extra Jnew T U hT hU s]

include hT hU in
theorem scalar_pull (s w : List Bool) :
    IsScalar (parameters P project extra) U (pair s w)↔IsScalar P T (pair (key project s) w) :=by
  simp only [IsScalar,pairSnd_pair,full_pull P D J project extra Jnew T U hT hU,
    local_pull P D J project extra Jnew T U hT hU,birthPacket,pairFst_pair,
    birth_pull P D J project extra Jnew T U hT hU]
  rw [span_pull P D J project extra Jnew T U hT hU s]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalSelectorPullback
