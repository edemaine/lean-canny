/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalPrefix
/-! # The exact prelude boundary in the native causal record table

The prelude plan is rebuilt under P, never imported from a narrower legacy
integer sampler. The equality holds for every saved-key tail.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)

noncomputable def preludePlan : Plan P :=
  IntegralMixedSourceIntegerPrelude.plan P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (fun root=>by have H:=hroom root; omega)

local notation "D"=>plan P S hn hd hcap N T hz hT hroom
local notation "I"=>preludePlan P S hd hcap N T hz hT hroom

theorem prelude_commands_at (key : List Bool) (hb : prefixLength P key=N (pairFst key)) :
    commands P D key=(I).rules (pairFst key) :=
  IntegralMixedSourceIntegerPrelude.extended_commands_at P (fun root=>S root 0) (fun root=>hd root 0)
    hcap T N hz hT (later P S hn hd hcap N) (fun root=>by rw [later_length]; exact hroom root) key hb

theorem prelude_commands_key (root tail : List Bool) :
    commands P D (keyAt root (N root) tail)=(I).rules (pairFst (keyAt root (N root) tail)) :=
  IntegralMixedSourceIntegerPrelude.extended_commands_key P (fun root=>S root 0) (fun root=>hd root 0)
    hcap T N hz hT (later P S hn hd hcap N) (fun root=>by rw [later_length]; exact hroom root) root tail

theorem prelude_initial (root : List Bool) : initial P D root=initial P I root :=rfl

theorem prelude_length (root : List Bool) : ((I).rules root).length=N root :=
  IntegralMixedSourceIntegerPrelude.commands_length _ _ _ _ _ _ _ _

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
