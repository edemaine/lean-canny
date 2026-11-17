/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ModularArithmetic
public import LeanCanny.CountingHierarchy.DerivativeRootLabels
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Total bounded decoding of short derivative-sign labels -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

abbrev encRootLabelCode : List (ℕ × ℕ) ↪ List Bool := encList (encPair encNat encNat)

@[expose] def rootSignCode (k : ℕ) : SignType :=
  if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else -1

@[expose] def rootSignResidue (p k : ℕ) : ℕ :=
  if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else modularSub p 0 1

@[expose] def codedRootLabel (D N : ℕ) (hD : 0 < D) (data : List (ℕ × ℕ)) :
    List (Fin D × SignType) :=
  (data.take N).map (fun t => (⟨t.1 % D, Nat.mod_lt _ hD⟩, rootSignCode t.2))

@[expose] def codedRootLabelOrders (D N : ℕ) (data : List (ℕ × ℕ)) : List ℕ :=
  (data.take N).map (fun t => t.1 % D + 1)

@[expose] def codedRootLabelTarget (p : ℕ) (data : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  if i = 0 then 1 else rootSignResidue p ((data[i - 1]?.getD (0, 0)).2)

theorem codedRootLabel_length_le (D N : ℕ) (hD : 0 < D) (data : List (ℕ × ℕ)) :
    (codedRootLabel D N hD data).length ≤ N := by
  simp only [codedRootLabel, List.length_map, List.length_take]
  exact min_le_left _ _

theorem codedRootLabel_orders (D N : ℕ) (hD : 0 < D) (data : List (ℕ × ℕ)) :
    (codedRootLabel D N hD data).map (fun t => t.1.val + 1) = codedRootLabelOrders D N data := by
  simp only [codedRootLabel, codedRootLabelOrders, List.map_map]
  rfl

variable {α : Type} {enc : α ↪ List Bool}

theorem rootSignResidue_polyTime {p k : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    ComputableInPolyTime (fun w => rootSignResidue (p w) (k w)) enc encNat := by
  have hmod := ComputableInPolyTime.binary_mod.comp (hk.prod (ComputableInPolyTime.const 3))
  have hzero := ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 0)
  have hone := ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 1)
  have htail : ComputableInPolyTime
      (fun w => if k w % 3 = 1 then 1 else modularSub (p w) 0 1) enc encNat := by
    simpa only [decide_eq_true_eq, Function.comp_apply] using
      ComputableInPolyTime.ite' hone (.const 1) (modularSub_polyTime hp (.const 0) (.const 1))
  simpa only [rootSignResidue, decide_eq_true_eq, Function.comp_apply] using
    ComputableInPolyTime.ite' hzero (.const 0) htail

theorem codedRootLabelOrders_polyTime {D N : α → ℕ} {data : α → List (ℕ × ℕ)}
    (hD : ComputableInPolyTime D enc encNat) (hN : ComputableInPolyTime N enc encUnary)
    (hdata : ComputableInPolyTime data enc encRootLabelCode) :
    ComputableInPolyTime (fun w => codedRootLabelOrders (D w) (N w) (data w)) enc (encList encNat) := by
  have hprefix := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listTakeWithInput hdata.tidy hN.tidy)
  have hf := ComputableInPolyTime.fst enc (encPair encNat encNat)
  have hi : ComputableInPolyTime (fun q : α × (ℕ × ℕ) => q.2.1)
      (encPair enc (encPair encNat encNat)) encNat := by fun_prop
  have horder := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mod.comp (hi.prod (hD.comp hf))) (.const 1)
  simpa only [codedRootLabelOrders, Function.comp_apply] using
    ComputableInPolyTime.mapWithInput hprefix horder

theorem codedRootLabelTarget_polyTime {p i : α → ℕ} {data : α → List (ℕ × ℕ)}
    (hp : ComputableInPolyTime p enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode) :
    ComputableInPolyTime (fun w => codedRootLabelTarget (p w) (data w) (i w)) enc encNat := by
  have hentry : ComputableInPolyTime (fun w => ((data w)[i w - 1]?.getD (0, 0)))
      enc (encPair encNat encNat) := by
    simpa only [List.getD_eq_getElem?_getD] using
      ComputableInPolyTime.listGetD_binary (0, 0) hdata (ComputableInPolyTime.binary_sub' hi (.const 1))
  have hk := (ComputableInPolyTime.snd encNat encNat).comp hentry
  have htest := ComputableInPolyTime.decide_eq' hi (ComputableInPolyTime.const 0)
  simpa only [codedRootLabelTarget, decide_eq_true_eq, Function.comp_apply] using
    ComputableInPolyTime.ite' htest (.const 1) (rootSignResidue_polyTime hp hk)

end LeanCanny.CountingHierarchy
