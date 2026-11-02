/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.SmallConnectedChains
public import Mathlib.Data.List.Chain
/-! # Constructed finite subdivisions through small connected neighborhoods

The subdivision has at least two edges, retains both prescribed endpoints and
every vertex lies in the original connected set. These are finite data obtained
from connectedness and local connectedness; no pre-existing path is an input.
-/
@[expose] public section
namespace LeanCanny.Geometry.ConnectedChainSubdivision
open Set SmallConnectedChains
open scoped Classical
variable {X : Type*} [PseudoMetricSpace X]

structure Subdivision (C U : Set X) (ε : ℝ) (x y : C) where
  steps : ℕ
  two_le : 2≤steps
  node : Fin (steps+1) → C
  first : node 0=x
  last : node (Fin.last steps)=y
  adjacent : ∀ i : Fin steps, Small U ε (node i.castSucc).val (node i.succ).val

variable [LocallyConnectedSpace X]
theorem exists_subdivision (C U : Set X) (hC : IsPreconnected C) (hU : IsOpen U) (hCU : C⊆U)
    (ε : ℝ) (hε : 0 < ε) (x y : C) : Nonempty (Subdivision C U ε x y) := by
  let R := fun a b : C => Small U ε a.val b.val
  obtain ⟨l,HL,HE⟩ := List.exists_isChain_cons_of_relationReflTransGen (chain C U hC hU hCU ε hε x y)
  have HX : R x x := mem_of_mem_nhds (small_nhds U hU ε hε x.val (hCU x.property))
  let L := x::x::x::l
  let k := l.length+2
  have Hlen : L.length=k+1 := by simp only [L,k,List.length_cons]
  have Hne : L≠[] := List.cons_ne_nil _ _
  have HL' : L.IsChain R := List.IsChain.cons_cons HX (List.IsChain.cons_cons HX HL)
  have HE' : L.getLast Hne=y := by simpa only [L,List.getLast_cons_cons] using HE
  let p : Fin (k+1) → C := fun i => L[i.val]'(by rw [Hlen]; exact i.isLt)
  refine ⟨⟨k,by dsimp [k]; omega,p,?_,?_,?_⟩⟩
  · simp only [p,L,Fin.val_zero,List.getElem_cons_zero]
  · have H : L.getLast Hne=L[k]'(by rw [Hlen]; omega) := by
      simpa only [Hlen,Nat.add_sub_cancel] using List.getLast_eq_getElem Hne
    exact H.symm.trans HE'
  · intro i
    exact (List.isChain_iff_getElem.mp HL') i.val (by rw [Hlen]; exact Nat.succ_lt_succ i.isLt)
end LeanCanny.Geometry.ConnectedChainSubdivision
