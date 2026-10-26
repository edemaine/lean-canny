/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ImplicitGraphPSPACE

/-! # Native connectivity between marked vertices

Marks select the endpoints of the connectivity test. Traversal still uses
all valid vertices, including unmarked ones. Marked invalid endpoints are
rejected, while an empty marked set is accepted.
-/

@[expose] public section
namespace LeanCanny.Computation.ImplicitGraph
open Turing.MultiTapeTM Cslib.Reachability Cslib.BitString
open scoped Classical

def MarkedConnected (edge : List Bool → List Bool → Bool) (valid marked : List Bool → Bool) (w : ℕ) : Prop :=
  ∀ u : List Bool, u.length = w → ∀ v : List Bool, v.length = w →
    marked u = true → marked v = true → Reachable edge valid w u v

theorem marked_all_iff_connected (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool) (w : ℕ) :
    MarkedConnected edge valid valid w ↔ Connected edge valid w := by
  constructor
  · intro h u hu v hv hU hV
    exact (h u hu v hv hU hV).2.2
  · intro h u hu v hv hU hV
    exact ⟨hU, hV, h u hu v hv hU hV⟩

/-- An executable finite specification. The native cost proof below scans
with binary counters and does not store this list of all vertex words. -/
def markedConnected (edge : List Bool → List Bool → Bool) (valid marked : List Bool → Bool) (w : ℕ) : Bool :=
  (enumList w).all fun u => (enumList w).all fun v =>
    if marked u && marked v then valid u && valid v && savitch (guard edge valid) w w u v else true

theorem markedConnected_correct (edge : List Bool → List Bool → Bool) (valid marked : List Bool → Bool) (w : ℕ) :
    markedConnected edge valid marked w = true ↔ MarkedConnected edge valid marked w := by
  simp only [markedConnected, List.all_eq_true]
  constructor
  · intro h u hu v hv hmu hmv
    have H := h u (mem_enumList.mpr hu) v (mem_enumList.mpr hv)
    simp only [hmu, hmv, Bool.and_self, ↓reduceIte, Bool.and_eq_true] at H
    exact ⟨H.1.1, H.1.2, (savitch_iff_reachable hu hv).mp H.2⟩
  · intro h u hu v hv
    split
    next hm =>
      simp only [Bool.and_eq_true] at hm
      have hr := h u (mem_enumList.mp hu) v (mem_enumList.mp hv) hm.1 hm.2
      simpa only [hr.1, hr.2.1, Bool.true_and] using
        (savitch_iff_reachable (mem_enumList.mp hu) (mem_enumList.mp hv)).mpr hr.2.2
    next => rfl

theorem marked_connected_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {edge : α → List Bool → List Bool → Bool} {valid marked : α → List Bool → Bool} {width : α → ℕ}
    (he : ComputableTidilyInPolySpace (fun p : α × List Bool × List Bool => edge p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valid p.1 p.2) (encPair eA encBits) encBool)
    (hm : ComputableTidilyInPolySpace (fun p : α × List Bool => marked p.1 p.2) (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableTidilyInPolySpace (fun c => decide (MarkedConnected (edge c) (valid c) (marked c) (width c))) eA encBool := by
  let packet := encPair eA (encPair encNat encNat)
  have hp := ComputableTidilyInPolyTime.fst eA (encPair encNat encNat)
  have hi := (ComputableTidilyInPolyTime.snd eA (encPair encNat encNat)).fst'
  have hj := (ComputableTidilyInPolyTime.snd eA (encPair encNat encNat)).snd'
  have hW := hw.comp hp
  have hu := word_computable hW hi
  have hv' := word_computable hW hj
  have hargs := hp.prod (hW.prod (hW.prod (hu.prod hv')))
  have hs := savitch_computable_polySpace (edge := fun c => guard (edge c) (valid c))
    (guard_computable he hv) (.of_polyTime hargs) (fun p => length_word _ _) (fun p => length_word _ _)
  have hU := hv.comp (.of_polyTime (hp.prod hu))
  have hV := hv.comp (.of_polyTime (hp.prod hv'))
  have hMU := hm.comp (.of_polyTime (hp.prod hu))
  have hMV := hm.comp (.of_polyTime (hp.prod hv'))
  have hf : ComputableTidilyInPolySpace (fun _ : α × ℕ × ℕ => false) packet encBool :=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  have ht : ComputableTidilyInPolySpace (fun _ : α × ℕ × ℕ => true) packet encBool :=
    .of_polyTime (ComputableTidilyInPolyTime.const true)
  let test := fun p : α × ℕ × ℕ =>
    if marked p.1 (word (width p.1) p.2.1) && marked p.1 (word (width p.1) p.2.2) then
      valid p.1 (word (width p.1) p.2.1) && valid p.1 (word (width p.1) p.2.2) &&
        savitch (guard (edge p.1) (valid p.1)) (width p.1) (width p.1)
          (word (width p.1) p.2.1) (word (width p.1) p.2.2)
    else true
  have hc : ComputableTidilyInPolySpace test packet encBool := by
    have h := hMU.ite (hMV.ite (hU.ite (hV.ite hs hf) hf) ht) ht
    exact h.congr fun p => by
      cases hm₁ : marked p.1 (word (width p.1) p.2.1) <;>
        cases hm₂ : marked p.1 (word (width p.1) p.2.2) <;>
          cases hv₁ : valid p.1 (word (width p.1) p.2.1) <;>
            cases hv₂ : valid p.1 (word (width p.1) p.2.2) <;> simp [test, hm₁, hm₂, hv₁, hv₂]
  have hcount := ComputableTidilyInPolyTime.binary_two_pow.comp hw
  have hswap : ComputableTidilyInPolyTime (fun p : (α × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (encPair (encPair eA encNat) encNat) packet :=
    (ComputableTidilyInPolyTime.fst (encPair eA encNat) encNat).fst'.prod
      ((ComputableTidilyInPolyTime.fst (encPair eA encNat) encNat).snd'.prod
        (ComputableTidilyInPolyTime.snd (encPair eA encNat) encNat))
  have hinner := forall_below_computable (hc.comp (.of_polyTime hswap))
    (hcount.comp (ComputableTidilyInPolyTime.fst eA encNat))
  have houter := forall_below_computable hinner hcount
  refine houter.congr fun c => Bool.eq_iff_iff.mpr ?_
  simp only [decide_eq_true_eq, Function.comp_apply]
  constructor
  · intro hall u hu v hv hmu hmv
    have hi : Nat.fromBitsLE u < 2 ^ width c := by simpa [hu] using Nat.fromBitsLE_lt_pow_length u
    have hj : Nat.fromBitsLE v < 2 ^ width c := by simpa [hv] using Nat.fromBitsLE_lt_pow_length v
    have H := hall (Nat.fromBitsLE u) hi (Nat.fromBitsLE v) hj
    have huu : word (width c) (Nat.fromBitsLE u) = u := by rw [← hu, word_fromBitsLE]
    have hvv : word (width c) (Nat.fromBitsLE v) = v := by rw [← hv, word_fromBitsLE]
    simp only [test, huu, hvv, hmu, hmv, Bool.true_and, ↓reduceIte] at H
    simp only [Bool.and_eq_true] at H
    exact ⟨H.1.1, H.1.2, (savitch_iff_reachable hu hv).mp H.2⟩
  · intro hall i hi j hj
    dsimp only [test]
    split
    next hm' =>
      simp only [Bool.and_eq_true] at hm'
      have hr := hall _ (length_word _ _) _ (length_word _ _) hm'.1 hm'.2
      simpa only [hr.1, hr.2.1, Bool.true_and] using
        (savitch_iff_reachable (length_word _ _) (length_word _ _)).mpr hr.2.2
    next => rfl

theorem markedConnected_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {edge : α → List Bool → List Bool → Bool} {valid marked : α → List Bool → Bool} {width : α → ℕ}
    (he : ComputableTidilyInPolySpace (fun p : α × List Bool × List Bool => edge p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valid p.1 p.2) (encPair eA encBits) encBool)
    (hm : ComputableTidilyInPolySpace (fun p : α × List Bool => marked p.1 p.2) (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableTidilyInPolySpace (fun c => markedConnected (edge c) (valid c) (marked c) (width c)) eA encBool := by
  apply (marked_connected_computable he hv hm hw).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact (markedConnected_correct _ _ _ _).symm

end LeanCanny.Computation.ImplicitGraph
