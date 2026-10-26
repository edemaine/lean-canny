/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceReachability
public import LeanCanny.Computation.TidyBoundedFold
public import LeanCanny.Encoding.FixedWidthNatVectorFP

/-! # Polynomial-space implicit graphs

Vertices have a fixed, unary-computable bit width. Edges and vertex validity
may use polynomial space and arbitrary time. Reachability uses Savitch at
depth equal to the width; universal scans enumerate words with binary counters.
The graph is never materialized. Whole-graph connectivity ignores invalid
vertex words and accepts the empty graph.
-/

@[expose] public section

namespace LeanCanny.Computation.ImplicitGraph
open Turing.MultiTapeTM Cslib.Reachability Cslib.BitString
open scoped Classical

/-- Width-restricted edges, including both endpoint length checks. -/
def Step (edge : List Bool → List Bool → Bool) (w : ℕ) (u v : List Bool) : Prop :=
  u.length = w ∧ v.length = w ∧ edge u v = true

/-- Depth `w` suffices for arbitrary reachability on the `2^w` vertex words. -/
theorem savitch_iff_reachable {edge : List Bool → List Bool → Bool} {w : ℕ}
    {u v : List Bool} (hu : u.length = w) (hv : v.length = w) :
    savitch edge w w u v = true ↔ Relation.ReflTransGen (Step edge w) u v := by
  rw [savitch_iff hu hv]
  apply Iff.symm
  apply Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le
  have hsub : {x | Relation.ReflTransGen (Step edge w) u x} ⊆
      ((enumList w).toFinset : Set (List Bool)) := by
    intro x hx
    apply List.mem_toFinset.mpr
    apply mem_enumList.mpr
    induction hx with
    | refl => exact hu
    | tail _ he _ => exact he.2.1
  calc
    _ ≤ (((enumList w).toFinset : Set (List Bool))).encard := Set.encard_le_encard hsub
    _ = ((enumList w).toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ ((enumList w).length : ℕ∞) := by exact_mod_cast List.toFinset_card_le _
    _ = (2 ^ w : ℕ) := by rw [length_enumList]
    _ ≤ (2 ^ w : ℕ∞) + 1 := le_self_add

/-- The canonical width-`w` word for a counter value, truncating excess bits. -/
def word (w k : ℕ) : List Bool :=
  Encoding.FixedWidthNatVector.encode 1 w (fun _ => k)

@[simp] theorem length_word (w k : ℕ) : (word w k).length = w := by simp [word]

@[simp] theorem word_fromBitsLE (u : List Bool) : word u.length (Nat.fromBitsLE u) = u := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkw : k < u.length := hk'
    simp only [word, Encoding.FixedWidthNatVector.encode, List.getElem_ofFn,
      Nat.mod_eq_of_lt hkw, Encoding.BinaryNat.fromBitsLE_testBit]
    simp [hkw]

theorem word_computable {α : Type} {eA : α ↪ List Bool} {w k : α → ℕ}
    (hw : ComputableTidilyInPolyTime w eA encUnary)
    (hk : ComputableTidilyInPolyTime k eA encNat) :
    ComputableTidilyInPolyTime (fun x => word (w x) (k x)) eA encBits :=
  Encoding.FixedWidthNatVector.encode_of_coordinate (ComputableTidilyInPolyTime.const 1)
    hw ComputableTidilyInPolyTime.unary_to_binary
    (hk.comp (ComputableTidilyInPolyTime.fst eA encNat))

private def allBelow {α : Type} (test : α × ℕ → Bool) (c : α) : ℕ → Bool
  | 0 => true
  | k + 1 => allBelow test c k && test (c, k)

private theorem allBelow_correct {α : Type} (test : α × ℕ → Bool) (c : α) (n : ℕ) :
    allBelow test c n = true ↔ ∀ k < n, test (c, k) = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      by_cases he : k = n
      · simpa [he] using hn
      · exact h k (by omega)
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

/-- A typed binary-counted universal scan. No bound on the child's time is needed. -/
theorem forall_below_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {test : α × ℕ → Bool} {count : α → ℕ}
    (ht : ComputableTidilyInPolySpace test (encPair eA encNat) encBool)
    (hn : ComputableTidilyInPolyTime count eA encNat) :
    ComputableTidilyInPolySpace (fun c => decide (∀ k < count c, test (c, k) = true))
      eA encBool := by
  let child := fun p : α × ℕ × Bool => p.2.2 && test (p.1, p.2.1)
  have hp := ComputableTidilyInPolyTime.fst eA (encPair encNat encBool)
  have hr := ComputableTidilyInPolyTime.snd eA (encPair encNat encBool)
  have hq := hp.prod hr.fst'
  have hc : ComputableTidilyInPolySpace child (TidyBoundedFold.encPacket eA encBool)
      encBool := by
    have h := (ComputableTidilyInPolySpace.of_polyTime hr.snd').ite
      (ht.comp (.of_polyTime hq)) (.of_polyTime (ComputableTidilyInPolyTime.const false))
    exact h.congr fun p => by cases hb : p.2.2 <;> simp [child, hb]
  have h := TidyBoundedFold.evaluator_spec hc hn
    (.of_polyTime (ComputableTidilyInPolyTime.const true)) (allBelow test)
    (fun _ => rfl) (fun _ _ _ => rfl)
    (B := fun _ => 1) (PolyBounded.const 1) (fun _ _ _ => by simp)
  exact h.congr fun c => Bool.eq_iff_iff.mpr (by
    rw [decide_eq_true_eq, allBelow_correct])

/-- Quantify over every width-`w` word using polynomial space, with a unary
width and a polynomial-space predicate. This includes width zero. -/
theorem forall_words_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {test : α × List Bool → Bool} {width : α → ℕ}
    (ht : ComputableTidilyInPolySpace test (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableTidilyInPolySpace
      (fun c => decide (∀ u : List Bool, u.length = width c → test (c, u) = true))
      eA encBool := by
  have hp := ComputableTidilyInPolyTime.fst eA encNat
  have hk := ComputableTidilyInPolyTime.snd eA encNat
  have hword := word_computable (hw.comp hp) hk
  have h := forall_below_computable (ht.comp (.of_polyTime (hp.prod hword)))
    (ComputableTidilyInPolyTime.binary_two_pow.comp hw)
  refine h.congr fun c => Bool.eq_iff_iff.mpr ?_
  simp only [decide_eq_true_eq, Function.comp_apply]
  constructor
  · intro hall u hu
    have hlt : Nat.fromBitsLE u < 2 ^ width c := by
      simpa only [hu] using Nat.fromBitsLE_lt_pow_length u
    simpa only [← hu, word_fromBitsLE] using hall (Nat.fromBitsLE u) hlt
  · intro hall k _
    exact hall _ (length_word _ _)

def selectBelow {α : Type} (test : α × List Bool → Bool) (width : α → ℕ)
    (c : α) : ℕ → List Bool
  | 0 => word (width c) 0
  | k + 1 => if test (c, selectBelow test width c k) then
      selectBelow test width c k else word (width c) k

private theorem selectBelow_length {α : Type} (test : α × List Bool → Bool)
    (width : α → ℕ) (c : α) (n : ℕ) :
    (selectBelow test width c n).length = width c := by
  induction n with
  | zero => exact length_word _ _
  | succ n ih => simp only [selectBelow]; split <;> simp_all

private theorem selectBelow_correct {α : Type} (test : α × List Bool → Bool)
    (width : α → ℕ) (c : α) (n : ℕ) :
    ∀ k < n, test (c, word (width c) k) = true →
      test (c, selectBelow test width c n) = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro k hk ht
    simp only [selectBelow]
    split
    next h => exact h
    next h =>
      have he : k = n := by
        by_contra hne
        exact h (ih k (by omega) ht)
      simpa only [he] using ht

/-- Search every fixed-width word while retaining one candidate. If no word
passes, the returned word still has the specified width. -/
def findWord {α : Type} (test : α × List Bool → Bool) (width : α → ℕ) (c : α) : List Bool :=
  selectBelow test width c (2 ^ width c)

/-- Fixed-width search depends only on the width and tests at this input. -/
theorem findWord_congr {α β : Type} {test : α × List Bool → Bool}
    {test' : β × List Bool → Bool} {width : α → ℕ} {width' : β → ℕ}
    {c : α} {c' : β} (hw : width c = width' c')
    (ht : ∀ r, test (c, r) = test' (c', r)) :
    findWord test width c = findWord test' width' c' := by
  have hs (k) : selectBelow test width c k = selectBelow test' width' c' k := by
    induction k with
    | zero => simp only [selectBelow, hw]
    | succ k ih => simp only [selectBelow, ih, ht, hw]
  unfold findWord
  rw [hw]
  exact hs _

@[simp] theorem findWord_length {α : Type} (test : α × List Bool → Bool)
    (width : α → ℕ) (c : α) : (findWord test width c).length = width c :=
  selectBelow_length _ _ _ _

theorem findWord_correct {α : Type} {test : α × List Bool → Bool} {width : α → ℕ} {c : α}
    (h : ∃ u, u.length = width c ∧ test (c, u) = true) :
    test (c, findWord test width c) = true := by
  obtain ⟨u, hu, ht⟩ := h
  apply selectBelow_correct test width c (2 ^ width c) (Nat.fromBitsLE u)
  · simpa only [hu] using Nat.fromBitsLE_lt_pow_length u
  · simpa only [← hu, word_fromBitsLE] using ht

/-- Finding an endpoint piece needs only polynomial space, even when its
membership routine runs for arbitrarily long. -/
theorem findWord_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {test : α × List Bool → Bool} {width : α → ℕ}
    (ht : ComputableTidilyInPolySpace test (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableTidilyInPolySpace (findWord test width) eA encBits := by
  have hp := ComputableTidilyInPolyTime.fst eA (encPair encNat encBits)
  have hr := ComputableTidilyInPolyTime.snd eA (encPair encNat encBits)
  have htest := ht.comp (.of_polyTime (hp.prod hr.snd'))
  have hword := word_computable (hw.comp hp) hr.fst'
  have hstep := htest.ite (.of_polyTime hr.snd') (.of_polyTime hword)
  have hi := word_computable hw (ComputableTidilyInPolyTime.const 0)
  exact TidyBoundedFold.evaluator_spec hstep
    (ComputableTidilyInPolyTime.binary_two_pow.comp hw) (.of_polyTime hi)
    (selectBelow test width) (fun _ => rfl) (fun _ _ _ => rfl)
    (B := width) (by
      simpa only [encUnary_apply, List.length_replicate] using hw.polyBounded_length)
    (fun c _ _ => by simp only [encBits_apply, selectBelow_length]; rfl)

/-- Reject edges incident to invalid vertex records, including intermediates. -/
def guard (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool)
    (u v : List Bool) : Bool := valid u && valid v && edge u v

theorem guard_computable {α : Type} {eA : α ↪ List Bool}
    {edge : α → List Bool → List Bool → Bool} {valid : α → List Bool → Bool}
    (he : ComputableTidilyInPolySpace
      (fun p : α × List Bool × List Bool => edge p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valid p.1 p.2)
      (encPair eA encBits) encBool) :
    ComputableTidilyInPolySpace
      (fun p : α × List Bool × List Bool => guard (edge p.1) (valid p.1) p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool := by
  have hp := ComputableTidilyInPolyTime.fst eA (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd eA (encPair encBits encBits)
  have hu := hv.comp (.of_polyTime (hp.prod hr.fst'))
  have hv' := hv.comp (.of_polyTime (hp.prod hr.snd'))
  have hf : ComputableTidilyInPolySpace (fun _ : α × List Bool × List Bool => false)
      (encPair eA (encPair encBits encBits)) encBool :=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  have h := hu.ite (hv'.ite he hf) hf
  exact h.congr fun p => by
    cases h₁ : valid p.1 p.2.1 <;> cases h₂ : valid p.1 p.2.2 <;> simp [guard, h₁, h₂]

/-- Reachability requires valid endpoints and valid intermediate vertices. -/
def Reachable (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool)
    (w : ℕ) (u v : List Bool) : Prop :=
  valid u = true ∧ valid v = true ∧
    Relation.ReflTransGen (Step (guard edge valid) w) u v

/-- Point-to-point reachability with a unary width and polynomial-space endpoint readers. -/
theorem reachable_computable {α : Type} {eA : α ↪ List Bool}
    {edge : α → List Bool → List Bool → Bool} {valid : α → List Bool → Bool}
    {width : α → ℕ} {src dst : α → List Bool}
    (he : ComputableTidilyInPolySpace
      (fun p : α × List Bool × List Bool => edge p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valid p.1 p.2)
      (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary)
    (hs : ComputableTidilyInPolySpace src eA encBits)
    (hd : ComputableTidilyInPolySpace dst eA encBits)
    (hsrc : ∀ c, (src c).length = width c) (hdst : ∀ c, (dst c).length = width c) :
    ComputableTidilyInPolySpace
      (fun c => decide (Reachable (edge c) (valid c) (width c) (src c) (dst c))) eA encBool := by
  have hi : ComputableTidilyInPolySpace (id : α → α) eA eA := .id'
  have hw' := ComputableTidilyInPolySpace.of_polyTime hw
  have hargs := hi.prod (hw'.prod (hw'.prod (hs.prod hd)))
  have hr := savitch_computable_polySpace (edge := fun c => guard (edge c) (valid c))
    (guard_computable he hv) hargs hsrc hdst
  have hU := hv.comp (hi.prod hs)
  have hV := hv.comp (hi.prod hd)
  have hf : ComputableTidilyInPolySpace (fun _ : α => false) eA encBool :=
    .of_polyTime (ComputableTidilyInPolyTime.const false)
  have h := hU.ite (hV.ite hr hf) hf
  refine h.congr fun c => Bool.eq_iff_iff.mpr ?_
  rw [decide_eq_true_eq]
  simp only [Reachable, id_eq]
  cases hu : valid c (src c) <;> cases hv : valid c (dst c) <;>
    simp_all [savitch_iff_reachable (hsrc c) (hdst c)]

/-- All valid vertices reach one another through valid vertices. Empty graphs
are connected by the pairwise convention. -/
def Connected (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool) (w : ℕ) : Prop :=
  ∀ u : List Bool, u.length = w → ∀ v : List Bool, v.length = w →
    valid u = true → valid v = true → Relation.ReflTransGen (Step (guard edge valid) w) u v

/-- Whole-graph connectivity is polynomial-space computable. The hypothesis
on `edge` permits a polynomial-space algebraic adjacency routine. -/
theorem connected_computable {α : Type} [Inhabited α] {eA : α ↪ List Bool}
    {edge : α → List Bool → List Bool → Bool} {valid : α → List Bool → Bool}
    {width : α → ℕ}
    (he : ComputableTidilyInPolySpace
      (fun p : α × List Bool × List Bool => edge p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valid p.1 p.2)
      (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableTidilyInPolySpace
      (fun c => decide (Connected (edge c) (valid c) (width c))) eA encBool := by
  -- Enumerate normalized counter words, so every Savitch call has the right width.
  let packet := encPair eA (encPair encNat encNat)
  have hp := ComputableTidilyInPolyTime.fst eA (encPair encNat encNat)
  have hi := (ComputableTidilyInPolyTime.snd eA (encPair encNat encNat)).fst'
  have hj := (ComputableTidilyInPolyTime.snd eA (encPair encNat encNat)).snd'
  have hW := hw.comp hp
  have hu := word_computable hW hi
  have hv' := word_computable hW hj
  have hargs := hp.prod (hW.prod (hW.prod (hu.prod hv')))
  have hs := savitch_computable_polySpace (edge := fun c => guard (edge c) (valid c))
    (guard_computable he hv) (.of_polyTime hargs)
    (fun p => length_word _ _) (fun p => length_word _ _)
  have hU := hv.comp (.of_polyTime (hp.prod hu))
  have hV := hv.comp (.of_polyTime (hp.prod hv'))
  let test := fun p : α × ℕ × ℕ =>
    if valid p.1 (word (width p.1) p.2.1) && valid p.1 (word (width p.1) p.2.2) then
      savitch (guard (edge p.1) (valid p.1)) (width p.1) (width p.1)
        (word (width p.1) p.2.1) (word (width p.1) p.2.2)
    else true
  have ht : ComputableTidilyInPolySpace test packet encBool := by
    have h := hU.ite (hV.ite hs (.of_polyTime (ComputableTidilyInPolyTime.const true)))
      (.of_polyTime (ComputableTidilyInPolyTime.const true))
    exact h.congr fun p => by
      cases h₁ : valid p.1 (word (width p.1) p.2.1) <;>
        cases h₂ : valid p.1 (word (width p.1) p.2.2) <;> simp [test, h₁, h₂]
  have hcount := ComputableTidilyInPolyTime.binary_two_pow.comp hw
  -- The inner fold uses the input together with the outer counter.
  have hswap : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (encPair (encPair eA encNat) encNat) packet :=
    (ComputableTidilyInPolyTime.fst (encPair eA encNat) encNat).fst'.prod
      ((ComputableTidilyInPolyTime.fst (encPair eA encNat) encNat).snd'.prod
        (ComputableTidilyInPolyTime.snd (encPair eA encNat) encNat))
  have hinner := forall_below_computable (ht.comp (.of_polyTime hswap))
    (hcount.comp (ComputableTidilyInPolyTime.fst eA encNat))
  have houter := forall_below_computable hinner hcount
  refine houter.congr fun c => Bool.eq_iff_iff.mpr ?_
  simp only [decide_eq_true_eq, Function.comp_apply]
  constructor
  · intro hall u hu v hv hu' hv'
    have hi : Nat.fromBitsLE u < 2 ^ width c := by simpa [hu] using Nat.fromBitsLE_lt_pow_length u
    have hj : Nat.fromBitsLE v < 2 ^ width c := by simpa [hv] using Nat.fromBitsLE_lt_pow_length v
    have H := hall (Nat.fromBitsLE u) hi (Nat.fromBitsLE v) hj
    have huu : word (width c) (Nat.fromBitsLE u) = u := by rw [← hu, word_fromBitsLE]
    have hvv : word (width c) (Nat.fromBitsLE v) = v := by rw [← hv, word_fromBitsLE]
    simp only [test, huu, hvv, hu', hv', Bool.and_self, ↓reduceIte] at H
    exact (savitch_iff_reachable hu hv).mp H
  · intro hall i hi j hj
    dsimp only [test]
    split
    next hvalid =>
      simp only [Bool.and_eq_true] at hvalid
      obtain ⟨hu, hv⟩ := hvalid
      exact (savitch_iff_reachable (length_word _ _) (length_word _ _)).mpr
        (hall _ (length_word _ _) _ (length_word _ _) hu hv)
    next => rfl

end LeanCanny.Computation.ImplicitGraph
