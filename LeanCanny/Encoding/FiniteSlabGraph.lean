/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ImplicitGraphPSPACE
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Fixed-width records and native dispatch for a finite slab graph

A vertex consists of a fixed-width binary slab number followed by a local
vertex word. Out-of-range slab numbers are invalid. Edges use the local graph
within one slab and the endpoint attachment query between neighboring slabs.
All other pairs are rejected before any recursive query is needed.
-/

@[expose] public section
namespace LeanCanny.Encoding.FiniteSlabGraph
open LeanCanny.Computation Turing.MultiTapeTM

def tag (s : ℕ) (u : List Bool) : ℕ := Nat.fromBitsLE (u.take s)
def payload (s : ℕ) (u : List Bool) : List Bool := u.drop s
def encode (s i : ℕ) (u : List Bool) : List Bool := ImplicitGraph.word s i ++ u

@[simp] theorem length_encode (s i : ℕ) (u : List Bool) :
    (encode s i u).length = s + u.length := by simp [encode]

@[simp] theorem payload_encode (s i : ℕ) (u : List Bool) :
    payload s (encode s i u) = u := by simp [payload, encode]

theorem tag_encode (s i : ℕ) (u : List Bool) (hi : i < 2 ^ s) :
    tag s (encode s i u) = i := by
  have h := FixedWidthNatVector.decode_block 1 s (fun _ => i) 0 (by decide) hi
  have htake : (FixedWidthNatVector.encode 1 s (fun _ => i)).take s =
      FixedWidthNatVector.encode 1 s (fun _ => i) := by
    apply List.take_of_length_le
    simp
  rw [Nat.zero_mul, List.drop_zero, htake] at h
  simpa [tag, encode, ImplicitGraph.word] using h

theorem encode_injective {s i j : ℕ} {u v : List Bool}
    (hi : i < 2 ^ s) (hj : j < 2 ^ s) (h : encode s i u = encode s j v) :
    i = j ∧ u = v := by
  have ht := congrArg (tag s) h
  rw [tag_encode s i u hi, tag_encode s j v hj] at ht
  have hp := congrArg (payload s) h
  simp only [payload_encode] at hp
  exact ⟨ht, hp⟩

def valid (count s : ℕ) (localValid : ℕ → List Bool → Bool) (u : List Bool) : Bool :=
  if tag s u < count then localValid (tag s u) (payload s u) else false

def edge (count s : ℕ) (localEdge touch : ℕ → List Bool → List Bool → Bool)
    (u v : List Bool) : Bool :=
  if tag s u < count then
    if tag s v < count then
      if tag s u = tag s v then localEdge (tag s u) (payload s u) (payload s v)
      else if tag s u + 1 = tag s v then touch (tag s u) (payload s u) (payload s v)
      else if tag s v + 1 = tag s u then touch (tag s v) (payload s v) (payload s u)
      else false
    else false
  else false

theorem tag_computable {α : Type} {eA : α ↪ List Bool}
    {s : α → ℕ} {u : α → List Bool}
    (hs : ComputableTidilyInPolyTime s eA encUnary)
    (hu : ComputableTidilyInPolyTime u eA encBits) :
    ComputableTidilyInPolyTime (fun c => tag (s c) (u c)) eA encNat :=
  fromBitsLE_computable.comp (ComputableTidilyInPolyTime.bitsTakeWithInput hu hs)

theorem payload_computable {α : Type} {eA : α ↪ List Bool}
    {s : α → ℕ} {u : α → List Bool}
    (hs : ComputableTidilyInPolyTime s eA encUnary)
    (hu : ComputableTidilyInPolyTime u eA encBits) :
    ComputableTidilyInPolyTime (fun c => payload (s c) (u c)) eA encBits :=
  ComputableTidilyInPolyTime.bitsDropWithInput hu hs

/-- A polynomial-space recursive label can be packed without assuming its
locator runs in polynomial time. Only the output tag width is unary. -/
theorem encode_computable {α : Type} {eA : α ↪ List Bool}
    {s i : α → ℕ} {u : α → List Bool}
    (hs : ComputableTidilyInPolyTime s eA encUnary)
    (hi : ComputableTidilyInPolySpace i eA encNat)
    (hu : ComputableTidilyInPolySpace u eA encBits) :
    ComputableTidilyInPolySpace (fun c => encode (s c) (i c) (u c)) eA encBits := by
  have hword := ImplicitGraph.word_computable
    (ComputableTidilyInPolyTime.fst encUnary encNat)
    (ComputableTidilyInPolyTime.snd encUnary encNat)
  have htag := (ComputableTidilyInPolySpace.of_polyTime hword).comp
    ((ComputableTidilyInPolySpace.of_polyTime hs).prod hi)
  have happend : ComputableTidilyInPolyTime
      (fun q : List Bool × List Bool => q.1 ++ q.2) (encPair encBits encBits) encBits :=
    (ComputableTidilyInPolyTime.fst encBits encBits).append
      (ComputableTidilyInPolyTime.snd encBits encBits) (fun _ => rfl)
  exact (ComputableTidilyInPolySpace.of_polyTime happend).comp (htag.prod hu)

theorem valid_computable {α : Type} {eA : α ↪ List Bool}
    {count s : α → ℕ} {localValid : α → ℕ → List Bool → Bool}
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableTidilyInPolyTime s eA encUnary)
    (hv : ComputableTidilyInPolySpace
      (fun q : α × ℕ × List Bool => localValid q.1 q.2.1 q.2.2)
      (encPair eA (encPair encNat encBits)) encBool) :
    ComputableTidilyInPolySpace
      (fun q : α × List Bool => valid (count q.1) (s q.1) (localValid q.1) q.2)
      (encPair eA encBits) encBool := by
  have hc := ComputableTidilyInPolyTime.fst eA encBits
  have hu := ComputableTidilyInPolyTime.snd eA encBits
  have ht := tag_computable (hs.comp hc) hu
  have hp := payload_computable (hs.comp hc) hu
  have hg := ComputableTidilyInPolyTime.binary_lt' ht (hn.comp hc)
  have h := (ComputableTidilyInPolySpace.of_polyTime hg).ite
    (hv.comp (.of_polyTime (hc.prod (ht.prod hp))))
    (.of_polyTime (ComputableTidilyInPolyTime.const false))
  exact h.congr fun q => by simp [valid]

theorem edge_computable {α : Type} {eA : α ↪ List Bool}
    {count s : α → ℕ} {localEdge touch : α → ℕ → List Bool → List Bool → Bool}
    (hn : ComputableTidilyInPolyTime count eA encNat)
    (hs : ComputableTidilyInPolyTime s eA encUnary)
    (he : ComputableTidilyInPolySpace
      (fun q : α × ℕ × List Bool × List Bool => localEdge q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair eA (encPair encNat (encPair encBits encBits))) encBool)
    (htouch : ComputableTidilyInPolySpace
      (fun q : α × ℕ × List Bool × List Bool => touch q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair eA (encPair encNat (encPair encBits encBits))) encBool) :
    ComputableTidilyInPolySpace
      (fun q : α × List Bool × List Bool => edge (count q.1) (s q.1)
        (localEdge q.1) (touch q.1) q.2.1 q.2.2)
      (encPair eA (encPair encBits encBits)) encBool := by
  have hc := ComputableTidilyInPolyTime.fst eA (encPair encBits encBits)
  have hr := ComputableTidilyInPolyTime.snd eA (encPair encBits encBits)
  have ha := tag_computable (hs.comp hc) hr.fst'
  have hb := tag_computable (hs.comp hc) hr.snd'
  have hu := payload_computable (hs.comp hc) hr.fst'
  have hv := payload_computable (hs.comp hc) hr.snd'
  have hfalse := ComputableTidilyInPolySpace.of_polyTime
    (ComputableTidilyInPolyTime.const
      (encIn := encPair eA (encPair encBits encBits)) (encMid := encBool) false)
  have hlocal := he.comp (.of_polyTime (hc.prod (ha.prod (hu.prod hv))))
  have hleft := htouch.comp (.of_polyTime (hc.prod (ha.prod (hu.prod hv))))
  have hright := htouch.comp (.of_polyTime (hc.prod (hb.prod (hv.prod hu))))
  have hab := ComputableTidilyInPolyTime.decide_eq encNat |>.comp (ha.prod hb)
  have ha1 := ComputableTidilyInPolyTime.binary_add' ha (ComputableTidilyInPolyTime.const 1)
  have hb1 := ComputableTidilyInPolyTime.binary_add' hb (ComputableTidilyInPolyTime.const 1)
  have hab1 := ComputableTidilyInPolyTime.decide_eq encNat |>.comp (ha1.prod hb)
  have hba1 := ComputableTidilyInPolyTime.decide_eq encNat |>.comp (hb1.prod ha)
  have ga := ComputableTidilyInPolyTime.binary_lt' ha (hn.comp hc)
  have gb := ComputableTidilyInPolyTime.binary_lt' hb (hn.comp hc)
  have h := (ComputableTidilyInPolySpace.of_polyTime ga).ite
    ((ComputableTidilyInPolySpace.of_polyTime gb).ite
      ((ComputableTidilyInPolySpace.of_polyTime hab).ite hlocal
        ((ComputableTidilyInPolySpace.of_polyTime hab1).ite hleft
          ((ComputableTidilyInPolySpace.of_polyTime hba1).ite hright hfalse))) hfalse) hfalse
  exact h.congr fun q => by simp [edge]

end LeanCanny.Encoding.FiniteSlabGraph
