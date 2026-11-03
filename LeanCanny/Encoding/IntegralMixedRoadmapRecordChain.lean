/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedJointRecordBudgetNative
/-! # A finite record grammar for one recursive roadmap chain

Each level stores its optional endpoint births, one midpoint anchor, all
free-coordinate midpoint companions, one physical endpoint record and all
endpoint companions. Recursion freezes the next coordinate. The quadratic
record and byte bounds follow from these literal code arrays; no whole
recursive tree is serialized. Semantic and native recognition of these
records are separate from this syntax and its length bounds.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
open scoped Classical

abbrev Word (T : ℕ):={w : List Bool // w.length≤T}

inductive Endpoint (T cap : ℕ) where
  | retained (label : Fin cap)
  | fresh (code : Word T)

def Endpoint.codes {T cap : ℕ} : Endpoint T cap→List (Word T)
  | .retained _=>[]
  | .fresh code=>[code]

theorem Endpoint.codes_length_le {T cap : ℕ} (e : Endpoint T cap) : e.codes.length≤1:=by
  cases e <;> simp only [Endpoint.codes,List.length_nil,List.length_singleton] <;> omega

structure Level (n k T cap : ℕ) where
  left : Endpoint T cap
  right : Endpoint T cap
  anchor : Word T
  midpoint : Fin (n+1-(k+1))→Word T
  endpoint : Word T
  companions : Fin (n+1-(k+1))→Word T

def Level.codes {n k T cap : ℕ} (L : Level n k T cap) : List (Word T) :=
  L.left.codes++L.right.codes++[L.anchor]++List.ofFn L.midpoint++[L.endpoint]++List.ofFn L.companions

theorem Level.codes_length {n k T cap : ℕ} (L : Level n k T cap) :
    L.codes.length=L.left.codes.length+L.right.codes.length+2+2*(n+1-(k+1)) :=by
  simp only [Level.codes,List.length_append,List.length_singleton,List.length_ofFn]
  omega

theorem Level.codes_length_le {n k T cap : ℕ} (L : Level n k T cap) :
    L.codes.length≤4+2*(n+1-(k+1)) :=by
  rw [L.codes_length]
  have HL:=L.left.codes_length_le
  have HR:=L.right.codes_length_le
  omega

inductive Chain (n T cap : ℕ) : ℕ→Type where
  | stop (k : ℕ) : Chain n T cap k
  | descend (k : ℕ) (hk : k<n+1) (level : Level n k T cap)
      (tail : Chain n T cap (k+1)) : Chain n T cap k

def Chain.codes {n T cap : ℕ} : {k : ℕ}→Chain n T cap k→List (Word T)
  | _,.stop _=>[]
  | _,.descend _ _ level tail=>level.codes++tail.codes

def Chain.depth {n T cap : ℕ} : {k : ℕ}→Chain n T cap k→ℕ
  | _,.stop _=>0
  | _,.descend _ _ _ tail=>tail.depth+1

theorem Chain.depth_le {n T cap k : ℕ} (C : Chain n T cap k) : C.depth≤n+1-k :=by
  induction C with
  | stop k=>exact Nat.zero_le _
  | descend k hk level tail ih=>
    change tail.depth+1≤_
    omega

theorem Chain.codes_length_le {n T cap k : ℕ} (C : Chain n T cap k) :
    C.codes.length≤(n+1-k)*(n+1-k+3) :=by
  induction C with
  | stop k=>exact Nat.zero_le _
  | descend k hk level tail ih=>
    change (level.codes++tail.codes).length≤_
    rw [List.length_append]
    have HB:=level.codes_length_le
    have HE : n+1-k=(n+1-(k+1))+1:=by omega
    rw [HE]
    nlinarith

structure Records (n T cap : ℕ) where
  seed : Fin (n+2)→Word T
  chain : Chain n T cap 0

def Records.codes {n T cap : ℕ} (R : Records n T cap) : List (Word T) :=List.ofFn R.seed++R.chain.codes

def recordBound (n : ℕ):=n+2+(n+1)*(n+4)

theorem Records.codes_length_le {n T cap : ℕ} (R : Records n T cap) : R.codes.length≤recordBound n :=by
  have HC:=R.chain.codes_length_le
  simpa only [Records.codes,List.length_append,List.length_ofFn,Nat.sub_zero,recordBound] using
    Nat.add_le_add_left HC (n+2)

def Records.word {n T cap : ℕ} (R : Records n T cap) : List Bool:=WordList.encode (R.codes.map Subtype.val)

def byteBound (n T : ℕ):=(2*T+2)*recordBound n

theorem Records.word_length_le {n T cap : ℕ} (R : Records n T cap) : R.word.length≤byteBound n T :=by
  have HB:=WordList.length_le (R.codes.map Subtype.val) T (by
    intro w hw
    obtain ⟨code,_,rfl⟩:=List.mem_map.mp hw
    exact code.property)
  exact HB.trans (by
    rw [List.length_map]
    exact Nat.mul_le_mul_left _ R.codes_length_le)

theorem recordBound_unary {n : List Bool→ℕ} (hn : UnaryFn n) : UnaryFn (fun q=>recordBound (n q)) :=
  (hn.add (UnaryFn.const 2)).add ((hn.add (UnaryFn.const 1)).mul (hn.add (UnaryFn.const 4)))

theorem byteBound_unary {n T : List Bool→ℕ} (hn : UnaryFn n) (hT : UnaryFn T) :
    UnaryFn (fun q=>byteBound (n q) (T q)) :=
  (((UnaryFn.const 2).mul hT).add (UnaryFn.const 2)).mul (recordBound_unary hn)

end LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
