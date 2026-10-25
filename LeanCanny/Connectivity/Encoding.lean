/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.Problem
public import LeanCanny.ETR.Encoding
public import LeanCanny.Computation.PolyTime

/-! # Canonical connectivity inputs

A tagged tree distinguishes point queries from whole-space queries. Dimension
is unary; polynomial formulas use the existing ETR codec. Decoding rejects
trailing data and noncanonical encodings. These are codec correctness results,
not polynomial-space certificates for geometric connectivity.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open ETR ETR.Codec

inductive Input where
  | point : PointQuery → Input
  | whole : Description → Input
  deriving DecidableEq, Repr

namespace Input

def toData : Input → Data
  | .point q => .l [unary 0, unary q.space.dimension, q.space.formula.toData,
      q.source.toData, q.target.toData]
  | .whole d => .l [unary 1, unary d.dimension, d.formula.toData]

def fromData : Data → Option Input
  | .l [tag, dim, space, source, target] => do
      let t ← readUnary tag
      if t ≠ 0 then none else do
        let n ← readUnary dim
        let s ← Formula.fromData space
        let a ← Formula.fromData source
        let b ← Formula.fromData target
        some (.point ⟨⟨n, s⟩, a, b⟩)
  | .l [tag, dim, space] => do
      let t ← readUnary tag
      if t ≠ 1 then none else do
        let n ← readUnary dim
        let s ← Formula.fromData space
        some (.whole ⟨n, s⟩)
  | _ => none

@[simp] theorem fromData_toData (i : Input) : fromData i.toData = some i := by
  cases i with
  | point q => cases q; simp [toData, fromData]
  | whole d => cases d; simp [toData, fromData]

def encode (i : Input) : List Bool := i.toData.toBits

def decode (bits : List Bool) : Option Input := do
  let d ← Data.fromBits bits
  let i ← fromData d
  if i.encode = bits then some i else none

@[simp] theorem decode_encode (i : Input) : decode i.encode = some i := by
  simp [decode, encode]

theorem decode_eq_some_iff (bits : List Bool) (i : Input) :
    decode bits = some i ↔ bits = i.encode := by
  constructor
  · intro h
    unfold decode at h
    cases hd : Data.fromBits bits with
    | none => simp [hd] at h
    | some d =>
      rw [hd] at h
      change (fromData d).bind (fun j => if j.encode = bits then some j else none) = some i at h
      cases hi : fromData d with
      | none => simp [hi] at h
      | some j =>
        rw [hi] at h
        change (if j.encode = bits then some j else none) = some i at h
        split at h
        next he => cases h; exact he.symm
        next => simp at h
  · rintro rfl
    exact decode_encode i

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have := congrArg decode h
  simpa using this

end Input

/-- Canonically encoded point-to-point path reachability. Malformed inputs,
ill-formed spaces, and nonunique endpoint descriptions are rejected. -/
def pointLanguage : Language :=
  {bits | ∃ q : PointQuery, bits = (Input.point q).encode ∧ q.Reachable}

/-- Canonically encoded whole-space topological connectivity; empty accepted. -/
def connectedLanguage : Language :=
  {bits | ∃ d : Description, bits = (Input.whole d).encode ∧ d.Connected}

@[simp] theorem point_encode_mem_iff (q : PointQuery) :
    (Input.point q).encode ∈ pointLanguage ↔ q.Reachable := by
  simp only [pointLanguage, Set.mem_ofPred_eq, Input.encode_injective.eq_iff,
    Input.point.injEq, exists_eq_left']

@[simp] theorem whole_encode_mem_iff (d : Description) :
    (Input.whole d).encode ∈ connectedLanguage ↔ d.Connected := by
  simp only [connectedLanguage, Set.mem_ofPred_eq, Input.encode_injective.eq_iff,
    Input.whole.injEq, exists_eq_left']

@[simp] theorem whole_not_mem_pointLanguage (d : Description) :
    (Input.whole d).encode ∉ pointLanguage := by
  simp [pointLanguage, Input.encode_injective.eq_iff]

@[simp] theorem point_not_mem_connectedLanguage (q : PointQuery) :
    (Input.point q).encode ∉ connectedLanguage := by
  simp [connectedLanguage, Input.encode_injective.eq_iff]

end LeanCanny.Connectivity
