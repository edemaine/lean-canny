/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthNatVector
public import LeanCanny.Tactic.PolyTime

/-! # FP fixed-width vector writing from coordinate access

A polynomial number of fixed-width coordinates can be written bit by bit
using a uniform FP binary coordinate reader. Oversized coordinates are
truncated to the requested width; the earlier round trip applies when they fit.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthNatVector


open Turing.MultiTapeTM

/-- Write coordinates with binary values and an arbitrary index encoding
reachable from unary. Oversized coordinates are truncated, including at width zero. -/
theorem encode_of_coordinate {α : Type} {encIn : α ↪ List Bool}
    {encIndex : ℕ ↪ List Bool} {A W : α → ℕ} {e : α → ℕ → ℕ}
    (hA : ComputableTidilyInPolyTime A encIn encUnary)
    (hW : ComputableTidilyInPolyTime W encIn encUnary)
    (hindex : ComputableTidilyInPolyTime id encUnary encIndex)
    (he : ComputableTidilyInPolyTime (fun p : α × ℕ => e p.1 p.2)
      (encPair encIn encIndex) encNat) :
    ComputableTidilyInPolyTime (fun c => encode (A c) (W c) (e c)) encIn encBits := by
  have hwidth := hW.comp (ComputableTidilyInPolyTime.fst encIn encUnary)
  have hk := ComputableTidilyInPolyTime.snd encIn encUnary
  have hcoord := he.comp ((ComputableTidilyInPolyTime.fst encIn encUnary).prod
    (hindex.comp (ComputableTidilyInPolyTime.unary_div.comp (hk.prod hwidth))))
  have hbit := ComputableTidilyInPolyTime.binary_testBit hcoord
    (ComputableTidilyInPolyTime.unary_mod.comp (hk.prod hwidth))
  have hbit' : ComputableTidilyInPolyTime
      (fun p : α × ℕ => (e p.1 (p.2 / W p.1)).testBit (p.2 % W p.1))
      (encPair encIn encUnary) encBool := by
    simpa only [Function.comp_apply, id_eq] using hbit
  have hcount := ComputableTidilyInPolyTime.unary_mul.comp (hA.prod hW)
  have h := ComputableTidilyInPolyTime.mapToBitsWithInput
    (f := fun c k => (e c (k / W c)).testBit (k % W c))
    (ComputableTidilyInPolyTime.range.comp hcount) hbit'
  refine h.of_enc_eq fun c => ?_
  simp only [encBits_apply, Function.comp_apply]
  apply List.ext_getElem
  · simp [encode]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, encode, List.getElem_ofFn]

/-- Turn a total raw packet reader into a typed coordinate reader. -/
theorem coordinate_of_reader {e : List Bool → ℕ → ℕ} {read : List Bool → List Bool}
    (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (e c i)) :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => e p.1 p.2)
      (encPair encBits encNat) encNat := by
  have hpacket : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ => pair p.1 (BinaryNatCode.encode p.2))
      (encPair encBits encNat) encBits :=
    pair_computable (ComputableTidilyInPolyTime.fst encBits encNat)
      (natBits_computable.comp (ComputableTidilyInPolyTime.snd encBits encNat))
  exact (hr.comp hpacket).of_enc_eq fun p => (he p.1 p.2).symm

/-- Compatibility interface for existing raw packet readers. -/
theorem encode_mem_FP (A W : List Bool → ℕ) (e : List Bool → ℕ → ℕ)
    (hA : UnaryFn A) (hW : UnaryFn W) (read : List Bool → List Bool) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (e c i)) :
    (fun c => encode (A c) (W c) (e c)) ∈ FP :=
  encode_of_coordinate hA hW ComputableTidilyInPolyTime.unary_to_binary
    (coordinate_of_reader hr he)

end LeanCanny.Encoding.FixedWidthNatVector
