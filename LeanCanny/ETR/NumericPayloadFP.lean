/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.BitPayload

/-!
# Polynomial-time recognition of the ETR numeric payloads

Natural magnitudes are checked as digit strings, including canonicality. The
integer checker then validates the sign field and the exact two-field framing.
Both predicates recognize precisely the images of the original typed codecs.
-/

@[expose] public section

namespace LeanCanny.ETR.Codec
open Complexity
open LeanCanny.Encoding.Brackets

theorem natural_toBits (n : ℕ) :
    (natural n).toBits = wrap (BitPayload.body n.bits) := by
  simp only [natural, Data.toBits_l, List.map_map, Function.comp_def, wrap, BitPayload.body]

def IsNatural (bits : List Bool) : Prop :=
  TreeCode bits ∧ (BitPayload.run (contents bits)).phase = .ready ∧
    CanonicalDigits (BitPayload.run (contents bits)).output

instance isNaturalDecidable (bits : List Bool) : Decidable (IsNatural bits) := by
  unfold IsNatural
  infer_instance

theorem isNatural_iff (bits : List Bool) :
    IsNatural bits ↔ ∃ n : ℕ, bits = (natural n).toBits := by
  constructor
  · rintro ⟨htree, hready, hcanonical⟩
    obtain ⟨n, hn⟩ := (canonicalDigits_iff _).mp hcanonical
    obtain ⟨d, hd⟩ := (treeCode_iff bits).mp htree
    have hwrap : bits = wrap (contents bits) := by
      rw [hd]
      cases d with
      | l xs => rw [contents_toBits, wrap, Data.toBits_l]
    refine ⟨n, ?_⟩
    calc
      bits = wrap (contents bits) := hwrap
      _ = wrap (BitPayload.body (BitPayload.run (contents bits)).output) :=
        congrArg wrap (BitPayload.body_of_ready _ hready)
      _ = wrap (BitPayload.body n.bits) := by rw [hn]
      _ = (natural n).toBits := (natural_toBits n).symm
  · rintro ⟨n, rfl⟩
    have hcontents : contents (natural n).toBits = BitPayload.body n.bits := by
      simp only [natural, contents_toBits, List.map_map, Function.comp_def, BitPayload.body]
    refine ⟨treeCode_toBits _, ?_, ?_⟩
    · rw [hcontents, BitPayload.run_body]
    · rw [hcontents, BitPayload.run_body]
      exact canonicalDigits_bits n

theorem isNatural_fppred : FPPred IsNatural :=
  treeCode_fppred.and ((BitPayload.ready_fppred.comp contents_mem_FP).and
    (canonicalDigits_fppred.comp (mem_FP_comp contents_mem_FP BitPayload.output_mem_FP)))

/-- The second child is the magnitude field in an integer payload. -/
def integerMagnitude (bits : List Bool) : List Bool := firstChild (remainingChildren bits)

theorem integerMagnitude_mem_FP : integerMagnitude ∈ FP :=
  mem_FP_comp remainingChildren_mem_FP firstChild_mem_FP

def IsInteger (bits : List Bool) : Prop :=
  (bits = taggedOne 0 (integerMagnitude bits) ∨ bits = taggedOne 1 (integerMagnitude bits)) ∧
    IsNatural (integerMagnitude bits)

instance isIntegerDecidable (bits : List Bool) : Decidable (IsInteger bits) := by
  unfold IsInteger
  infer_instance

theorem isInteger_iff (bits : List Bool) :
    IsInteger bits ↔ ∃ z : ℤ, bits = (integer z).toBits := by
  constructor
  · rintro ⟨hsign, hnat⟩
    obtain ⟨n, hn⟩ := (isNatural_iff _).mp hnat
    rcases hsign with hpos | hneg
    · refine ⟨.ofNat n, ?_⟩
      simpa only [hn, taggedOne_toBits, integer] using hpos
    · refine ⟨.negSucc n, ?_⟩
      simpa only [hn, taggedOne_toBits, integer] using hneg
  · rintro ⟨z, rfl⟩
    cases z with
    | ofNat n =>
        have hm : integerMagnitude (integer (.ofNat n)).toBits = (natural n).toBits := by
          simp only [integerMagnitude, integer, remainingChildren_toBits, firstChild_toBits]
        refine ⟨Or.inl ?_, (isNatural_iff _).mpr ⟨n, hm⟩⟩
        rw [hm, taggedOne_toBits, integer]
    | negSucc n =>
        have hm : integerMagnitude (integer (.negSucc n)).toBits = (natural n).toBits := by
          simp only [integerMagnitude, integer, remainingChildren_toBits, firstChild_toBits]
        refine ⟨Or.inr ?_, (isNatural_iff _).mpr ⟨n, hm⟩⟩
        rw [hm, taggedOne_toBits, integer]

theorem isInteger_fppred : FPPred IsInteger :=
  ((stringEq_fppred id_mem_FP (taggedOne_mem_FP 0 integerMagnitude_mem_FP)).or
    (stringEq_fppred id_mem_FP (taggedOne_mem_FP 1 integerMagnitude_mem_FP))).and
      (isNatural_fppred.comp integerMagnitude_mem_FP)

end LeanCanny.ETR.Codec
