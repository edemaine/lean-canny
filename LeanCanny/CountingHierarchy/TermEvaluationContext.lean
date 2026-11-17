/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TermModularExecution
public import LeanCanny.CountingHierarchy.Controlled

/-! # Native evaluation contexts for encoded integer expressions -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermEvaluation

open LeanCanny.Encoding LeanCanny.ETR Turing.MultiTapeTM

abbrev Input := List Bool × (ℕ × List ℕ)

def decoder : Decoder (encEvaluation encBits) :=
  Decoder.pair Decoder.bits (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))

def parameters : TermModular.Parameters where
  prime z := (decoder.decode z).2.1
  coordinate z i := ((decoder.decode z).2.2[i]?).getD 0

theorem parameters_access : TermModular.Access parameters := by
  have hd := decoder.computableInPolyTime
  constructor
  · exact ((ComputableInPolyTime.fst encNat (encList encNat)).comp
      ((ComputableInPolyTime.snd encBits (encPair encNat (encList encNat))).comp hd)).tidy
  · have hlist : ComputableInPolyTime (fun q : List Bool × ℕ => (decoder.decode q.1).2.2)
        (encPair encBits encNat) (encList encNat) := by
      exact (ComputableInPolyTime.snd encNat (encList encNat)).comp
        ((ComputableInPolyTime.snd encBits (encPair encNat (encList encNat))).comp
          (hd.comp (ComputableInPolyTime.fst encBits encNat)))
    have h : ComputableInPolyTime (fun q : List Bool × ℕ => parameters.coordinate q.1 q.2)
        (encPair encBits encNat) encNat := by
      simpa only [parameters, List.getD_eq_getElem?_getD] using
        ComputableInPolyTime.listGetD_binary 0 hlist (ComputableInPolyTime.snd encBits encNat)
    exact h.tidy

def sourceContext (source : List Bool → List Bool) (z : List Bool) : List Bool :=
  TermView.normalize (source (decoder.decode z).1)

theorem sourceContext_FP (source : List Bool → List Bool) (hs : source ∈ FP) : sourceContext source ∈ FP := by
  have hi : (fun z => (decoder.decode z).1) ∈ FP :=
    (ComputableTidilyInPolyTime.fst encBits (encPair encNat (encList encNat))).comp
      decoder.computableInPolyTime.tidy
  exact mem_FP_comp (mem_FP_comp hi hs) TermView.normalize_mem_FP

def evaluate (source : List Bool → List Bool) (q : Input) : ℕ :=
  TermModular.write parameters (sourceContext source) (encEvaluation encBits q)

theorem evaluate_polyTime (source : List Bool → List Bool) (hs : source ∈ FP) :
    ComputableInPolyTime (evaluate source) (encEvaluation encBits) encNat := by
  have hi : ComputableTidilyInPolyTime (fun q : Input => q)
      (encEvaluation encBits) (encEvaluation encBits) := .id'
  have he : ComputableTidilyInPolyTime (fun q : Input => encEvaluation encBits q)
      (encEvaluation encBits) encBits :=
    hi.encoded
  exact ((TermModular.write_binary parameters parameters_access (sourceContext source)
    (sourceContext_FP source hs)).comp he).computableInPolyTime

theorem evaluate_cast (source : List Bool → List Bool) (w : List Bool) (p : ℕ) (z : List ℕ)
    [Fact p.Prime] : (evaluate source (w, p, z) : ZMod p) =
      (TermView.term (source w)).eval (fun i => (z[i]?.getD 0 : ZMod p)) := by
  have hdec : decoder.decode (encEvaluation encBits (w, p, z)) = (w, p, z) := Decoder.decode_enc _ _
  have h := TermModular.write_data parameters (sourceContext source)
    (encEvaluation encBits (w, p, z)) (TermView.term (source w)).toData
    (by simp only [sourceContext, hdec, TermView.normalize_eq_term])
  have hv : evaluate source (w, p, z) = TermModular.value p
      (fun i => z[i]?.getD 0) (TermView.term (source w)).toData := by
    simpa only [parameters, hdec, evaluate] using h
  rw [hv]
  exact TermModular.value_term_cast _ _

theorem evaluate_lt (source : List Bool → List Bool) (w : List Bool) (p : ℕ) (z : List ℕ)
    (hp : p.Prime) : evaluate source (w, p, z) < p := by
  have hdec : decoder.decode (encEvaluation encBits (w, p, z)) = (w, p, z) := Decoder.decode_enc _ _
  have h := TermModular.write_data parameters (sourceContext source)
    (encEvaluation encBits (w, p, z)) (TermView.term (source w)).toData
    (by simp only [sourceContext, hdec, TermView.normalize_eq_term])
  unfold evaluate
  rw [h]
  have hb := TermModular.value_lt p (fun i => z[i]?.getD 0) (TermView.term (source w)).toData
  simpa only [parameters, hdec, TermModular.modulus, max_eq_right hp.one_le] using hb

end LeanCanny.CountingHierarchy.TermEvaluation
