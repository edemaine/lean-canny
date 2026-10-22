/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Algebra.CannyResultantRecursiveStage

/-! # A one-request symbolic pair source for a uniform task scheduler

The encoded entry degree is split into alpha and theta indices before the
existing integer Canny controller runs on a slice. Its sole child request
retains alpha in the context. This constructs the local recursive source;
global reachable-task bounds and source-descent ranks remain a separate layer.
-/

@[expose] public section

namespace LeanCanny.Computation.SingleCall.Program
open Turing.MultiTapeTM

def reindex (P : SingleCall.Program) (f : List Bool → List Bool) : SingleCall.Program where
  request p := P.request (f p)
  query p := P.query (f p)
  immediate p := P.immediate (f p)
  finish p := P.finish (pair (f (pairFst p)) (pairSnd p))

theorem value_reindex (P : SingleCall.Program) (f answer : List Bool → List Bool) (p : List Bool) :
    (P.reindex f).value answer p = P.value answer (f p) := by
  simp only [SingleCall.Program.value, reindex, pairFst_pair, pairSnd_pair]

def reindexFinish (f : List Bool → List Bool) (p : List Bool) : List Bool := pair (f (pairFst p)) (pairSnd p)

theorem reindexFinish_FP (f : List Bool → List Bool) (hf : f ∈ FP) : reindexFinish f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

theorem reindex_certificates_of_space (P : SingleCall.Program) (f : List Bool → List Bool) (hf : f ∈ FP)
    (hrequest : (fun p => [P.request p]) ∈ FP) (hquery : P.query ∈ FP)
    (hi : SpaceFunction P.immediate) (hfinish : SpaceFunction P.finish) :
    (P.reindex f).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) := by
  apply SingleCall.Program.certificates_of_space
  · exact mem_FP_of_eq (mem_FP_comp (f := f) (g := fun p => [P.request p]) hf hrequest) (fun _ => rfl)
  · exact mem_FP_of_eq (mem_FP_comp (f := f) (g := P.query) hf hquery) (fun _ => rfl)
  · exact (hi.precompose f hf).computable
  · exact (hfinish.precompose (reindexFinish f) (reindexFinish_FP f hf)).computable

end LeanCanny.Computation.SingleCall.Program

namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable

def entryDegree (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd p))

theorem entryDegree_FP : entryDegree ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def splitInput (radix : List Bool → List Bool) (p : List Bool) : List Bool :=
  let d := pair (entryDegree p) (radix (pairFst p))
  pair (pairFst p) (pair (pairFst (pairSnd p)) (pair (pairFst (pairSnd (pairSnd p)))
    (pair (BinaryNat.mod d) (BinaryNat.div d))))

theorem splitInput_FP (radix : List Bool → List Bool) (hr : radix ∈ FP) : splitInput radix ∈ FP := by
  have hd := mem_FP_pair entryDegree_FP (mem_FP_comp pairFst_mem_FP hr)
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
      (mem_FP_pair (mem_FP_comp hd BinaryNat.mod_mem_FP) (mem_FP_comp hd BinaryNat.div_mem_FP))))

def sourceInput (radix : List Bool → List Bool) : List Bool → List Bool := entryQuery ∘ splitInput radix

theorem sourceInput_FP (radix : List Bool → List Bool) (hr : radix ∈ FP) : sourceInput radix ∈ FP :=
  mem_FP_comp (splitInput_FP radix hr) entryQuery_FP

noncomputable def Family.encodedEntry (F : Family) (radix : List Bool → List Bool) : List Bool → List Bool :=
  F.entry ∘ splitInput radix

noncomputable def Family.sourceProgram (F : Family) (radix leftTask rightTask : List Bool → List Bool) : SingleCall.Program :=
  (CannyResultantBits.RecursiveStage.program F.access leftTask rightTask).reindex (sourceInput radix)

theorem Family.sourceProgram_correct (F : Family) (radix leftTask rightTask answer : List Bool → List Bool)
    (hl : ∀ p, answer (leftTask p) = F.access.leftCoefficient p)
    (hr : ∀ p, answer (rightTask p) = F.access.rightCoefficient p) (p : List Bool) :
    (F.sourceProgram radix leftTask rightTask).value answer p = F.encodedEntry radix p := by
  rw [Family.sourceProgram, SingleCall.Program.value_reindex]
  exact CannyResultantBits.RecursiveStage.value_eq F.access leftTask rightTask answer hl hr (sourceInput radix p)

theorem Family.sourceProgram_certificates (F : Family) (radix leftTask rightTask : List Bool → List Bool)
    (hmod : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction)
    (hr : radix ∈ FP) (hlTask : leftTask ∈ FP) (hrTask : rightTask ∈ FP) :
    (F.sourceProgram radix leftTask rightTask).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) := by
  have ha := F.access_controls hmod hn hc
  have hquery := (flag_computable (CannyResultantBits.RecursiveStage.selectRight_FP F.access ha)).ite'
    (mem_FP_comp CannyResultantBits.RecursiveStage.rightQuery_FP hrTask)
    (mem_FP_comp (CannyResultantBits.RecursiveStage.leftQuery_FP F.access ha) hlTask)
  exact SingleCall.Program.reindex_certificates_of_space
    (CannyResultantBits.RecursiveStage.program F.access leftTask rightTask) _ (sourceInput_FP radix hr)
    (CannyResultantBits.RecursiveStage.request_FP F.access ha) (mem_FP_of_eq hquery (fun _ => rfl))
    (SpaceFunction.ofFP _ (constFn_mem_FP [])) (CannyResultantBits.RecursiveStage.finish_space F.access ha)

theorem Family.encodedEntry_correct (F : Family) (radix : List Bool → List Bool) (c m : List Bool)
    (E : ℕ) (hleft : ∀ k, ((F.left c).coeff k).natDegree ≤ E)
    (hright : ∀ k, ((F.right c).coeff k).natDegree ≤ E)
    (hB : E < Nat.fromBitsLE (radix (pair c m)))
    (i j : Fin (F.leftOrder c + F.rightOrder c)) (d : ℕ) :
    F.encodedEntry radix (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) =
      integerResidue
        ((PolynomialKronecker.encode (Nat.fromBitsLE (radix (pair c m)))
          (Polynomial.sylvester (shiftFamily (F.left c) (F.direction c)) ((F.right c).map C)
            (F.leftOrder c) (F.rightOrder c) i j)).coeff d) (Nat.fromBitsLE m + 1) := by
  have h := F.entry_correct c m i j (d % Nat.fromBitsLE (radix (pair c m))) (d / Nat.fromBitsLE (radix (pair c m)))
  change F.entry _ = integerResidue _ (Nat.fromBitsLE m + 1) at h
  have he := encoded_sylvester_coefficient (F.left c) (F.right c) (F.direction c)
    (F.leftOrder c) (F.rightOrder c) E (Nat.fromBitsLE (radix (pair c m))) hleft hright hB i j d
  rw [he, ← sylvester_slice] -- the right side of `he` is exactly the sliced integer entry
  simpa only [Family.encodedEntry, Function.comp_apply, splitInput, entryDegree, pairFst_pair, pairSnd_pair,
    BinaryNat.mod_pair, BinaryNat.div_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
