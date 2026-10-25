/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitShift

/-! # Native reindexing of shared arithmetic networks

Input-dependent unary maps can reindex every wire of a gate list. Straight-line
outputs remain consecutive when the map is a translation on the output range;
the input references can follow a different map.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Encoding.Brackets

def Gate.reindex (f : ℕ → ℕ) : Gate → Gate
  | .constant out z => .constant (f out) z
  | .add out left right => .add (f out) (f left) (f right)
  | .mul out left right => .mul (f out) (f left) (f right)
  | .zero wire => .zero (f wire)

theorem Gate.reindex_holds (f : ℕ → ℕ) (g : Gate) (env : ℕ → ℂ) :
    (g.reindex f).Holds env ↔ g.Holds (fun i => env (f i)) := by cases g <;> rfl

def Operation.reindex (f : ℕ → ℕ) : Operation → Operation
  | .constant z => .constant z
  | .add left right => .add (f left) (f right)
  | .mul left right => .mul (f left) (f right)

theorem Operation.reindex_gate (f : ℕ → ℕ) (out : ℕ) (op : Operation) :
    (op.reindex f).gate (f out) = (op.gate out).reindex f := by cases op <;> rfl

theorem Operation.reindex_inputsBelow (f : ℕ → ℕ) (out next : ℕ) (op : Operation)
    (hw : op.InputsBelow out) (hf : ∀ i < out, f i < next) : (op.reindex f).InputsBelow next := by
  cases op with
  | constant z => trivial
  | add left right => exact ⟨hf left hw.1, hf right hw.2⟩
  | mul left right => exact ⟨hf left hw.1, hf right hw.2⟩

theorem StraightLine.reindex_gates (f : ℕ → ℕ) (start next : ℕ) (ops : List Operation)
    (hf : ∀ q, f (start + q) = next + q) :
    gates next (ops.map (Operation.reindex f)) = (gates start ops).map (Gate.reindex f) := by
  induction ops generalizing start next with
  | nil => rfl
  | cons op ops ih =>
    have h0 : f start = next := by simpa only [Nat.add_zero] using hf 0
    have ht (q : ℕ) : f (start + 1 + q) = next + 1 + q := by
      simpa only [Nat.add_assoc] using hf (1 + q)
    simp only [List.map_cons, gates]
    apply congrArg₂ List.cons
    · rw [← h0, Operation.reindex_gate]
    · exact ih (start + 1) (next + 1) ht

theorem StraightLine.reindex_wellFormed (f : ℕ → ℕ) (start next : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) (hf : ∀ q, ∀ i < start + q, f i < next + q) :
    WellFormed next (ops.map (Operation.reindex f)) := by
  induction ops generalizing start next with
  | nil => trivial
  | cons op ops ih =>
    have h0 : ∀ i < start, f i < next := by simpa only [Nat.add_zero] using hf 0
    have ht (q i : ℕ) (hi : i < start + 1 + q) : f i < next + 1 + q := by
      simpa only [Nat.add_assoc] using hf (1 + q) i (by simpa only [Nat.add_assoc] using hi)
    exact ⟨Operation.reindex_inputsBelow f start next op hw.1 h0, ih (start + 1) (next + 1) hw.2 ht⟩

namespace Reindex

def gateBits (index : List Bool → ℕ → ℕ) (packet : List Bool) : List Bool :=
  let g := pairSnd packet
  let f := index (pairFst packet)
  if firstChild g = (Codec.unary 0).toBits then constantGateBits (f (outIndex g)) (NNF.second (payload g))
  else if firstChild g = (Codec.unary 1).toBits then arithmeticGateBits 1 (f (outIndex g)) (f (leftIndex g)) (f (rightIndex g))
  else if firstChild g = (Codec.unary 2).toBits then arithmeticGateBits 2 (f (outIndex g)) (f (leftIndex g)) (f (rightIndex g))
  else zeroGateBits (f (Codec.unaryValue (payload g)))

attribute [local irreducible] outIndex leftIndex rightIndex payload NNF.second firstChild

theorem gateBits_mem_FP {index : List Bool → ℕ → ℕ}
    (hi : UnaryFn (fun p => index (pairFst p) (pairSnd p).length)) : gateBits index ∈ FP := by
  have hm {i : List Bool → ℕ} (h : UnaryFn i) : UnaryFn (fun p => index (pairFst p) (i p)) :=
    (UnaryFn.comp hi (mem_FP_pair pairFst_mem_FP h.mem_FP)).of_eq
      (fun p => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate])
  have ho := hm (UnaryFn.comp (f := outIndex) (g := pairSnd) outIndex_unary pairSnd_mem_FP)
  have hl := hm (UnaryFn.comp (f := leftIndex) (g := pairSnd) leftIndex_unary pairSnd_mem_FP)
  have hr := hm (UnaryFn.comp (f := rightIndex) (g := pairSnd) rightIndex_unary pairSnd_mem_FP)
  have hp := mem_FP_comp (f := pairSnd) (g := payload) pairSnd_mem_FP payload_mem_FP
  have hc := constantGateBits_mem_FP ho (mem_FP_comp hp NNF.second_mem_FP)
  have hz := zeroGateBits_mem_FP (hm (UnaryFn.comp Codec.unaryValue_unary hp))
  have htag (k : ℕ) := stringEq_fppred (mem_FP_comp pairSnd_mem_FP firstChild_mem_FP)
    (constFn_mem_FP (Codec.unary k).toBits)
  exact mem_FP_of_eq ((htag 0).ite_mem_FP hc ((htag 1).ite_mem_FP
    (arithmeticGateBits_mem_FP 1 ho hl hr) ((htag 2).ite_mem_FP (arithmeticGateBits_mem_FP 2 ho hl hr) hz)))
    (fun _ => rfl)

theorem gateBits_encode (index : List Bool → ℕ → ℕ) (par : List Bool) (g : Gate) :
    gateBits index (pair par g.encode) = (g.reindex (index par)).encode := by
  cases g <;>
    simp [gateBits, pairFst_pair, pairSnd_pair, Gate.encode, Gate.toData, Gate.reindex,
      outIndex, leftIndex, rightIndex, payload, Codec.unary_toBits_injective.eq_iff,
      constantGateBits_encode, addGateBits_encode, mulGateBits_encode, zeroGateBits_encode]

def run (index : List Bool → ℕ → ℕ) : List Bool → List Bool := CapturedTransform.run (gateBits index)

theorem run_mem_FP {index : List Bool → ℕ → ℕ}
    (hi : UnaryFn (fun p => index (pairFst p) (pairSnd p).length)) : run index ∈ FP :=
  CapturedTransform.run_mem_FP (gateBits_mem_FP hi)

theorem run_encode (index : List Bool → ℕ → ℕ) (par : List Bool) (gs : List Gate) :
    run index (pair par (encode gs)) = encode (gs.map (Gate.reindex (index par))) := by
  have hw (g : Gate) : gateBits index (pair par g.encode) = forest [g.reindex (index par)] := by
    rw [gateBits_encode, forest_cons, forest_nil, List.append_nil]
  have hm : gs.flatMap (fun g => [g.reindex (index par)]) = gs.map (Gate.reindex (index par)) := by
    induction gs with
    | nil => rfl
    | cons g gs ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]
  have h := CapturedTransform.run_encode (gateBits index) par (fun g => [g.reindex (index par)]) hw gs
  simpa only [run, hm] using h

theorem encode_mem_FP {index : List Bool → ℕ → ℕ} {par : List Bool → List Bool} {gs : List Bool → List Gate}
    (hi : UnaryFn (fun p => index (pairFst p) (pairSnd p).length)) (hp : par ∈ FP)
    (hg : (fun c => encode (gs c)) ∈ FP) :
    (fun c => encode ((gs c).map (Gate.reindex (index (par c))))) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_pair hp hg) (run_mem_FP hi)) (fun c => run_encode index (par c) (gs c))

end Reindex
end LeanCanny.ETR.ComplexCircuit
