/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitFreezeEncoding
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Shared circuits for blocks of free coordinates

The first `dim` inputs are the new free coordinates. Every other original
coordinate is read from its own parent input after that block. Operation
outputs are translated consecutively. Neither the source polynomial nor
the parent coordinate values are expanded or serialized as coefficients.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CircuitBlock
open MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical

def input (offset dim i : ℕ) : ℕ :=
  if offset ≤ i ∧ i < offset + dim then i - offset else dim + i

def index (inputs offset dim start i : ℕ) : ℕ :=
  if i < inputs then input offset dim i else start + (i - inputs)

def program (inputs offset dim start : ℕ) (ops : List Operation) : List Operation :=
  ops.map (Operation.reindex (index inputs offset dim start))

def output (inputs offset dim start out : ℕ) : ℕ := index inputs offset dim start out

noncomputable def substitution (offset dim : ℕ) : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℤ :=
  (rename (input offset dim)).toRingHom

theorem input_free (offset dim : ℕ) (i : Fin dim) : input offset dim (offset + i.val) = i.val := by
  simp only [input, ite_eq_left (show offset ≤ offset + i.val ∧ offset + i.val < offset + dim by omega),
    Nat.add_sub_cancel_left]

theorem input_frozen (offset dim i : ℕ) (hi : ¬(offset ≤ i ∧ i < offset + dim)) :
    input offset dim i = dim + i := ite_eq_right hi

theorem input_injective (offset dim : ℕ) : Function.Injective (input offset dim) := by
  intro i j hij
  unfold input at hij
  split_ifs at hij <;> omega

theorem index_aux (inputs offset dim start q : ℕ) :
    index inputs offset dim start (inputs + q) = start + q := by
  simp only [index, ite_eq_right (show ¬inputs + q < inputs by omega), Nat.add_sub_cancel_left]

theorem index_lt (inputs offset dim start q i : ℕ) (hs : inputs + dim ≤ start)
    (hi : i < inputs + q) : index inputs offset dim start i < start + q := by
  unfold index input
  split_ifs <;> omega

theorem program_length (inputs offset dim start : ℕ) (ops : List Operation) :
    (program inputs offset dim start ops).length = ops.length := List.length_map ..

theorem wellFormed (inputs offset dim start : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed inputs ops) (hs : inputs + dim ≤ start) :
    StraightLine.WellFormed start (program inputs offset dim start ops) :=
  StraightLine.reindex_wellFormed _ inputs start ops hw
    (fun q i hi => index_lt inputs offset dim start q i hs hi)

theorem gates_eq (inputs offset dim start : ℕ) (ops : List Operation) :
    StraightLine.gates start (program inputs offset dim start ops) =
      (StraightLine.gates inputs ops).map (Gate.reindex (index inputs offset dim start)) :=
  StraightLine.reindex_gates _ inputs start ops (index_aux inputs offset dim start)

theorem output_lt (inputs offset dim start out : ℕ) (ops : List Operation)
    (hs : inputs + dim ≤ start) (ho : out < inputs + ops.length) :
    output inputs offset dim start out < start + (program inputs offset dim start ops).length := by
  rw [program_length]
  exact index_lt inputs offset dim start ops.length out hs ho

theorem symbolic_output (inputs offset dim start out : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed inputs ops) (hs : inputs + dim ≤ start)
    (ho : out < inputs + ops.length) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
      (program inputs offset dim start ops) (output inputs offset dim start out) =
        substitution offset dim (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops out) := by
  let old := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program inputs offset dim start ops)
  have hOld := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops hw
  have hMapped := Differential.Realizes.hom (substitution offset dim) old inputs ops hOld
  have hWire := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program inputs offset dim start ops) (wellFormed inputs offset dim start ops hw hs)
  have hReindexed := (Differential.reindex_realizes wire (index inputs offset dim start) inputs start ops
    (index_aux inputs offset dim start)).mp hWire
  apply Differential.realizes_unique (fun i => wire (index inputs offset dim start i))
    (fun i => substitution offset dim (old i)) inputs ops hw hReindexed hMapped ?_ out ho
  intro i hi
  have hlt : index inputs offset dim start i < start := by
    simpa only [Nat.add_zero] using index_lt inputs offset dim start 0 i hs (by omega)
  rw [show wire (index inputs offset dim start i) = X (index inputs offset dim start i) from
    Differential.symbolicRun_preserves_before _ _ _ _ hlt,
    show old i = X i from Differential.symbolicRun_preserves_before _ _ _ _ hi]
  change X (index inputs offset dim start i) = rename (input offset dim) (X i)
  rw [rename_X, index, ite_eq_left hi]

theorem eval_substitution {K : Type*} [CommRing K] (φ : ℤ →+* K) (offset dim : ℕ)
    (p : MvPolynomial ℕ ℤ) (x : ℕ → K) :
    (substitution offset dim p).eval₂ φ x = p.eval₂ φ (fun i => x (input offset dim i)) := by
  change (rename (input offset dim) p).eval₂ φ x = _
  rw [eval₂_rename]
  rfl

theorem index_unary {inputs offset dim start i : List Bool → ℕ}
    (hn : UnaryFn inputs) (ho : BinaryFn offset) (hd : UnaryFn dim) (hs : UnaryFn start) (hi : UnaryFn i) :
    UnaryFn (fun c => index (inputs c) (offset c) (dim c) (start c) (i c)) := by
  have hcap : UnaryFn (fun c => min (offset c) (i c)) :=
    (UnaryFn.fromBitsLE_min ho.bits_mem_FP hi).of_eq
      (fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits])
  have hdiff : UnaryFn (fun c => i c - offset c) := (hi.sub hcap).of_eq (fun c => by omega)
  have hb := (ho.le (BinaryFn.ofUnary hi)).and
    ((BinaryFn.ofUnary hi).lt (ho.add (BinaryFn.ofUnary hd)))
  exact (UnaryFn.ite (FPPred.lt hi hn) (UnaryFn.ite hb hdiff (hd.add hi)) (hs.add (hi.sub hn))).of_eq
    (fun _ => rfl)

namespace Encoded

def index (par : List Bool) (i : ℕ) : ℕ :=
  CircuitBlock.index (pairFst par).length (Nat.fromBitsLE (pairFst (pairSnd par)))
    (pairFst (pairSnd (pairSnd par))).length (pairSnd (pairSnd (pairSnd par))).length i

theorem index_pair (inputs offset dim start : ℕ) :
    index (pair (List.replicate inputs true) (pair (BinaryNatCode.encode offset)
      (pair (List.replicate dim true) (List.replicate start true)))) = CircuitBlock.index inputs offset dim start := by
  funext i
  simp only [index, pairFst_pair, pairSnd_pair, List.length_replicate, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem index_unary : UnaryFn (fun p => index (pairFst p) (pairSnd p).length) := by
  have hn := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have htail := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have ho := mem_FP_comp htail pairFst_mem_FP
  have htail2 := mem_FP_comp htail pairSnd_mem_FP
  have hd := mem_FP_comp htail2 pairFst_mem_FP
  have hs := mem_FP_comp htail2 pairSnd_mem_FP
  exact CircuitBlock.index_unary (UnaryFn.length hn) (BinaryFn.fromBits ho)
    (UnaryFn.length hd) (UnaryFn.length hs) (UnaryFn.length pairSnd_mem_FP)

end Encoded

theorem encode_mem_FP {inputs offset dim start : List Bool → ℕ} {ops : List Bool → List Operation}
    (hn : UnaryFn inputs) (ho : BinaryFn offset) (hd : UnaryFn dim) (hs : UnaryFn start)
    (hg : (fun c => encode (StraightLine.gates (inputs c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (inputs c) (offset c) (dim c) (start c) (ops c)))) ∈ FP := by
  have hpar := mem_FP_pair hn.mem_FP (mem_FP_pair ho.bits_mem_FP (mem_FP_pair hd.mem_FP hs.mem_FP))
  have h := Reindex.encode_mem_FP Encoded.index_unary hpar hg
  apply mem_FP_of_eq h
  intro c
  rw [gates_eq, Encoded.index_pair]

theorem output_unary {inputs offset dim start out : List Bool → ℕ}
    (hn : UnaryFn inputs) (ho : BinaryFn offset) (hd : UnaryFn dim) (hs : UnaryFn start) (hOut : UnaryFn out) :
    UnaryFn (fun c => output (inputs c) (offset c) (dim c) (start c) (out c)) :=
  index_unary hn ho hd hs hOut

end LeanCanny.ETR.ComplexCircuit.CircuitBlock
