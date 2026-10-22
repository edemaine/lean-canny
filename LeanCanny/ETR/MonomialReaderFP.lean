/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderCorrect
public import LeanCanny.ETR.MonomialReaderBounds

/-!
# Polynomial-time selected-monomial traversal

FP term/index/seed writers and leaf accumulation give a uniform FP reader
whenever the accumulator has a polynomial binary-size bound. The complete
task stack is bounded using the original tree size and index word length.
The context, stack, accumulator, and polynomial traversal clock are included.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding

def initBits (term index seed : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair c (pair (pair (pair (term c) (BinaryNat.normalize (index c))) []) (seed c))

theorem initBits_mem_FP {term index seed : List Bool → List Bool}
    (ht : term ∈ FP) (hi : index ∈ FP) (hs : seed ∈ FP) : initBits term index seed ∈ FP := by
  have hindex := mem_FP_comp hi BinaryNat.normalize_mem_FP
  have h := mem_FP_pair id_mem_FP (mem_FP_pair (mem_FP_pair (mem_FP_pair ht hindex) (constFn_mem_FP [])) hs)
  refine mem_FP_of_eq (g := initBits term index seed) h ?_
  intro c
  simp only [initBits, Function.comp_apply]
  rfl

def evaluate (atom term index seed : List Bool → List Bool) (c : List Bool) : List Bool :=
  accumulator ((stepBits atom)^[(term c).length] (initBits term index seed c))

section
variable {R : List Bool → Type*} [∀ c, Monoid (R c)]
variable (code : (c : List Bool) → R c → List Bool)
variable (constant : (c : List Bool) → ℤ → R c) (variableValue : (c : List Bool) → ℕ → R c)
variable (T : List Bool → Term) (term index seed atom : List Bool → List Bool)
variable (ht : ∀ c, term c = (T c).toData.toBits) (hs : ∀ c, seed c = code c 1)
variable (hc : ∀ c z v, atom (pair c (pair (Term.const z).toData.toBits (code c v))) = code c (v * constant c z))
variable (hv : ∀ c i v, atom (pair c (pair (Term.var i).toData.toBits (code c v))) = code c (v * variableValue c i))

include ht hs

theorem initBits_encode (c : List Bool) : initBits term index seed c =
    pair c ((⟨[⟨T c, Nat.fromBitsLE (index c)⟩], 1⟩ : State (R c)).encode (code c)) := by
  simp only [initBits, ht, hs, State.encode, DynamicTreeFold.stackBits, Task.encode, BinaryNat.normalize_eq_bits,
    BinaryNatCode.encode]

include hc hv

theorem evaluate_eq (c : List Bool) : evaluate atom term index seed c =
    code c (fold (constant c) (variableValue c) (T c) (Nat.fromBitsLE (index c))) := by
  rw [evaluate, initBits_encode code T term index seed ht hs,
    iterate_encode (code c) (constant c) (variableValue c) atom c (hc c) (hv c), run_steps]
  · simp only [accumulator, State.encode, pairSnd_pair]
  · rw [ht c, Data.length_toBits]
    exact work_le_dataSize _ _

theorem reader_mem_FP (htFP : term ∈ FP) (hiFP : index ∈ FP) (hsFP : seed ∈ FP) (haFP : atom ∈ FP)
    (pA : Polynomial ℕ)
    (hacc : ∀ c k, k ≤ (term c).length →
      (code c (((step (constant c) (variableValue c))^[k]
        ⟨[⟨T c, Nat.fromBitsLE (index c)⟩], 1⟩).value)).length ≤ pA.eval c.length) :
    (fun c => code c (fold (constant c) (variableValue c) (T c) (Nat.fromBitsLE (index c)))) ∈ FP := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP htFP
  obtain ⟨q, hq⟩ := output_length_poly_of_mem_FP hiFP
  let B := fun n => 2 * n + 4 + (4 * q.eval n + 20) * p.eval n + pA.eval n
  have hB : PolyBound B :=
    ((((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 4)).add
      ((((PolyBound.const 4).mul (PolyBound.eval q)).add (PolyBound.const 20)).mul (PolyBound.eval p))).add (PolyBound.eval pA)
  have hloop := iterate_mem_FP_of_polyBound (stepBits_mem_FP haFP) (initBits_mem_FP htFP hiFP hsFP) htFP hB (by
    intro c k hk
    rw [initBits_encode code T term index seed ht hs,
      iterate_encode (code c) (constant c) (variableValue c) atom c (hc c) (hv c)]
    have hstate := initial_encode_length_le (constant c) (variableValue c) (code c) (T c)
      (Nat.fromBitsLE (index c)) k c
    have hT : (T c).toData.size ≤ p.eval c.length := by rw [← Data.length_toBits, ← ht c]; exact hp c
    have hI : (Nat.fromBitsLE (index c)).size ≤ q.eval c.length :=
      (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (index c))).trans (hq c)
    have hprod := Nat.mul_le_mul (show 4 * (Nat.fromBitsLE (index c)).size + 20 ≤ 4 * q.eval c.length + 20 by omega) hT
    have hA := hacc c k hk
    dsimp only [B]
    omega)
  have houtput := mem_FP_comp hloop accumulator_mem_FP
  refine mem_FP_of_eq (g := fun c => code c (fold (constant c) (variableValue c) (T c) (Nat.fromBitsLE (index c)))) houtput ?_
  intro c
  exact evaluate_eq code constant variableValue T term index seed atom ht hs hc hv c

end
end LeanCanny.ETR.MonomialReader
