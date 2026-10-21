/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunction
public import LeanCanny.Encoding.BinarySubFP

/-!
# Bounded folds with certified space-bounded updates

The update receives `pair context (pair index accumulator)`. A binary bound
permits exponentially many updates, while the retained accumulator remains
short. Updates compose directly in the tidy space calculus.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedFold

open LeanCanny.Encoding

def counter (p : List Bool) : List Bool := pairFst (pairSnd p)
def accumulator (p : List Bool) : List Bool := pairSnd (pairSnd p)
def packet (c : List Bool) (i : ℕ) (v : List Bool) : List Bool := pair c (pair (BinaryNatCode.encode i) v)
def init (seed : List Bool → List Bool) (c : List Bool) : List Bool := packet c 0 (seed c)
def halted (bound : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (bound (pairFst p)) ≤ Nat.fromBitsLE (counter p))
def fold (f seed : List Bool → List Bool) (c : List Bool) : ℕ → List Bool
  | 0 => seed c
  | i + 1 => f (packet c i (fold f seed c i))

theorem counter_mem_FP : counter ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem accumulator_mem_FP : accumulator ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem init_mem_FP {seed : List Bool → List Bool} (hs : seed ∈ FP) : init seed ∈ FP := by
  have h := mem_FP_pair id_mem_FP (mem_FP_pair (constFn_mem_FP []) hs)
  refine mem_FP_of_eq (g := init seed) h ?_
  intro c
  rfl

theorem halted_mem_FP {bound : List Bool → List Bool} (hb : bound ∈ FP) : (fun p => [halted bound p]) ∈ FP :=
  (BinaryNat.le_fppred (mem_FP_comp pairFst_mem_FP hb) counter_mem_FP).flag_mem_FP

@[simp] theorem context_packet (c : List Bool) (i : ℕ) (v : List Bool) : pairFst (packet c i v) = c := by simp [packet]
@[simp] theorem counter_packet (c : List Bool) (i : ℕ) (v : List Bool) :
    counter (packet c i v) = BinaryNatCode.encode i := by simp [counter, packet]
@[simp] theorem accumulator_packet (c : List Bool) (i : ℕ) (v : List Bool) : accumulator (packet c i v) = v := by
  simp [accumulator, packet]

theorem halted_packet (bound : List Bool → List Bool) (c : List Bool) (i : ℕ) (v : List Bool) :
    halted bound (packet c i v) = decide (Nat.fromBitsLE (bound c) ≤ i) := by
  simp only [halted, context_packet, counter_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Computation.BoundedFold
