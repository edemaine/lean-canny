/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveGraphMidpoints

/-! # Recursive midpoint calls preserve short native graph query records

Each child keeps the same original context and replaces one vertex word by a
word of exactly the graph width. On valid endpoint words, the complete child
record is no longer than its parent, including its serialized depth counter.
-/

@[expose] public section
namespace LeanCanny.Computation.RecursiveGraphMidpoints
open LeanCanny.Encoding Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem task_length (c : List Bool) (d : ℕ) (u v : List Bool) :
    (task c d u v).length = 4 * c.length + 2 * (BinaryNatCode.encode d).length + 2 * u.length + v.length + 8 := by
  simp only [task, pair_length]
  omega

theorem request_packet (width : List Bool → ℕ) (answer : List Bool → List Bool)
    (c : List Bool) (d : ℕ) (u v child : List Bool)
    (hrequest : (program width).controller.Requests answer (fun q => 2 * (program width).count q)
      (task c (d + 1) u v) child) :
    ∃ m : List Bool, m.length = width c ∧ (child = task c d u m ∨ child = task c d m v) := by
  obtain ⟨k, _, he | he⟩ := ((program width).requests_iff answer (task c (d + 1) u v) child).mp hrequest
  · refine ⟨ImplicitGraph.word (width c) k, ImplicitGraph.length_word _ _, Or.inl ?_⟩
    simpa only [program, left, PairedScan.Program.entry, task, context, depth, depthWord, start,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel] using he
  · refine ⟨ImplicitGraph.word (width c) k, ImplicitGraph.length_word _ _, Or.inr ?_⟩
    simpa only [program, right, PairedScan.Program.entry, task, context, depth, depthWord, finish,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel] using he

theorem request_length (width : List Bool → ℕ) (answer : List Bool → List Bool)
    (c : List Bool) (d : ℕ) (u v child : List Bool) (hu : u.length = width c) (hv : v.length = width c)
    (hrequest : (program width).controller.Requests answer (fun q => 2 * (program width).count q)
      (task c (d + 1) u v) child) : child.length ≤ (task c (d + 1) u v).length := by
  have HD : (BinaryNatCode.encode d).length ≤ (BinaryNatCode.encode (d + 1)).length := by
    simpa only [BinaryNatCode.encode, ← Nat.size_eq_bits_len] using Nat.size_le_size (Nat.le_succ d)
  obtain ⟨m, hm, he | he⟩ := request_packet width answer c d u v child hrequest
  all_goals rw [he, task_length, task_length, hu, hv, hm]
  all_goals omega

theorem budget_binary {width : List Bool → ℕ} (hw : UnaryFn width) :
    BinaryFn (fun q => 2 * (program width).count q) :=
  (BinaryFn.const 2).mul (ComputableTidilyInPolyTime.binary_two_pow.comp (hw.comp context_FP))

end LeanCanny.Computation.RecursiveGraphMidpoints
