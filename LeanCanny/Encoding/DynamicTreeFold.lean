/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.TreeFold

/-!
# Polynomial-time tree folds with variable-length frames

Stack frames use self-delimiting pairs, with the stack tail in the undoubled
component. This charges each frame's bytes twice, independently of stack depth.
The implementation supports an input-dependent frame algebra. Its time theorem
requires polynomial-time frame operations and a bound on every intermediate
encoded stack; polynomial final output length alone is not sufficient.
-/

@[expose] public section

namespace LeanCanny.Encoding.DynamicTreeFold

open Brackets

variable {σ : Type*}

def stackBits (code : σ → List Bool) : List σ → List Bool
  | [] => []
  | s :: rest => pair (code s) (stackBits code rest)

def encode (code : σ → List Bool) : Option (List σ) → List Bool
  | none => [false]
  | some stack => true :: stackBits code stack

def weight (code : σ → List Bool) : List σ → ℕ
  | [] => 0
  | s :: rest => 2 * (code s).length + 2 + weight code rest

@[simp] theorem stackBits_length (code : σ → List Bool) (stack : List σ) :
    (stackBits code stack).length = weight code stack := by
  induction stack <;> simp_all [stackBits, weight]

@[simp] theorem stackBits_eq_nil_iff (code : σ → List Bool) (stack : List σ) :
    stackBits code stack = [] ↔ stack = [] := by
  cases stack with
  | nil => simp [stackBits]
  | cons s rest =>
      constructor
      · intro h
        have he := congrArg List.length h
        simp only [stackBits_length, weight, List.length_nil] at he
        omega
      · simp

@[simp] theorem encode_some_length (code : σ → List Bool) (stack : List σ) :
    (encode code (some stack)).length = 1 + weight code stack := by
  simp [encode, Nat.add_comm]

/-- The packet is `pair originalInput encodedStack`. The frame combiner receives
`pair originalInput (pair encodedChild encodedParent)`. -/
def update (emptyBits combineBits : List Bool → List Bool) (b : Bool) (packet : List Bool) : List Bool :=
  let z := pairFst packet
  let xs := pairSnd packet
  let body := xs.drop 1
  if xs[0]?.getD false = true then
    if b then true :: pair (emptyBits z) body
    else if body = [] ∨ pairSnd body = [] then [false]
    else true :: pair (combineBits (pair z (pair (pairFst body) (pairFst (pairSnd body)))))
      (pairSnd (pairSnd body))
  else [false]

theorem update_encode (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : ∀ z, emptyBits z = code (empty z))
    (hcombine : ∀ z child parent,
      combineBits (pair z (pair (code child) (code parent))) = code (combine z child parent))
    (z : List Bool) (b : Bool) (state : Option (List σ)) :
    update emptyBits combineBits b (pair z (encode code state)) =
      encode code (TreeFold.step (empty z) (combine z) b state) := by
  cases state with
  | none => simp [update, encode, TreeFold.step]
  | some stack =>
      cases b with
      | true => simp [update, encode, TreeFold.step, stackBits, hempty]
      | false =>
          cases stack with
          | nil => simp [update, encode, TreeFold.step, stackBits]
          | cons child tail =>
              cases tail with
              | nil => simp [update, encode, TreeFold.step, stackBits]
              | cons parent rest =>
                  have hchild : pair (code child) (pair (code parent) (stackBits code rest)) ≠ [] := by
                    intro he
                    have hh := congrArg List.length he
                    simp at hh
                  have hparent : pair (code parent) (stackBits code rest) ≠ [] := by
                    intro he
                    have hh := congrArg List.length he
                    simp at hh
                  simp [update, encode, TreeFold.step, stackBits, hcombine, hchild, hparent]

theorem update_mem_FP {emptyBits combineBits : List Bool → List Bool}
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP) (b : Bool) :
    update emptyBits combineBits b ∈ FP := by
  have hx := pairSnd_mem_FP
  have hz := pairFst_mem_FP
  have hbody := drop_mem_FP hx (UnaryFn.const 1)
  have htail := mem_FP_comp hbody pairSnd_mem_FP
  have hrest := mem_FP_comp htail pairSnd_mem_FP
  have hchild := mem_FP_comp hbody pairFst_mem_FP
  have hparent := mem_FP_comp htail pairFst_mem_FP
  have hinput := mem_FP_pair hz (mem_FP_pair hchild hparent)
  have hmerged := mem_FP_comp hinput hcombine
  have hpop := mem_FP_comp (mem_FP_pair hmerged hrest) (cons_mem_FP true)
  have hpush := mem_FP_comp
    (mem_FP_pair (mem_FP_comp hz hempty) hbody) (cons_mem_FP true)
  have hbad :=
    ((FPPred.eq (UnaryFn.length hbody) (UnaryFn.const 0)).or
      (FPPred.eq (UnaryFn.length htail) (UnaryFn.const 0)))
  have hbad' : FPPred fun packet =>
      (pairSnd packet).drop 1 = [] ∨ pairSnd ((pairSnd packet).drop 1) = [] :=
    hbad.of_iff (by intro packet; simp only [List.length_eq_zero_iff, Function.comp_apply])
  cases b
  · exact (FPPred.getBit hx (UnaryFn.const 0)).ite_mem_FP
      (hbad'.ite_mem_FP (constFn_mem_FP [false]) hpop) (constFn_mem_FP [false])
  · exact (FPPred.getBit hx (UnaryFn.const 0)).ite_mem_FP hpush (constFn_mem_FP [false])

/-- Uniform polynomial-time execution, with the original input available to
every frame operation and a bound on every suffix's complete encoded stack. -/
theorem runEncoded_mem_FP (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP)
    (hempty_eq : ∀ z, emptyBits z = code (empty z))
    (hcombine_eq : ∀ z child parent,
      combineBits (pair z (pair (code child) (code parent))) = code (combine z child parent))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ z →
      (encode code (TreeFold.run (empty z) (combine z) t)).length ≤ bound z.length) :
    (fun z => encode code (TreeFold.run (empty z) (combine z) z)) ∈ FP := by
  have hinit : (fun z => encode code (some [empty z])) ∈ FP := by
    refine mem_FP_of_eq
      (mem_FP_comp (mem_FP_pair hempty (constFn_mem_FP [])) (cons_mem_FP true)) ?_
    intro z
    simp only [hempty_eq, encode, stackBits, Function.comp_apply]
  refine recFold_mem_FP_of_bound
    (g := fun z t => encode code (TreeFold.run (empty z) (combine z) t))
    (mem_FP_comp pairFst_mem_FP (update_mem_FP hempty hcombine false))
    (mem_FP_comp pairFst_mem_FP (update_mem_FP hempty hcombine true))
    hinit id_mem_FP id_mem_FP ?_ ?_ ?_ hbound hle
  · intro z
    rfl
  · intro z t
    simpa only [Function.comp_apply, pairFst_pair, id_eq, TreeFold.run_cons] using
      (update_encode empty combine code emptyBits combineBits hempty_eq hcombine_eq z false
        (TreeFold.run (empty z) (combine z) t)).symm
  · intro z t
    simpa only [Function.comp_apply, pairFst_pair, id_eq, TreeFold.run_cons] using
      (update_encode empty combine code emptyBits combineBits hempty_eq hcombine_eq z true
        (TreeFold.run (empty z) (combine z) t)).symm

theorem step_encode_length_le (empty : σ) (combine : σ → σ → σ)
    (code : σ → List Bool) (c : ℕ)
    (hgrowth : ∀ child parent, (code (combine child parent)).length ≤
      (code child).length + (code parent).length + c)
    (b : Bool) (state : Option (List σ)) :
    (encode code (TreeFold.step empty combine b state)).length ≤ (encode code state).length +
      (2 * (code empty).length + 2 * c + 2) := by
  cases state with
  | none => simp [TreeFold.step, encode]
  | some stack =>
      cases b with
      | true =>
          simp only [TreeFold.step, ite_true, encode_some_length, weight]
          omega
      | false =>
          cases stack with
          | nil => simp [TreeFold.step, encode, stackBits]
          | cons child tail =>
              cases tail with
              | nil => simp [TreeFold.step, encode, stackBits]; omega
              | cons parent rest =>
                  have hg := hgrowth child parent
                  simp only [TreeFold.step, Bool.false_eq_true, ite_false, encode_some_length, weight]
                  omega

theorem run_encode_length_le (empty : σ) (combine : σ → σ → σ)
    (code : σ → List Bool) (c : ℕ)
    (hgrowth : ∀ child parent, (code (combine child parent)).length ≤
      (code child).length + (code parent).length + c) (bits : List Bool) :
    (encode code (TreeFold.run empty combine bits)).length ≤
      2 * (code empty).length + 3 + bits.length * (2 * (code empty).length + 2 * c + 2) := by
  induction bits with
  | nil => simp [encode, stackBits]
  | cons b bits ih =>
      rw [TreeFold.run_cons]
      have hs := step_encode_length_le empty combine code c hgrowth b (TreeFold.run empty combine bits)
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A polynomial additive allowance per frame combination supplies the complete
stack bound automatically. Initial frame size is bounded by its `FP` certificate. -/
theorem runEncoded_mem_FP_of_additive (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP)
    (hempty_eq : ∀ z, emptyBits z = code (empty z))
    (hcombine_eq : ∀ z child parent,
      combineBits (pair z (pair (code child) (code parent))) = code (combine z child parent))
    {allowance : ℕ → ℕ} (hallowance : PolyBound allowance)
    (hgrowth : ∀ z child parent, (code (combine z child parent)).length ≤
      (code child).length + (code parent).length + allowance z.length) :
    (fun z => encode code (TreeFold.run (empty z) (combine z) z)) ∈ FP := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hempty
  let bound := fun n => 2 * p.eval n + 3 + n * (2 * p.eval n + 2 * allowance n + 2)
  have hbound : PolyBound bound :=
    (((PolyBound.const 2).mul (PolyBound.eval p)).add (PolyBound.const 3)).add
      (PolyBound.id.mul ((((PolyBound.const 2).mul (PolyBound.eval p)).add
        ((PolyBound.const 2).mul hallowance)).add (PolyBound.const 2)))
  refine runEncoded_mem_FP empty combine code emptyBits combineBits hempty hcombine
    hempty_eq hcombine_eq hbound (fun z t ht => ?_)
  have he : (code (empty z)).length ≤ p.eval z.length := by rw [← hempty_eq]; exact hp z
  have hs := run_encode_length_le (empty z) (combine z) code (allowance z.length) (hgrowth z) t
  have hd : 2 * (code (empty z)).length + 2 * allowance z.length + 2 ≤
      2 * p.eval z.length + 2 * allowance z.length + 2 := by omega
  have hm := Nat.mul_le_mul ht.length_le hd
  dsimp [bound]
  omega

/-- A simpler reference encoding can be used to bound all actual stack bytes. -/
theorem encode_length_le_mul (code reference : σ → List Bool) (factor : ℕ) (hf : 1 ≤ factor)
    (hcode : ∀ s, (code s).length ≤ factor * (reference s).length) (state : Option (List σ)) :
    (encode code state).length ≤ factor * (encode reference state).length := by
  have hw : ∀ stack : List σ, weight code stack ≤ factor * weight reference stack := by
    intro stack
    induction stack with
    | nil => simp [weight]
    | cons s rest ih =>
        have hc := hcode s
        simp only [weight]
        nlinarith
  cases state with
  | none => simp [encode, hf]
  | some stack =>
      rw [encode_some_length, encode_some_length]
      have hh := hw stack
      nlinarith

end LeanCanny.Encoding.DynamicTreeFold
