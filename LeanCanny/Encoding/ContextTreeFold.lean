/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.DynamicTreeFold

/-! # Native tree folds with input-dependent frame encodings

A captured parameter may affect every transformed subtree. Encoding that
subtree with the same captured parameter avoids requiring correctness between
frames encoded under different inputs. Complete intermediate stack bounds
remain explicit; this theorem does not infer FP from final output size.
-/
@[expose] public section
namespace LeanCanny.Encoding.DynamicTreeFold
open Brackets
variable {σ : Type*}

theorem update_encode_context (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : List Bool → σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : ∀ z, emptyBits z = code z (empty z))
    (hcombine : ∀ z child parent,
      combineBits (pair z (pair (code z child) (code z parent))) = code z (combine z child parent))
    (z : List Bool) (b : Bool) (state : Option (List σ)) :
    update emptyBits combineBits b (pair z (encode (code z) state)) =
      encode (code z) (TreeFold.step (empty z) (combine z) b state) := by
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
                  have hchild : pair (code z child) (pair (code z parent) (stackBits (code z) rest)) ≠ [] := by
                    intro he
                    have hh := congrArg List.length he
                    simp at hh
                  have hparent : pair (code z parent) (stackBits (code z) rest) ≠ [] := by
                    intro he
                    have hh := congrArg List.length he
                    simp at hh
                  simp [update, encode, TreeFold.step, stackBits, hcombine, hchild, hparent]


theorem runEncoded_mem_FP_context (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : List Bool → σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP)
    (hempty_eq : ∀ z, emptyBits z = code z (empty z))
    (hcombine_eq : ∀ z child parent,
      combineBits (pair z (pair (code z child) (code z parent))) = code z (combine z child parent))
    {bound : ℕ → ℕ} (hbound : PolyBound bound)
    (hle : ∀ z t, t <:+ z →
      (encode (code z) (TreeFold.run (empty z) (combine z) t)).length ≤ bound z.length) :
    (fun z => encode (code z) (TreeFold.run (empty z) (combine z) z)) ∈ FP := by
  have hinit : (fun z => encode (code z) (some [empty z])) ∈ FP := by
    refine mem_FP_of_eq
      (mem_FP_comp (mem_FP_pair hempty (constFn_mem_FP [])) (cons_mem_FP true)) ?_
    intro z
    simp only [hempty_eq, encode, stackBits, Function.comp_apply]
  let step := fun z acc bit => update emptyBits combineBits bit (pair z acc)
  have hp : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => pair p.1.1 p.1.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by fun_prop
  have hstep : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => step p.1.1 p.1.2 p.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by
    have hb := Turing.MultiTapeTM.ComputableTidilyInPolyTime.snd
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool
    exact (hb.cond ((update_mem_FP hempty hcombine true).comp hp)
      ((update_mem_FP hempty hcombine false).comp hp)).of_enc_eq
        fun p => by cases p.2 <;> rfl
  refine foldrEncodedWith_spec
    (fun state : List Bool × Option (List σ) => encode (code state.1) state.2) (step := step)
    (g := fun z t => (z,TreeFold.run (empty z) (combine z) t))
    id_mem_FP id_mem_FP hinit hstep ?_ (hbound.polyBounded (fun z : List Bool => z.length)) hle
  intro z t bit
  exact update_encode_context empty combine code emptyBits combineBits hempty_eq hcombine_eq z bit
    (TreeFold.run (empty z) (combine z) t)

theorem runEncoded_mem_FP_context_of_additive (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : List Bool → σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP)
    (hempty_eq : ∀ z, emptyBits z = code z (empty z))
    (hcombine_eq : ∀ z child parent,
      combineBits (pair z (pair (code z child) (code z parent))) = code z (combine z child parent))
    {allowance : ℕ → ℕ} (hallowance : PolyBound allowance)
    (hgrowth : ∀ z child parent, (code z (combine z child parent)).length ≤
      (code z child).length + (code z parent).length + allowance z.length) :
    (fun z => encode (code z) (TreeFold.run (empty z) (combine z) z)) ∈ FP := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hempty
  let bound := fun n => 2 * p.eval n + 3 + n * (2 * p.eval n + 2 * allowance n + 2)
  have hbound : PolyBound bound :=
    (((PolyBound.const 2).mul (PolyBound.eval p)).add (PolyBound.const 3)).add
      (PolyBound.id.mul ((((PolyBound.const 2).mul (PolyBound.eval p)).add
        ((PolyBound.const 2).mul hallowance)).add (PolyBound.const 2)))
  refine runEncoded_mem_FP_context empty combine code emptyBits combineBits hempty hcombine
    hempty_eq hcombine_eq hbound (fun z t ht => ?_)
  have he : (code z (empty z)).length ≤ p.eval z.length := by rw [← hempty_eq]; exact hp z
  have hs := run_encode_length_le (empty z) (combine z) (code z) (allowance z.length) (hgrowth z) t
  have hd : 2 * (code z (empty z)).length + 2 * allowance z.length + 2 ≤
      2 * p.eval z.length + 2 * allowance z.length + 2 := by omega
  have hm := Nat.mul_le_mul ht.length_le hd
  dsimp [bound]
  omega

end LeanCanny.Encoding.DynamicTreeFold
