/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralRowSpace
public import LeanCanny.Algebra.PaddedIntegralGeneratorSourceComp

/-! # Native monic-row readers through an original source-word map

The map rewrites only the source word. The actual algebra, polynomial and
fixed power schedule come from that source, while exponent queries and caller
moduli retain the native input record and its full space charge.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralRowBits
open LeanCanny.Encoding LeanCanny.Computation
open PaddedIntegralGeneratorSource
set_option backward.isDefEq.respectTransparency false

theorem polynomial_comp (S : Source) (f : List Bool→List Bool) (cap : List Bool→ℕ) (q : List Bool) :
    polynomial (S.comp f) (cap ∘ f) q=polynomial S cap (f q) := rfl

theorem comp_row_evaluator (S : Source) (f : List Bool→List Bool) (cap V : List Bool→ℕ)
    (target modulus : List Bool→List Bool) (hf : f∈FP)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>S.arity (f q)+1) V
      (fun q=>polynomial S cap (f q)) target modulus) := by
  have H := row_evaluator (S.comp f) (cap ∘ f) V target modulus (hc.comp hf) (ha.comp hf) (hw.comp hf)
    hV ht hm (comp_evaluator S f hf E)
  exact H.congr (funext fun q=>by
    simp only [FixedWidthRowBits.value,polynomial_comp]
    rfl)

end LeanCanny.Algebra.PaddedIntegralRowBits
