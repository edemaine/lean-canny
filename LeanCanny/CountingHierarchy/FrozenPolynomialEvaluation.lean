/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FinitePolynomialBlocks

/-! # Source evaluation with a frozen parameter block at the same counting level -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

namespace Controlled

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

noncomputable def frozenEvaluate (C : Controlled P enc a) (p : α → ℕ) (params : α → List ℕ)
    (q : α × List ℕ) : ℕ := C.evaluate (q.1, p q.1, joinedPoint (n q.1) (m q.1) q.2 (params q.1))

/-- Padding both blocks makes the source query correct even when either input
point list is short or overlong. The original source oracle remains fixed. -/
theorem frozenEvaluate_mem (C : Controlled P enc a)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    {p : α → ℕ} {params : α → List ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hparams : ComputableInPolyTime params enc (encList encNat)) :
    C.frozenEvaluate p params ∈ CountingFunction a (encPair enc (encList encNat)) encNat := by
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hpoint := joinedPoint_polyTime (hn.comp hf) (hm.comp hf)
    (ComputableInPolyTime.snd enc (encList encNat)) (hparams.comp hf)
  have hquery : ComputableInPolyTime (fun q : α × List ℕ =>
      (q.1, p q.1, joinedPoint (n q.1) (m q.1) q.2 (params q.1)))
      (encPair enc (encList encNat)) (encEvaluation enc) := by
    simpa only [Function.comp_apply] using hf.prod ((hp.comp hf).prod hpoint)
  exact CountingFunction.preprocess (g := fun q : α × List ℕ =>
    (q.1, p q.1, joinedPoint (n q.1) (m q.1) q.2 (params q.1))) C.evaluate_mem hquery

theorem frozenEvaluate_cast (C : Controlled P enc a) (p : α → ℕ) (params : α → List ℕ) (w : α)
    (hp : (p w).Prime) (hcut : C.cutoff w < p w) (y : List ℕ) :
    (C.frozenEvaluate p params (w, y) : ZMod (p w)) =
      MvPolynomial.eval (fun i : Fin (n w) => (y[i.val]?.getD 0 : ZMod (p w)))
        (specializeFinitePolynomial (P w) (Int.castRingHom (ZMod (p w)))
          (fun i : Fin (m w) => ((params w)[i.val]?.getD 0 : ZMod (p w)))) := by
  let : NeZero (p w) := ⟨hp.ne_zero⟩
  rw [frozenEvaluate, C.evaluate_eq w (p w) _ hp hcut]
  simp only [evaluation, ZMod.natCast_zmod_val]
  exact eval_joinedPoint (P w) (Int.castRingHom (ZMod (p w))) y (params w)

end Controlled

end LeanCanny.CountingHierarchy
