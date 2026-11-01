/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerModularRecursiveStage

/-! # Native context pullback of actual modular matrix powers -/

@[expose] public section
namespace LeanCanny.Algebra.MatrixPower
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

noncomputable def ModularFamily.requery (F : ModularFamily) (f : List Bool → List Bool) : ModularFamily where
  dimension c := F.dimension (f c)
  modulus c := F.modulus (f c)
  exponent c := F.exponent (f c)
  row c := F.row (f c)
  col c := F.col (f c)
  matrix c := F.matrix (f c)
  modulus_ne_zero c := F.modulus_ne_zero (f c)

def ModularAccess.requery (F : ModularFamily) (a : ModularAccess F) (f : List Bool → List Bool) :
    ModularAccess (F.requery f) where
  dimension := a.dimension ∘ f
  modulus := a.modulus ∘ f
  exponent := a.exponent ∘ f
  row := a.row ∘ f
  col := a.col ∘ f
  entry p := a.entry (pair (f (pairFst p)) (pairSnd p))
  dimension_eq c := a.dimension_eq (f c)
  modulus_eq c := a.modulus_eq (f c)
  exponent_eq c := a.exponent_eq (f c)
  row_eq c := a.row_eq (f c)
  col_eq c := a.col_eq (f c)
  entry_eq c i j := by
    simp only [pairFst_pair, pairSnd_pair]
    exact a.entry_eq (f c) i j

theorem ModularAccess.requery_controls (F : ModularFamily) (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (f : List Bool → List Bool) (hf : f ∈ FP) :
    (a.requery F f).ControlsPolyTime :=
  ⟨mem_FP_comp (f := f) (g := a.dimension) hf ha.dimension,
    mem_FP_comp (f := f) (g := a.modulus) hf ha.modulus,
    mem_FP_comp (f := f) (g := a.exponent) hf ha.exponent,
    mem_FP_comp (f := f) (g := a.row) hf ha.row,
    mem_FP_comp (f := f) (g := a.col) hf ha.col⟩

theorem ModularFamily.requery_value (F : ModularFamily) (f : List Bool → List Bool) (c : List Bool) :
    (F.requery f).value c = F.value (f c) := rfl

end LeanCanny.Algebra.MatrixPower
