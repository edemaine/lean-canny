/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSystem
public import LeanCanny.Algebra.MacaulayShiftedKoszul
public import LeanCanny.Algebra.MacaulayReducedCount

/-! # A nonzero Koszul relation for the actual shifted tube system

The projection degree is one and all other spatial degrees have the proved
uniform bound. Two distinct coordinates admit a compatible Koszul multiplier
at the Macaulay level. Their shifted inputs give a nonzero finite kernel vector
of the full graded multiplication matrix without new algebraic hypotheses.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeMacaulayKoszul
open LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

theorem exists_nonzero_relation (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    ∃ v : Macaulay.MultiplierIndex (MacaulayBits.Degrees (TubeCleared.layout source) c)
        (TubeCleared.matrixWidth (source c)) → Polynomial (Polynomial (Polynomial ℤ)),
      v ≠ 0 ∧ Matrix.vecMul v
        (Macaulay.fullMatrix
          (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
            (MacaulayBits.Degrees (TubeCleared.layout source) c))
          (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))) = 0 := by
  let ds : Fin (TubeParameter.spatialCount (source c)) → ℕ := MacaulayBits.Degrees (TubeCleared.layout source) c
  let W := TubeCleared.matrixWidth (source c)
  have hS : 3 ≤ TubeParameter.spatialCount (source c) := by
    unfold TubeParameter.spatialCount TubeProjectionEncoding.pointCount TubeEncoding.constraintCount
    omega
  let i : Fin (TubeParameter.spatialCount (source c)) := ⟨0, by omega⟩
  let j : Fin (TubeParameter.spatialCount (source c)) := ⟨1, by omega⟩
  let k : Fin (TubeParameter.spatialCount (source c)) := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change (0 : ℕ) = 1 at hv
    omega
  have hkj : k ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change (2 : ℕ) = 1 at hv
    omega
  have hD : 2 ≤ TubeIndexed.degreeBound (source c) := by
    unfold TubeIndexed.degreeBound
    omega
  have hpos (a : Fin (TubeParameter.spatialCount (source c))) : 0 < ds a := TubeCleared.degree_pos source c a.val
  have hL := Macaulay.level_eq_otherSum ds hpos j
  have hterm : ds k - 1 ≤ Macaulay.otherSum j (fun a => ds a - 1) :=
    Finset.single_le_sum (f := fun a => ds a - 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
  change Macaulay.level ds = TubeIndexed.degreeBound (source c) + Macaulay.otherSum j (fun a => ds a - 1) at hL
  change TubeIndexed.degreeBound (source c) - 1 ≤ Macaulay.otherSum j (fun a => ds a - 1) at hterm
  have hpair : ds i + ds j ≤ Macaulay.level ds := by
    change 1 + TubeIndexed.degreeBound (source c) ≤ Macaulay.level ds
    omega
  let m : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ :=
    Finsupp.single i (Macaulay.level ds - ds i - ds j)
  have hm : m.degree + ds i + ds j = Macaulay.level ds := by
    rw [show m.degree = Macaulay.level ds - ds i - ds j from Finsupp.degree_single _ _]
    omega
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  let p := TubeBivariate.rows source active n d ell c
  have hp := TubeBivariate.rows_homogeneous source active n d ell c
  refine ⟨Macaulay.sourceCoefficients (Macaulay.koszulMultipliers (Macaulay.subtractiveSystem p ds) i j m) ds W, ?_, ?_⟩
  · exact Macaulay.subtractive_koszul_coefficients_ne_zero p ds W hp hW i j hij m hm
  · exact Macaulay.subtractive_koszul_vecMul_eq_zero p ds W hp hW i j hij m hm

end LeanCanny.ETR.TubeMacaulayKoszul
