/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerSingularHeightCurves
public import LeanCanny.Encoding.FlatAffineShiftPrefixInput
public import LeanCanny.Encoding.FlatAffineJointPrefixChoice

/-! # Native newest-height indices recover exactly the original parent depth -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLastHeightRow
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def row (F : Inputs) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) : Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  FlatAffinePowerSingularHeightCurves.rowIndex F u (h u)

theorem row_val (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    (row F h u).val = F.depth u * stageWidth F u + arity F u + (h u).val + 1 := by
  have HE := FlatAffinePowerTower.multiplier_eq (n := arity F u)
    (FlatAffinePowerSingularHeightCurves.lastStage F u) (h u).succ
  have HV := congrArg Fin.val HE
  change (row F h u).val = F.depth u * stageWidth F u + (arity F u + ((h u).val + 1)) at HV
  omega

theorem row_unary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) : UnaryFn (fun u => (row F h u).val) :=
  (((hF.depth.mul (FlatAffineFullSourceTower.stageWidth_unary hF)).add
    (FlatAffineFullSourceTower.arity_unary hF)).add hh |>.add (UnaryFn.const 1)).of_eq (fun u => (row_val F h u).symm)

theorem ordinary (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    (row F h u).val < FlatAffineFullSourceTower.count (next F) u := by
  rw [row_val]
  have HH := (h u).isLt
  change F.depth u * stageWidth F u + arity F u + (h u).val + 1 < (F.depth u + 1) * stageWidth F u
  rw [Nat.add_mul, Nat.one_mul]
  change _ < F.depth u * stageWidth F u + (arity F u + (arity F u + 1))
  omega

theorem depth_eq (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    FlatAffineShiftPrefixInput.depth (next F) (row F h) u = F.depth u := by
  change (row F h u).val / stageWidth F u = F.depth u
  rw [row_val]
  have HH := (h u).isLt
  have HW : 0 < stageWidth F u := by change 0 < arity F u + (arity F u + 1); omega
  have HS : arity F u + (h u).val + 1 < stageWidth F u := by
    change _ < arity F u + (arity F u + 1)
    omega
  have HE : F.depth u * stageWidth F u + arity F u + (h u).val + 1 =
      (arity F u + (h u).val + 1) + stageWidth F u * F.depth u := by ac_rfl
  rw [HE, Nat.add_mul_div_left _ _ HW, Nat.div_eq_of_lt HS, Nat.zero_add]

theorem inputs_eq (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) :
    FlatAffineShiftPrefixInput.inputs (next F) (row F h) = F := by
  have HD : FlatAffineShiftPrefixInput.depth (next F) (row F h) = F.depth := funext (depth_eq F h)
  unfold FlatAffineShiftPrefixInput.inputs
  rw [HD]
  cases F
  rfl

theorem parentCone (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) :
    FlatAffinePowerPositive.ConeCertificate F :=
  FlatAffineCompleteRootStages.cone_prefix (next F) C F.depth
    (fun u => by change F.depth u ≤ F.depth u + 1; omega)

private theorem sampleInput_congr (F G : Inputs) (CF : FlatAffinePowerPositive.ConeCertificate F)
    (CG : FlatAffinePowerPositive.ConeCertificate G) (he : F = G) :
    FlatAffinePowerSampleInput.input F CF = FlatAffinePowerSampleInput.input G CG := by
  cases he
  rfl

theorem input_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) :
    FlatAffineShiftPrefixInput.input (next F) C (row F h) = FlatAffinePowerSampleInput.input F (parentCone F C) :=
  sampleInput_congr _ _ (FlatAffineShiftPrefixInput.cone (next F) C (row F h)) (parentCone F C) (inputs_eq F h)

theorem target_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) :
    FlatAffineJointPrefixChoice.target (next F) C (row F h) =
      SquareSampleInput.comp (FlatAffinePowerSampleInput.input F (parentCone F C)) FlatAffineJointPrefixChoice.original :=
  congrArg (fun I => SquareSampleInput.comp I FlatAffineJointPrefixChoice.original) (input_eq F C h)

end LeanCanny.Encoding.FlatAffineLastHeightRow
