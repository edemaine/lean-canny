/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphPointGlue
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdgeSymmetry
/-! # Actual raw and entire-point provider paths reverse and concatenate -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
set_option backward.isDefEq.respectTransparency false
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number

theorem raw_reachable_symm {c a b : List Bool} (H : RawReachable c a b) : RawReachable c b a := by
  let : Std.Symm FormulaSignSlotRadialProviderEdge.Adjacent :=
    ⟨fun _ _ => FormulaSignSlotRadialProviderEdge.symm⟩
  exact ⟨H.2.1,H.1,H.2.2.2.1,H.2.2.1,symm H.2.2.2.2⟩

theorem PointReachable.symm {c : List Bool} {p q : Fin (num c+4)→ℝ}
    (H : PointReachable c p q) : PointReachable c q p := by
  obtain ⟨a,b,ha,hb,hca,hcb,HA,HB,HP⟩ := H
  exact ⟨b,a,hb,ha,hcb,hca,HB,HA,raw_reachable_symm HP⟩

theorem PointReachable.trans {c : List Bool} {p q r : Fin (num c+4)→ℝ}
    (H : PointReachable c p q) (K : PointReachable c q r) : PointReachable c p r := point_reachable_trans H K

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
