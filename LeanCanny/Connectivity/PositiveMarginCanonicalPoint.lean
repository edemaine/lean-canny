/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginEndpointSemantics
public import LeanCanny.Connectivity.PositiveMarginValues
/-! # Every old singleton has exactly one full margin endpoint, even outside the open source -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginGraph
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def point (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) : Fin (PositiveMarginSource.total F c) → ℝ :=
  appendHomeomorph (F.dimension c+F.count c) (PositiveMarginValues.full F c x,
    reciprocalValue ((PositiveMarginSource.root F c).eval (Formula.extend (PositiveMarginValues.full F c x))))

theorem projection_full (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) :
    TriangularContinuousGraph.projection (F.dimension c) (F.count c) (PositiveMarginValues.full F c x)=x := by
  funext i
  exact TriangularContinuousGraph.old _ _ x _ i

theorem point_old (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (i : Fin (F.dimension c)) :
    point F c x ⟨i.val,by have HI:=i.isLt; unfold PositiveMarginSource.total; omega⟩=x i := by
  unfold point
  rw [appendHomeomorph_apply]
  change Fin.append (PositiveMarginValues.full F c x) _ (Fin.castAdd 1 (Fin.castAdd (F.count c) i))=x i
  rw [Fin.append_left]
  exact TriangularContinuousGraph.old _ _ x _ i

theorem point_endpoint (F : Family) (c : List Bool) (s : Formula) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (x : Fin (F.dimension c) → ℝ) (hx : s.Holds (Formula.extend x)) :
    (PositiveMarginSource.endpoint F s c).Holds (Formula.extend (point F c x)) := by
  unfold point
  rw [appendHomeomorph_apply,endpoint_append F c s hs ha,projection_full]
  exact ⟨hx,TriangularContinuousGraph.equations _ _ x _,rfl⟩

theorem endpoint_denotes (F : Family) (c : List Bool) (s : Formula)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c)
    (x : Fin (F.dimension c) → ℝ) (hs : Denotes (F.dimension c) s x) :
    Denotes (PositiveMarginSource.total F c) (PositiveMarginSource.endpoint F s c) (point F c x) := by
  refine ⟨PositiveMarginSource.endpoint_arity F s c hs.1 ha,?_⟩
  intro y
  constructor
  · intro HY
    let E:=appendHomeomorph (F.dimension c+F.count c)
    let z:=E.symm y
    have HZ : E z=y := E.apply_symm_apply y
    have HC := (endpoint_append F c s hs.1 ha z.1 z.2).mp (show
        (PositiveMarginSource.endpoint F s c).Holds (Formula.extend (Fin.append z.1 (fun _ : Fin 1 => z.2))) by
      rw [← appendHomeomorph_apply, HZ]
      exact HY)
    have HX : TriangularContinuousGraph.projection (F.dimension c) (F.count c) z.1=x := (hs.2 _).mp HC.1
    have HU:=TriangularContinuousGraph.unique (F.dimension c) (gate F c) (F.count c) ⟨z.1,HC.2.1⟩
    change PositiveMarginValues.full F c (TriangularContinuousGraph.projection (F.dimension c) (F.count c) z.1)=z.1 at HU
    rw [HX] at HU
    have HR : z.2=reciprocalValue ((PositiveMarginSource.root F c).eval (Formula.extend (PositiveMarginValues.full F c x))) := by
      rw [HU]
      exact HC.2.2
    calc
      y=E z := HZ.symm
      _=point F c x := congrArg E (Prod.ext HU.symm HR)
  · rintro rfl
    exact point_endpoint F c s hs.1 ha x ((hs.2 x).mpr rfl)

end LeanCanny.Connectivity.PositiveMarginGraph
