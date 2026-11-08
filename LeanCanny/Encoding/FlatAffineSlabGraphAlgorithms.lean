/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraph
public import LeanCanny.Computation.ImplicitGraphPSPACE

/-! # Native reachability algorithms for the concrete slab graph

The graph's own native validity, equality, and attachment computations supply
all oracle calls to the implicit graph algorithm. Vertex widths come from the
original source. Geometric identification of the assembled cover remains a
separate proof; these languages describe the explicit bit graph.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraph
open LeanCanny.Algebra LeanCanny.Computation Turing.MultiTapeTM
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w : List Bool) : Bool :=
  decide (pair c w ∈ validLanguage F cone height)
noncomputable def edge (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c w v : List Bool) : Bool :=
  decide (pair c (pair w v) ∈ edgeLanguage F cone height)

theorem valid_computable {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    ComputableInPolySpace (fun p : List Bool × List Bool => valid F cone height p.1 p.2)
      (encPair encBits encBits) encBool := by
  have C := ComputableTidilyInPolyTime.fst encBits encBits
  have W := ComputableTidilyInPolyTime.snd encBits encBits
  exact (validDecider h cone height hh).computable.comp (.of_tidyPolyTime (pair_computable C W))

theorem edge_computable {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    ComputableInPolySpace (fun p : List Bool × List Bool × List Bool => edge F cone height p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have C := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have R := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  exact (edgeDecider h cone height hh).computable.comp (.of_tidyPolyTime (pair_computable C (pair_computable R.fst' R.snd')))

noncomputable def connectedLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {c | ImplicitGraph.Connected (edge F cone height c) (valid F cone height c) (FlatAffineSlabGraphCodes.width F cone height c)}

theorem connectedDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (connectedLanguage F cone height) := by
  apply SpaceDecider.of_computable (ImplicitGraph.connected_computable (edge_computable h cone height hh)
    (valid_computable h cone height hh) (FlatAffineSlabGraphCodes.width_unary h cone height hh))
  intro c
  simp only [connectedLanguage, Set.mem_ofPred_eq, decide_eq_true_eq]

theorem connected_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : connectedLanguage F cone height ∈ PSPACE :=
  (connectedDecider h cone height hh).mem_PSPACE

theorem reachableDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    {src dst : List Bool → List Bool} (hs : SpaceFunction src) (hd : SpaceFunction dst)
    (hsrc : ∀ c, (src c).length = FlatAffineSlabGraphCodes.width F cone height c)
    (hdst : ∀ c, (dst c).length = FlatAffineSlabGraphCodes.width F cone height c) :
    SpaceDecider {c | ImplicitGraph.Reachable (edge F cone height c) (valid F cone height c)
      (FlatAffineSlabGraphCodes.width F cone height c) (src c) (dst c)} := by
  apply SpaceDecider.of_computable (ImplicitGraph.reachable_computable (edge_computable h cone height hh)
    (valid_computable h cone height hh) (FlatAffineSlabGraphCodes.width_unary h cone height hh)
    hs.computable hd.computable hsrc hdst)
  intro c
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq]

end LeanCanny.Encoding.FlatAffineSlabGraph
