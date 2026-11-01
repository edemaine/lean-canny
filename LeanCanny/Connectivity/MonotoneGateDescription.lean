/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.MonotoneGateGraph
public import LeanCanny.Connectivity.InputFP
public import LeanCanny.Encoding.BoundedFullWriter
/-! # The unique gate graph is an actual native bounded-source input -/
@[expose] public section
namespace LeanCanny.Connectivity.MonotoneGateGraph
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open MonotoneGateSource
open scoped Classical

def description (F : Family) (c : List Bool) : Description :=
  ⟨total F c,.eqZero (MonotoneGateSource.polynomial F c)⟩

theorem description_wellFormed (F : Family) (c : List Bool)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (description F c).WellFormed := by
  have H := polynomial_arity F c ha
  change (MonotoneGateSource.polynomial F c).arity≤total F c
  dsimp [total,base,outputDimension] at H ⊢
  omega

theorem description_dim_unary (F : Family) (hF : Access F) : UnaryFn (fun c => (description F c).dimension) :=
  (hF.dimension.add ((UnaryFn.const 2).mul hF.count)).add hF.count

theorem whole_record_FP (F : Family) (hF : Access F) :
    (fun c => (Input.whole (description F c)).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP (description_dim_unary F hF))
    (Codec.taggedOne_mem_FP 1 (polynomial_FP F hF))
  apply mem_FP_of_eq H
  intro c
  simp only [Codec.taggedOne_toBits,Codec.taggedTwo_toBits,Input.encode,Input.toData,description,Formula.toData]

theorem description_connected_iff (F : Family) (c : List Bool)
    (ha : ∀ i<F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (description F c).Connected ↔ IsPreconnected {x : Fin (base F c) → ℝ | rootValue F c x=0} := by
  have HW := description_wellFormed F c ha
  simp only [Description.Connected,HW,true_and]
  change IsPreconnected (ZeroSet F c) ↔ _
  have H := (zeroHomeomorph F c ha).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (zeroHomeomorph F c ha).surjective] at H
  have HL : IsPreconnected (ZeroSet F c) ↔ IsPreconnected (univ : Set (ZeroSet F c)) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  have HR : IsPreconnected {x : Fin (base F c) → ℝ | rootValue F c x=0} ↔
      IsPreconnected (univ : Set {x : Fin (base F c) → ℝ // rootValue F c x=0}) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  exact HL.trans (H.symm.trans HR.symm)

def readers (F : Family) (radius : List Bool → ℕ) : BoundedFullWriter.Readers where
  source c := (MonotoneGateSource.polynomial F c).toData.toBits
  dim c := total F c
  radius := radius

theorem readers_polyTime (F : Family) (hF : Access F) (radius : List Bool → ℕ) (hR : BinaryFn radius) :
    (readers F radius).PolyTime := ⟨polynomial_FP F hF,description_dim_unary F hF,hR⟩

theorem readers_scope (F : Family) (radius : List Bool → ℕ)
    (ha : ∀ c i, i<F.count c → (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    ∀ c, (TermView.term ((readers F radius).source c)).arity≤(readers F radius).dim c := by
  intro c
  rw [readers,TermView.term_toBits]
  exact description_wellFormed F c (ha c)

end LeanCanny.Connectivity.MonotoneGateGraph
