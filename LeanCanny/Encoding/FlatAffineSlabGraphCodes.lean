/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointIncidenceQuery

/-! # Bounded native records for a slab attachment graph

Context `((frame, gap), ((left height, left sample), (right height, right sample)))`
supplies both checked attachment queries. A two-bit tag selects a short branch
descriptor or a left/right endpoint marker. Unused payload bits may duplicate
pieces; they do not denote additional points or branches.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphCodes
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (c : List Bool) : List Bool := pairFst (pairFst c)
def gapWord (c : List Bool) : List Bool := pairSnd (pairFst c)
def side (right : Bool) (c : List Bool) : List Bool := if right then pairSnd (pairSnd c) else pairFst (pairSnd c)
def endpointWord (right : Bool) (c : List Bool) : List Bool := pairFst (side right c)
def sampleWord (right : Bool) (c : List Bool) : List Bool := pairSnd (side right c)
theorem source_FP : source ∈ FP := by polytime [source]
theorem gapWord_FP : gapWord ∈ FP := by polytime [gapWord]
theorem endpointWord_FP (right : Bool) : endpointWord right ∈ FP := by cases right <;> polytime [endpointWord, side]
theorem sampleWord_FP (right : Bool) : sampleWord right ∈ FP := by cases right <;> polytime [sampleWord, side]

noncomputable def jointWidth (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source c)
theorem jointWidth_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (jointWidth F cone height) :=
  (FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp source_FP

noncomputable def descriptorWidth (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) : ℕ :=
  FlatAffineEndpointFiniteSide.originalCount F (source c) * (jointWidth F cone height c + 1)
theorem descriptorWidth_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (descriptorWidth F cone height) :=
  ((FlatAffineEndpointFiniteSide.originalCount_unary h).comp source_FP).mul
    ((jointWidth_unary h cone height hh).add (UnaryFn.const 1))

noncomputable def width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) : ℕ :=
  2 + descriptorWidth F cone height c + jointWidth F cone height c
theorem width_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (width F cone height) :=
  ((UnaryFn.const 2).add (descriptorWidth_unary h cone height hh)).add (jointWidth_unary h cone height hh)

def kind (w : List Bool) : ℕ := Nat.fromBitsLE (w.take 2)
theorem kind_binary : BinaryFn kind := BinaryFn.fromBits (take_mem_FP id_mem_FP (UnaryFn.const 2))
def payload (w : List Bool) : List Bool := w.drop 2
theorem payload_FP : payload ∈ FP := drop_mem_FP id_mem_FP (UnaryFn.const 2)
noncomputable def branchPayload (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  (payload (pairSnd q)).take (descriptorWidth F cone height (pairFst q))
noncomputable def markerPayload (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  (payload (pairSnd q)).take (jointWidth F cone height (pairFst q))
theorem branchPayload_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : branchPayload F cone height ∈ FP :=
  take_mem_FP (mem_FP_comp pairSnd_mem_FP payload_FP) ((descriptorWidth_unary h cone height hh).comp pairFst_mem_FP)
theorem markerPayload_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : markerPayload F cone height ∈ FP :=
  take_mem_FP (mem_FP_comp pairSnd_mem_FP payload_FP) ((jointWidth_unary h cone height hh).comp pairFst_mem_FP)

noncomputable def branchQuery (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  pair (pair (source (pairFst q)) (pair (sampleWord false (pairFst q)) (gapWord (pairFst q)))) (branchPayload F cone height q)
noncomputable def markerQuery (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (q : List Bool) : List Bool :=
  pair (pair (source (pairFst q)) (endpointWord right (pairFst q))) (markerPayload F cone height q)
theorem branchQuery_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : branchQuery F cone height ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := source) pairFst_mem_FP source_FP)
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := sampleWord false) pairFst_mem_FP (sampleWord_FP false))
      (mem_FP_comp (f := pairFst) (g := gapWord) pairFst_mem_FP gapWord_FP)))
    (branchPayload_FP h cone height hh)
theorem markerQuery_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) : markerQuery F cone height right ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := source) pairFst_mem_FP source_FP)
    (mem_FP_comp (f := pairFst) (g := endpointWord right) pairFst_mem_FP (endpointWord_FP right)))
    (markerPayload_FP h cone height hh)

def leftVertex (r : List Bool) : List Bool := pair (pairFst r) (pairFst (pairSnd r))
def rightVertex (r : List Bool) : List Bool := pair (pairFst r) (pairSnd (pairSnd r))
theorem leftVertex_FP : leftVertex ∈ FP := by polytime [leftVertex]
theorem rightVertex_FP : rightVertex ∈ FP := by polytime [rightVertex]
def swap (r : List Bool) : List Bool := pair (pairFst r) (pair (pairSnd (pairSnd r)) (pairFst (pairSnd r)))
theorem swap_FP : swap ∈ FP := by polytime [swap]

noncomputable def markerEqualityQuery (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (r : List Bool) : List Bool :=
  pair (pair (source (pairFst r)) (endpointWord side (pairFst r)))
    (pair (markerPayload F cone height (leftVertex r)) (markerPayload F cone height (rightVertex r)))
theorem markerEqualityQuery_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (side : Bool) :
    markerEqualityQuery F cone height side ∈ FP := by
  have L := mem_FP_comp leftVertex_FP (markerPayload_FP h cone height hh)
  have R := mem_FP_comp rightVertex_FP (markerPayload_FP h cone height hh)
  have S := mem_FP_comp pairFst_mem_FP source_FP
  have A := mem_FP_comp pairFst_mem_FP (endpointWord_FP side)
  exact mem_FP_pair (mem_FP_pair S A) (mem_FP_pair L R)

noncomputable def attachmentQuery (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (r : List Bool) : List Bool :=
  FlatAffineEndpointIncidenceQuery.record (source (pairFst r)) (endpointWord side (pairFst r))
    (sampleWord side (pairFst r)) (gapWord (pairFst r))
    (branchPayload F cone height (leftVertex r)) (markerPayload F cone height (rightVertex r))
theorem attachmentQuery_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (side : Bool) : attachmentQuery F cone height side ∈ FP := by
  have B := mem_FP_comp leftVertex_FP (branchPayload_FP h cone height hh)
  have M := mem_FP_comp rightVertex_FP (markerPayload_FP h cone height hh)
  have S := mem_FP_comp pairFst_mem_FP source_FP
  have A := mem_FP_comp pairFst_mem_FP (endpointWord_FP side)
  have T := mem_FP_comp pairFst_mem_FP (sampleWord_FP side)
  have G := mem_FP_comp pairFst_mem_FP gapWord_FP
  exact mem_FP_pair (mem_FP_pair S (mem_FP_pair A T)) (mem_FP_pair (mem_FP_pair G B) M)

attribute [local irreducible] jointWidth descriptorWidth width

noncomputable def branchNode (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c d : List Bool) : List Bool :=
  [false, false] ++ d ++ List.replicate (jointWidth F cone height c) false
noncomputable def markerNode (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (c w : List Bool) : List Bool :=
  (if right then [false, true] else [true, false]) ++ w ++ List.replicate (descriptorWidth F cone height c) false

theorem branchNode_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    (fun q => branchNode F cone height (pairFst q) (pairSnd q)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP [false, false]) pairSnd_mem_FP)
    (((jointWidth_unary h cone height hh).comp pairFst_mem_FP).replicate_mem_FP false)
theorem markerNode_FP {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    (fun q => markerNode F cone height right (pairFst q) (pairSnd q)) ∈ FP :=
  appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP _) pairSnd_mem_FP)
    (((descriptorWidth_unary h cone height hh).comp pairFst_mem_FP).replicate_mem_FP false)

theorem branchNode_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c d : List Bool) (hd : d.length = descriptorWidth F cone height c) :
    (branchNode F cone height c d).length = width F cone height c := by
  simp only [branchNode, List.length_append, List.length_cons, List.length_nil, List.length_replicate, hd, width]
theorem markerNode_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (c w : List Bool) (hw : w.length = jointWidth F cone height c) :
    (markerNode F cone height right c w).length = width F cone height c := by
  cases right <;> simp only [markerNode, Bool.false_eq_true, ite_false, ite_true, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate, hw, width] <;> omega

theorem branchNode_kind (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c d : List Bool) : kind (branchNode F cone height c d) = 0 := rfl
theorem markerNode_kind (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (c w : List Bool) :
    kind (markerNode F cone height right c w) = if right then 2 else 1 := by cases right <;> rfl

theorem branchNode_payload (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c d : List Bool) (hd : d.length = descriptorWidth F cone height c) :
    branchPayload F cone height (pair c (branchNode F cone height c d)) = d := by
  simp only [branchPayload, pairFst_pair, pairSnd_pair, payload, branchNode,
    List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [← hd, List.take_left]
theorem markerNode_payload (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (c w : List Bool) (hw : w.length = jointWidth F cone height c) :
    markerPayload F cone height (pair c (markerNode F cone height right c w)) = w := by
  cases right <;> simp only [markerPayload, pairFst_pair, pairSnd_pair, payload, markerNode,
    Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero] <;>
    rw [← hw, List.take_left]

theorem attachmentQuery_nodes (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c d w : List Bool)
    (hd : d.length = descriptorWidth F cone height c) (hw : w.length = jointWidth F cone height c) :
    attachmentQuery F cone height side (pair c (pair (branchNode F cone height c d) (markerNode F cone height side c w))) =
      FlatAffineEndpointIncidenceQuery.record (source c) (endpointWord side c) (sampleWord side c) (gapWord c) d w := by
  simp only [attachmentQuery, leftVertex, rightVertex, pairFst_pair, pairSnd_pair,
    branchNode_payload F cone height c d hd, markerNode_payload F cone height side c w hw]

end LeanCanny.Encoding.FlatAffineSlabGraphCodes
