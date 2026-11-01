/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FiniteSlabBitCover

/-! # Native algorithms for the assembled recursive slab cover

The global graph routines are derived from local slab graph routines and
endpoint-fiber intersection routines. The number of slabs may be exponential;
only the slab tag width and local vertex width must be unary computable.
Component membership packs an original local point locator into the global
record, and applies guarded reachability without an additional global oracle.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FiniteSlabBitCover
open Set LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open FiniteSlabGraph
open scoped Classical

section Algorithms
variable {Y : List Bool → Type} [∀ c, TopologicalSpace (Y c)]
  {n s w : List Bool → ℕ}
  (p : (c : List Bool) → Y c → ℝ) (cut : List Bool → ℕ → ℝ)
  (localEdge touch : List Bool → ℕ → List Bool → List Bool → Bool)
  (localValid : List Bool → ℕ → List Bool → Bool)
  (C : ∀ (c : List Bool) (i : Fin (n c + 1)), BitPathCover
    (p c ⁻¹' Icc (cut c i.val) (cut c (i.val + 1))) (w c)
      (localEdge c i.val) (localValid c i.val))
  (htouch : ∀ c (i j : Fin (n c + 1)), i.val + 1 = j.val → ∀ u v : Vertex (w c),
    touch c i.val u.val v.val = true ↔
      ∃ z : p c ⁻¹' {cut c (i.val + 1)},
        z.val ∈ imagePiece (p c) (cut c) (localEdge c) (localValid c) (C c) i u ∧
        z.val ∈ imagePiece (p c) (cut c) (localEdge c) (localValid c) (C c) j v)
  (hp : ∀ c, Continuous (p c))
  (hcut : ∀ c, StrictMonoOn (cut c) (Icc 0 (n c + 1)))
  (hbound : ∀ c x, p c x ∈ Icc (cut c 0) (cut c (n c + 1)))
  (hcap : ∀ c, n c + 1 ≤ 2 ^ s c)
  (hn : BinaryFn n) (hs : UnaryFn s) (hw : UnaryFn w)
  (he : ComputableTidilyInPolySpace
    (fun q : List Bool × ℕ × List Bool × List Bool => localEdge q.1 q.2.1 q.2.2.1 q.2.2.2)
    (encPair encBits (encPair encNat (encPair encBits encBits))) encBool)
  (hv : ComputableTidilyInPolySpace
    (fun q : List Bool × ℕ × List Bool => localValid q.1 q.2.1 q.2.2)
    (encPair encBits (encPair encNat encBits)) encBool)
  (ht : ComputableTidilyInPolySpace
    (fun q : List Bool × ℕ × List Bool × List Bool => touch q.1 q.2.1 q.2.2.1 q.2.2.2)
    (encPair encBits (encPair encNat (encPair encBits encBits))) encBool)

local notation "B" => (fun c => bitCover (p c) (cut c) (localEdge c) (localValid c)
  (C c) (touch c) (htouch c) (hp c) (hcut c) (hbound c) (hcap c))

include C htouch hp hcut hbound hcap hn hs hw he hv ht in
/-- Native whole-space connectivity is obtained from the assembled geometric
cover and its locally dispatched graph, rather than an assumed global test. -/
theorem connected_computable :
    ComputableTidilyInPolySpace
      (fun c => decide (IsPreconnected (univ : Set (Y c)))) encBits encBool := by
  classical
  exact BitPathCover.connected_computable B
    (FiniteSlabGraph.edge_computable (hn.add (BinaryFn.const 1)) hs he ht)
    (FiniteSlabGraph.valid_computable (hn.add (BinaryFn.const 1)) hs hv) (hs.add hw)

include C htouch hp hcut hbound hcap hn hs hw he hv ht in
/-- A local recursive point locator is sufficient for membership in any global
component record. The component record itself may have an invalid slab tag. -/
theorem component_membership_computable
    {label : List Bool → List Bool} {srcSlab : List Bool → ℕ} {srcWord : List Bool → List Bool}
    (hl : ComputableTidilyInPolySpace label encBits encBits)
    (hi : ComputableTidilyInPolySpace srcSlab encBits encNat)
    (hu : ComputableTidilyInPolySpace srcWord encBits encBits)
    (hlabel : ∀ c, (label c).length = s c + w c)
    (hindex : ∀ c, srcSlab c < n c + 1)
    (hword : ∀ c, (srcWord c).length = w c)
    {x : (c : List Bool) → Y c}
    (hx : ∀ c, x c ∈ imagePiece (p c) (cut c) (localEdge c) (localValid c) (C c)
      ⟨srcSlab c, hindex c⟩ ⟨srcWord c, hword c⟩) :
    ComputableTidilyInPolySpace
      (fun c => decide (x c ∈ (B c).toFrontierCover.componentCover.piece
        ⟨label c, hlabel c⟩)) encBits encBool := by
  classical
  have hsrc (c) : (encode (s c) (srcSlab c) (srcWord c)).length = s c + w c := by
    simp [hword c]
  have hmem (c) : x c ∈ (B c).piece
      ⟨encode (s c) (srcSlab c) (srcWord c), hsrc c⟩ := by
    change x c ∈ piece (p c) (cut c) (localEdge c) (localValid c) (C c)
      ⟨encode (s c) (srcSlab c) (srcWord c), hsrc c⟩
    rw [piece_of_tag (p c) (cut c) (localEdge c) (localValid c) (C c) _
      ⟨srcSlab c, hindex c⟩ (tag_encode _ _ _ ((hindex c).trans_le (hcap c)))]
    have hlocal : localWord (⟨encode (s c) (srcSlab c) (srcWord c), hsrc c⟩ :
        Vertex (s c + w c)) = ⟨srcWord c, hword c⟩ :=
      Subtype.ext (payload_encode _ _ _)
    rw [hlocal]
    exact hx c
  exact BitFrontierCover.component_membership_computable (fun c => (B c).toFrontierCover)
    (FiniteSlabGraph.edge_computable (hn.add (BinaryFn.const 1)) hs he ht)
    (FiniteSlabGraph.valid_computable (hn.add (BinaryFn.const 1)) hs hv) (hs.add hw)
    hl (encode_computable hs hi hu) hlabel hsrc hmem

end Algorithms
end LeanCanny.Connectivity.FiniteSlabBitCover
