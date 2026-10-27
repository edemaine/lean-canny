/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OrderedRealCellCover
public import LeanCanny.Encoding.BoundedAlgebraicSliceRootProductCellLanguage

/-! # Constructed finite sign-invariant covers of algebraic slices

The native root product determines every point cell and gap, including rays
and the empty-root case. All original factor signs are constant on every
cell. Any predicate of their sign vector therefore has a finite accessible
cover of its actual real solution set, with an explicit label-size bound.
The graph transfer is proved here; native incidence is constructed in
`AlgebraicSliceCellAdjacency`.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellCover
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open Encoding.BoundedFullWriter Encoding.BoundedAlgebraicSlice
open scoped Classical

noncomputable def roots (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : Finset ℝ :=
  (BoundedAlgebraicSliceRootProduct.polynomial P Q u).roots.toFinset

abbrev Index (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :=
  Geometry.OrderedRealCells.Index (roots P Q u)

noncomputable def piece (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : Index P Q u → Set ℝ :=
  Geometry.OrderedRealCells.piece (roots P Q u)

noncomputable def signVector (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (x : ℝ) :
    Fin (Q.count (pairFst u)) → SignType := fun i => SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval x)

theorem sign_constant (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Index P Q u) (x : ℝ) (hx : x ∈ piece P Q u i) (y : ℝ) (hy : y ∈ piece P Q u i) :
    signVector P Q u x = signVector P Q u y := by
  cases i with
  | inl i =>
    change x ∈ ({Geometry.OrderedRealCells.root (roots P Q u) i} : Set ℝ) at hx
    change y ∈ ({Geometry.OrderedRealCells.root (roots P Q u) i} : Set ℝ) at hy
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  | inr k =>
    apply funext
    intro j
    by_cases hz : BoundedAlgebraicSliceIndexed.value P Q u j.val = 0
    · simp only [signVector, hz, Polynomial.eval_zero, sign_zero]
    · have hn : ∀ z ∈ Geometry.OrderedRealCells.gap (roots P Q u) k,
          (BoundedAlgebraicSliceIndexed.value P Q u j.val).eval z ≠ 0 := by
        intro z hzk hzg
        have hzr : z ∈ (BoundedAlgebraicSliceIndexed.value P Q u j.val).roots.toFinset :=
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hz).mpr hzg)
        have hzR : z ∈ roots P Q u := (BoundedAlgebraicSliceRootProduct.root_iff P Q u hu z).mpr ⟨j, hzr⟩
        exact Geometry.OrderedRealCells.gap_no_root (roots P Q u) k hzk hzR
      have hc : IsPreconnected (Geometry.OrderedRealCells.gap (roots P Q u) k) :=
        (IsPathConnected.isConnected (Geometry.OrderedRealCells.piece_pathConnected (roots P Q u) (.inr k))).2
      exact hc.sign_eq_of_continuousOn (BoundedAlgebraicSliceIndexed.value P Q u j.val).continuousOn hn hx hy

noncomputable def solutionSet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) : Set ℝ :=
  {x | truth (signVector P Q u x)}

theorem stable (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) :
    OrderedRealCellCover.Stable (roots P Q u) (solutionSet P Q u truth) := by
  intro i x hx y hy
  change truth (signVector P Q u x) ↔ truth (signVector P Q u y)
  rw [sign_constant P Q u hu i x hx y hy]

noncomputable def restrictedPiece (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) (i : Index P Q u) : Set (solutionSet P Q u truth) :=
  OrderedRealCellCover.restrictedPiece (roots P Q u) (solutionSet P Q u truth) i

theorem cover (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) (x : solutionSet P Q u truth) :
    ∃ i : Index P Q u, x ∈ restrictedPiece P Q u truth i :=
  OrderedRealCellCover.restricted_cover (roots P Q u) (solutionSet P Q u truth) x

theorem accessible (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) (i : Index P Q u) :
    FrontierCover.Accessible (restrictedPiece P Q u truth i) :=
  OrderedRealCellCover.restricted_accessible (roots P Q u) (solutionSet P Q u truth) (stable P Q u hu truth) i

theorem joinedIn_iff_graph (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) {i j : Index P Q u}
    {x y : solutionSet P Q u truth} (hx : x ∈ restrictedPiece P Q u truth i) (hy : y ∈ restrictedPiece P Q u truth j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (FrontierCover.Incident (restrictedPiece P Q u truth)) i j :=
  OrderedRealCellCover.joinedIn_iff_graph (roots P Q u) (solutionSet P Q u truth) (stable P Q u hu truth) hx hy

theorem preconnected_iff_graph (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (truth : (Fin (Q.count (pairFst u)) → SignType) → Prop) :
    IsPreconnected (univ : Set (solutionSet P Q u truth)) ↔ ∀ i j : Index P Q u,
      (restrictedPiece P Q u truth i).Nonempty → (restrictedPiece P Q u truth j).Nonempty →
        Relation.ReflTransGen (FrontierCover.Incident (restrictedPiece P Q u truth)) i j :=
  OrderedRealCellCover.preconnected_iff_graph (roots P Q u) (solutionSet P Q u truth) (stable P Q u hu truth)

theorem card_index (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    Fintype.card (Index P Q u) = 2 * BoundedAlgebraicSliceRootProduct.count P Q u + 1 := by
  rw [Geometry.OrderedRealCells.card_index]
  rfl

def cellBound (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℕ :=
  4 * Q.count (pairFst u) * Q.degree (pairFst u) + 1

theorem card_bound (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    Fintype.card (Index P Q u) ≤ cellBound Q u := by
  rw [card_index]
  have H := BoundedAlgebraicSliceRootProduct.count_bound P Q u
  unfold cellBound
  nlinarith

theorem cellBound_binary {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) :
    BinaryFn (cellBound Q) := by
  have hn : BinaryFn (fun u => Q.count (pairFst u)) := A.count_binary.comp pairFst_mem_FP
  have hd : BinaryFn (fun u => Q.degree (pairFst u)) := A.degree_binary.comp pairFst_mem_FP
  exact (((BinaryFn.const 4).mul hn).mul hd).add (BinaryFn.const 1)

def labelWidth (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℕ := (cellBound Q u).size

theorem labelWidth_unary {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) : UnaryFn (labelWidth Q) :=
  (UnaryFn.length (cellBound_binary A).bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (cellBound Q u))

theorem card_lt_pow_width (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    Fintype.card (Index P Q u) < 2 ^ labelWidth Q u :=
  (card_bound P Q u).trans_lt (Nat.lt_size_self _)

end LeanCanny.Connectivity.AlgebraicSliceCellCover
