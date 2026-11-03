/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteVertices
/-! # Primitive parameter and decoded values under literal input composition -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleParameterNaturality
open LeanCanny.Algebra SquareSampleInput Polynomial
open scoped Classical
attribute [local irreducible] FiniteLeafCoordinateBits.coordinate SquareSampleParameters.decode
  SquareSampleCoordinates.coordinate

theorem leaf_congr (p q : ℕ→Polynomial ℤ) (n : ℕ)
    (hp : ∀i<n,p i≠0) (hq : ∀i<n,q i≠0) (H : ∀i<n,p i=q i) :
    FiniteAnnihilatorTree.leaf p n hp=FiniteAnnihilatorTree.leaf q n hq :=by
  funext i
  unfold FiniteAnnihilatorTree.leaf
  split_ifs with hi
  · have HS (a b : Polynomial ℤ) (ha : a≠0) (hb : b≠0) (he : a=b) :
        SeparableIntegerPolynomial.squarefree a ha=SeparableIntegerPolynomial.squarefree b hb:=by
      cases he
      rfl
    exact HS _ _ _ _ (H i hi)
  · rfl

theorem tree_decode_congr (p q : ℕ→Polynomial ℤ) (n k : ℕ)
    (hp : ∀i<n,p i≠0) (hq : ∀i<k,q i≠0) (hn : n=k) (H : ∀i<n,p i=q i)
    (theta : ℝ) (i : Fin n) (j : Fin k) (hij : i.val=j.val) :
    FiniteAnnihilatorTree.decode p n hp theta i=FiniteAnnihilatorTree.decode q k hq theta j :=by
  subst k
  have HE : i=j:=Fin.ext hij
  subst j
  simp only [FiniteAnnihilatorTree.decode,leaf_congr p q n hp hq H]

noncomputable def polynomials (F : Inputs) (u : List Bool) (i : ℕ) : Polynomial ℤ:=
  if hi : i<F.count u then F.annihilator u ⟨i,hi⟩ else X

theorem polynomials_nonzero (F : Inputs) (u : List Bool) (i : ℕ) (hi : i<F.count u) :
    polynomials F u i≠0 :=by
  rw [polynomials,dite_eq_left hi]
  exact F.ann_nonzero u _

theorem parameter_eq (F : Inputs) (u : List Bool) :
    SquareSampleCoordinates.parameter F u=
      (FiniteAnnihilatorTree.parameter (polynomials F u) (F.count u) (polynomials_nonzero F u)).polynomial :=by
  let c:=SquareSampleSource.prepare F u
  let p:=fun i=>(SquareSampleSource.family F).polynomial (pair c (BinaryNatCode.encode i))
  have Hn : SquareSampleCoordinates.count F c=F.count u:=by
    simp only [SquareSampleCoordinates.count,c,SquareSampleSource.prepare_source,SquareSampleSource.count]
  have H : ∀i<F.count u,p i=polynomials F u i:=by
    intro i hi
    rw [polynomials,dite_eq_left hi]
    exact SquareSampleSource.prepared_coordinate F u ⟨i,hi⟩
  have HE:=leaf_congr p (polynomials F u) (F.count u)
    (fun i hi=>SquareSampleCoordinates.nonzero F c i (Hn.symm ▸ hi)) (polynomials_nonzero F u) H
  simp only [SquareSampleCoordinates.parameter,SquareSampleCoordinates.rawParameter,Function.comp_apply,
    FiniteAnnihilatorBits.finiteParameter]
  change (FiniteAnnihilatorTree.parameter p (SquareSampleCoordinates.count F c) _).polynomial=_
  simp only [SquareSampleCoordinates.count,c,SquareSampleSource.prepare_source,SquareSampleSource.count]
  change (BalancedPrimitiveTree.node (FiniteAnnihilatorTree.leaf p (F.count u) _) _ _).polynomial=_
  rw [HE]
  rfl

theorem parameter_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleCoordinates.parameter (comp F f) u=SquareSampleCoordinates.parameter F (f u) :=by
  rw [parameter_eq,parameter_eq]
  rfl

theorem decode_eq (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (SquareSampleCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta=0) :
    SquareSampleParameters.decode F u theta=
      FiniteAnnihilatorTree.decode (polynomials F u) (F.count u) (polynomials_nonzero F u) theta :=by
  funext i
  let c:=SquareSampleSource.prepare F u
  let p:=fun j=>(SquareSampleSource.family F).polynomial (pair c (BinaryNatCode.encode j))
  have Hn : SquareSampleCoordinates.count F c=F.count u:=by
    simp only [SquareSampleCoordinates.count,c,SquareSampleSource.prepare_source,SquareSampleSource.count]
  let j : Fin (SquareSampleCoordinates.count F c):=⟨i.val,Hn.symm ▸ i.isLt⟩
  have HD:=FiniteLeafCoordinateBits.finite_decode_spec (SquareSampleSource.family F)
    (SquareSampleCoordinates.count F) (SquareSampleCoordinates.degreeBound F)
    (SquareSampleCoordinates.height F) (SquareSampleCoordinates.nonzero F)
    (SquareSampleCoordinates.degree_le F) (SquareSampleCoordinates.height_le F) c j theta ht
  rw [SquareSampleParameters.decode]
  change (SquareSampleCoordinates.coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta=_
  have HV : (SquareSampleCoordinates.coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta=
      FiniteAnnihilatorTree.decode p (SquareSampleCoordinates.count F c)
        (SquareSampleCoordinates.nonzero F c) theta j:=by
    simpa only [SquareSampleCoordinates.coordinate,SquareSampleCoordinates.rawCoordinate,
      SquareSampleCoordinates.prepareCoordinate,Function.comp_apply,pairFst_pair,pairSnd_pair,j,c] using HD.2
  apply HV.trans
  apply tree_decode_congr p (polynomials F u) _ _ (SquareSampleCoordinates.nonzero F c)
    (polynomials_nonzero F u) Hn _ theta j i rfl
  intro k hk
  have hi : k<F.count u:=Hn ▸ hk
  have HE:=SquareSampleSource.prepared_coordinate F u ⟨k,hi⟩
  change p k=polynomials F u k
  exact HE.trans (show F.annihilator u ⟨k,hi⟩=polynomials F u k from by
    unfold polynomials
    rw [dite_eq_left hi])

theorem decode_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool) (theta : ℝ)
    (ht : (SquareSampleCoordinates.parameter F (f u)).eval₂ (Int.castRingHom ℝ) theta=0) :
    SquareSampleParameters.decode (comp F f) u theta=SquareSampleParameters.decode F (f u) theta :=by
  rw [decode_eq _ _ _ (by rw [parameter_comp];exact ht),decode_eq _ _ _ ht]
  rfl

theorem roots_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool) :
    SquareSampleQueries.roots (comp F f) u=SquareSampleQueries.roots F (f u) :=by
  ext theta
  rw [SquareSampleQueries.mem_roots,SquareSampleQueries.mem_roots,parameter_comp]
  constructor
  · intro H
    have HD:=decode_comp F f u theta H.1
    rw [HD] at H
    exact H
  · intro H
    have HD:=decode_comp F f u theta H.1
    rw [HD]
    exact H

end LeanCanny.Encoding.SquareSampleParameterNaturality
