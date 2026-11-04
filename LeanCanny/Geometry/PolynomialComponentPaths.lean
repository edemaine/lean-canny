/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialFiniteComponents
public import LeanCanny.Geometry.PolynomialLocallyConnected
public import LeanCanny.Geometry.CompleteConnectedIsometricPath
/-! # Paths in actual connected components of a closed polynomial zero set -/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialComponentPaths
open Set MvPolynomial CoerciveComponentSampling
open scoped Classical

theorem subtype_joined {n :ℕ} (q :MvPolynomial (Fin n) ℝ)
    (a b :Zeros q) (hb :b∈connectedComponent a):JoinedIn (Zeros q) a.val b.val:=by
  let :Finite (ConnectedComponents (Zeros q)):=PolynomialFiniteComponents.components_finite q q.totalDegree le_rfl
  let :CompleteSpace (Zeros q):=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).isComplete.completeSpace_coe
  let :LocallyConnectedSpace (Zeros q):=PolynomialLocallyConnected.locallyConnected q
  have HC:=FiniteComponentCover.isClopen_component a
  let :ConnectedSpace (connectedComponent a):=isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let :CompleteSpace (connectedComponent a):=HC.isClosed.isComplete.completeSpace_coe
  let :LocallyConnectedSpace (connectedComponent a):=HC.isOpen.locallyConnectedSpace
  let coordinate :connectedComponent a→Fin n→ℝ:=fun point=>point.val.val
  have HE:Isometry coordinate:=Isometry.of_dist_eq (fun _ _=>rfl)
  have H:=CompleteConnectedIsometricPath.joined coordinate HE ⟨a,mem_connectedComponent⟩ ⟨b,hb⟩
  have HComp:JoinedIn (connectedComponent a) a b:=(joinedIn_iff_joined mem_connectedComponent hb).mpr H
  apply (HComp.map continuous_subtype_val.continuousOn).mono
  rintro point ⟨value,_,rfl⟩
  exact value.property

theorem joinedIn_of_component {n :ℕ} (q :MvPolynomial (Fin n) ℝ)
    (x :Fin n→ℝ) (hx :x∈Zeros q) (y :Fin n→ℝ)
    (hy :y∈connectedComponentIn (Zeros q) x):JoinedIn (Zeros q) x y:=by
  rw [connectedComponentIn_eq_image hx] at hy
  obtain ⟨point,hpoint,rfl⟩:=hy
  exact subtype_joined q ⟨x,hx⟩ point hpoint

end LeanCanny.Geometry.PolynomialComponentPaths
