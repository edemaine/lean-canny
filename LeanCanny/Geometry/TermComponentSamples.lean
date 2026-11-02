/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TermFiniteComponents
public import Mathlib.Topology.Connected.TotallyDisconnected
/-! # Actual finite coercive-grid labels cover literal integer source components

Labels are zeros of the constructed finite trailing grid which also satisfy
the ORIGINAL polynomial. Their points retain the literal original tuple.
There is no component-membership or absolute-root lifting oracle in the cover.
-/
@[expose] public section
namespace LeanCanny.Geometry.TermComponentSamples
open Set LeanCanny.ETR MvPolynomial
open scoped Classical

noncomputable abbrev Sample (t : Term) (n : ℕ) :=
  PolynomialFiniteComponents.sample (TermFiniteComponents.polynomial t n) t.toData.size

theorem finite (t : Term) (n : ℕ) : Finite (Sample t n) :=
  (PolynomialFiniteComponents.finite_sample _ _ (TermFiniteComponents.degree t n)).to_subtype

noncomputable def fromPolynomial (t : Term) (n : ℕ)
    (a : CoerciveComponentSampling.Zeros (TermFiniteComponents.polynomial t n)) : TermFiniteComponents.Zeros t n :=
  ⟨a.val,by
    change t.eval (Formula.extend a.val)=0
    have H := a.property
    change (TermFiniteComponents.polynomial t n).eval a.val=0 at H
    simpa only [TermFiniteComponents.polynomial,MvPolynomial.eval_map,Term.eval_finitePolynomial] using H⟩

theorem continuous_fromPolynomial (t : Term) (n : ℕ) : Continuous (fromPolynomial t n) :=
  continuous_subtype_val.subtype_mk _

noncomputable def point (t : Term) (n : ℕ) (a : Sample t n) : TermFiniteComponents.Zeros t n :=
  fromPolynomial t n a.val

theorem point_coordinate (t : Term) (n : ℕ) (a : Sample t n) (i : Fin n) : (point t n a).val i=a.val.val i := rfl

theorem cover (t : Term) (n : ℕ) (x : TermFiniteComponents.Zeros t n) :
    ∃ a : Sample t n, x∈connectedComponent (point t n a) := by
  let y : CoerciveComponentSampling.Zeros (TermFiniteComponents.polynomial t n) := ⟨x.val,by
    change (TermFiniteComponents.polynomial t n).eval x.val=0
    rw [TermFiniteComponents.polynomial,MvPolynomial.eval_map,Term.eval_finitePolynomial]
    exact x.property⟩
  obtain ⟨a,HA,HG⟩ := PolynomialFiniteComponents.component_sample _ _ (TermFiniteComponents.degree t n) y
  have HE : ConnectedComponents.mk a=ConnectedComponents.mk y := ConnectedComponents.coe_eq_coe'.mpr HA
  have HM := congrArg (continuous_fromPolynomial t n).connectedComponentsMap HE
  change ConnectedComponents.mk (fromPolynomial t n a)=ConnectedComponents.mk x at HM
  exact ⟨⟨a,HG⟩,ConnectedComponents.coe_eq_coe'.mp HM.symm⟩
end LeanCanny.Geometry.TermComponentSamples
