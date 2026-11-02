/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.SampledBitComponentCover
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidatePointSampling
public import LeanCanny.Geometry.PolynomialLocallyConnected

/-! # Actual bounded auxiliary candidates index original zero-set components

The original-equation predicate filters native candidate labels. Their points
are the actual joint-root bank coordinates, and every clopen original piece
contains one. Invalid labels remain empty. All component paths and the
2^labelWidth component bound are derived here. Native costs for the original
filter and SAME-component/relative-frontier adjacency remain separate.
-/
@[expose] public section
namespace LeanCanny.Connectivity.AuxiliaryCandidateComponentCover
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Space (n : List Bool→ℕ) (t : List Bool→Term) (original : List Bool) :=
  CoerciveComponentSampling.Zeros (AuxiliaryTiltedTerm.polynomial (n original) (t original))

theorem evaluation (n : ℕ) (t : Term) (x : Fin n→ℝ) :
    (AuxiliaryTiltedTerm.polynomial n t).eval x=t.eval (Formula.extend x) := by
  rw [AuxiliaryTiltedTerm.polynomial_eq_map,MvPolynomial.eval_map,Term.eval_finitePolynomial]

def Good {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) : Prop :=
  ∃ hv : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair original label),
    (t original).eval (Formula.extend (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original label hv))=0

noncomputable def sample {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool)
    (i : {i : Vertex (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)//Good hn ht ha original i.val}) :
    Space n t original :=
  ⟨IntegralMixedAuxiliaryCandidate.pointAt hn ht ha original i.val.val (Classical.choose i.property),
    (evaluation _ _ _).trans (Classical.choose_spec i.property)⟩

attribute [local irreducible] sample IntegralMixedAuxiliaryCandidate.pointAt IntegralMixedAuxiliaryCandidate.point
  IntegralMixedAuxiliaryCandidate.labelWidth IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryRecipeRoot.positiveInput
  IntegralMixedAuxiliaryRecipeRoot.positiveState IntegralMixedAuxiliaryRecipeRoot.root IntegralMixedAuxiliaryRecipeRoot.planAt
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryParameters.scalarWidth
  IntegralMixedAuxiliaryParameters.scalarCeiling IntegralMixedAuxiliaryParameters.spatialDegree pair

noncomputable def samples {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) :
    SampledBitComponentCover.Samples (Space n t original) (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original) where
  good := Good hn ht ha original
  point := sample hn ht ha original
  hit C hC hN := by
    obtain ⟨x0,hx0⟩:=hN
    obtain ⟨label,hv,p,hp,Hread⟩:=IntegralMixedAuxiliaryCandidate.exists_point_sample hn ht ha original C hC x0 hx0
    have HL : label.length=IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original := by
      simpa only [pairSnd_pair,pairFst_pair] using hv.1.1
    have HG : Good hn ht ha original label := by
      refine ⟨hv,?_⟩
      rw [Hread]
      exact (evaluation _ _ _).symm.trans p.property
    refine ⟨⟨⟨label,HL⟩,HG⟩,?_⟩
    have HE : sample hn ht ha original ⟨⟨label,HL⟩,HG⟩=p := by
      apply Subtype.ext
      unfold sample
      exact Hread
    rw [HE]
    exact hp

theorem component_card_le {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) :
    Nat.card (ConnectedComponents (Space n t original))≤2^IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original :=
  SampledBitComponentCover.component_card_le (samples hn ht ha original)

theorem component_ceiling_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    BinaryFn (fun original=>2^IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original) :=
  (BinaryFn.const 2).powUnary (IntegralMixedAuxiliaryCandidate.labelWidth_unary hn ht ha)

noncomputable def cover {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) :
    ClopenPathCover (Space n t original) (Vertex (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)) := by
  let : CompleteSpace (Space n t original) :=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).isComplete.completeSpace_coe
  let : LocallyConnectedSpace (Space n t original) := PolynomialLocallyConnected.locallyConnected _
  exact SampledBitComponentCover.clopenCover (samples hn ht ha original)
    (fun x=>x.val) (Isometry.of_dist_eq (fun _ _=>rfl))

theorem nonempty_iff_good {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (i : Vertex (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)) :
    ((cover hn ht ha original).piece i).Nonempty↔Good hn ht ha original i.val :=
  SampledBitComponentCover.piece_nonempty (samples hn ht ha original) i

theorem incident_iff {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (i j : Vertex (IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha original)) :
    FrontierCover.Incident (cover hn ht ha original).piece i j↔
      ∃ hi : Good hn ht ha original i.val,∃ hj : Good hn ht ha original j.val,
        sample hn ht ha original ⟨j,hj⟩∈connectedComponent (sample hn ht ha original ⟨i,hi⟩) :=
  SampledBitComponentCover.incident_iff (samples hn ht ha original) i j

end LeanCanny.Connectivity.AuxiliaryCandidateComponentCover
