/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginGraph
public import LeanCanny.Geometry.PositiveReciprocalGraph
/-! # The actual closed margin source is its literal reciprocal graph -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginGraph
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem holds_append (N : ℕ) (y : Fin N → ℝ) (r : ℝ) (p : Formula) (hp : p.arity≤N) :
    p.Holds (Formula.extend (Fin.append y (fun _ : Fin 1 => r))) ↔ p.Holds (Formula.extend y) := by
  apply Formula.holds_congr
  intro i hi
  have HI : i<N := hi.trans_le hp
  have HN : i<N+1 := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HN]
  change Fin.append y (fun _ : Fin 1 => r) (Fin.castAdd 1 ⟨i,HI⟩)=y ⟨i,HI⟩
  exact Fin.append_left _ _ _

theorem eval_append (N : ℕ) (y : Fin N → ℝ) (r : ℝ) (p : Term) (hp : p.arity≤N) :
    p.eval (Formula.extend (Fin.append y (fun _ : Fin 1 => r)))=p.eval (Formula.extend y) := by
  apply Term.eval_congr
  intro i hi
  have HI : i<N := hi.trans_le hp
  have HN : i<N+1 := by omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HN]
  change Fin.append y (fun _ : Fin 1 => r) (Fin.castAdd 1 ⟨i,HI⟩)=y ⟨i,HI⟩
  exact Fin.append_left _ _ _

theorem source_append (F : Family) (c : List Bool) (y : Fin (F.dimension c+F.count c) → ℝ) (r : ℝ)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (PositiveMarginSource.source F c).Holds (Formula.extend (Fin.append y (fun _ : Fin 1 => r))) ↔
      r*(PositiveMarginSource.root F c).eval (Formula.extend y)=1 ∧
        y∈TriangularContinuousGraph.Solutions (F.dimension c) (gate F c) (F.count c) := by
  have HR:=eval_append _ y r _ (PositiveMarginSource.root_arity F c)
  have HV : Formula.extend (Fin.append y (fun _ : Fin 1 => r)) (F.dimension c+F.count c)=r := by
    simp only [Formula.extend,dite_eq_left (show F.dimension c+F.count c<F.dimension c+F.count c+1 by omega)]
    change Fin.append y (fun _ : Fin 1 => r) (Fin.natAdd _ (0 : Fin 1))=r
    exact Fin.append_right _ _ _
  have HC : (∀ i < F.count c, (PositiveMarginSource.condition F (pair c (List.replicate i true))).Holds
      (Formula.extend (Fin.append y (fun _ : Fin 1 => r)))) ↔
      (∀ i < F.count c, (PositiveMarginSource.condition F (pair c (List.replicate i true))).Holds (Formula.extend y)) := by
    apply forall₂_congr
    intro i hi
    apply holds_append
    have HS:=PositiveMarginSource.condition_arity F (pair c (List.replicate i true))
      (by simpa only [dimension,pairFst_pair] using ha i hi)
    simp only [PositiveMarginSource.valueIndex,dimension,index,pairFst_pair,pairSnd_pair,List.length_replicate] at HS
    omega
  simp only [PositiveMarginSource.source,Formula.Holds,PositiveMarginSource.reciprocal,WeakCircleCanonicalFormula.difference,
    Term.eval,Int.cast_neg,Int.cast_one,mul_one,← sub_eq_add_neg,sub_eq_zero,
    FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds,List.forall_mem_map,List.mem_range]
  rw [HV,HR,HC,conditions_iff F c y ha]

noncomputable def appendHomeomorph (N : ℕ) : ((Fin N → ℝ) × ℝ) ≃ₜ (Fin (N+1) → ℝ) :=
  ((Homeomorph.refl (Fin N → ℝ)).prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm).trans (Fin.appendHomeomorph N 1)

theorem appendHomeomorph_apply (N : ℕ) (p : (Fin N → ℝ) × ℝ) :
    appendHomeomorph N p=Fin.append p.1 (fun _ : Fin 1 => p.2) := rfl

noncomputable abbrev Sol (F : Family) (c : List Bool) :=
  TriangularContinuousGraph.Solutions (F.dimension c) (gate F c) (F.count c)
noncomputable def rootOn (F : Family) (c : List Bool) (y : Sol F c) : ℝ :=
  (PositiveMarginSource.root F c).eval (Formula.extend y.val)

noncomputable def reciprocalHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (PositiveMarginSource.description F c).realization ≃ₜ PositiveReciprocalGraph.Space (rootOn F c) := by
  let E:=appendHomeomorph (F.dimension c+F.count c)
  have HE (z : (PositiveMarginSource.description F c).realization) :
      (E.symm z.val).2*(PositiveMarginSource.root F c).eval (Formula.extend (E.symm z.val).1)=1 ∧
        (E.symm z.val).1∈Sol F c := by
    apply (source_append F c _ _ ha).mp
    have HV : Fin.append (E.symm z.val).1 (fun _ : Fin 1 => (E.symm z.val).2)=z.val := E.apply_symm_apply z.val
    rw [HV]
    exact z.property
  let f : (PositiveMarginSource.description F c).realization → PositiveReciprocalGraph.Space (rootOn F c) :=
    fun z => ⟨(⟨(E.symm z.val).1,(HE z).2⟩,(E.symm z.val).2),(HE z).1⟩
  let g : PositiveReciprocalGraph.Space (rootOn F c) → (PositiveMarginSource.description F c).realization :=
    fun z => ⟨E (z.val.1.val,z.val.2),(source_append F c _ _ ha).mpr ⟨z.property,z.val.1.property⟩⟩
  refine { toFun := f, invFun := g, left_inv := ?_,right_inv := ?_,continuous_toFun := ?_,continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    exact E.apply_symm_apply z.val
  · intro z
    apply Subtype.ext
    change (⟨(E.symm (E (z.val.1.val,z.val.2))).1,_⟩,(E.symm (E (z.val.1.val,z.val.2))).2)=z.val
    simp only [E.symm_apply_apply]
  · have HP : Continuous (fun z : (PositiveMarginSource.description F c).realization => E.symm z.val) :=
      E.symm.continuous.comp continuous_subtype_val
    have HF : Continuous (fun z : (PositiveMarginSource.description F c).realization =>
        (⟨(E.symm z.val).1,(HE z).2⟩ : Sol F c)) := (continuous_fst.comp HP).subtype_mk _
    exact (HF.prodMk (continuous_snd.comp HP)).subtype_mk _
  · exact (E.continuous.comp (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).comp
      continuous_subtype_val)).subtype_mk _

end LeanCanny.Connectivity.PositiveMarginGraph
