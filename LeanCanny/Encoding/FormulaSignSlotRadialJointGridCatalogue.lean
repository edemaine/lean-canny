/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridSource
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
public import LeanCanny.Algebra.SquareFeatureProductFamily
/-! # The actual finite grid-feature catalogue at a descriptor's choices

Context is pair joint-header perturbation-table. Every coordinate appears;
table entries select only its perturbation coefficient. Missing entries
decode zero, as in the actual WordList protocol.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def header (c : List Bool) := pairFst c
def choice (c : List Bool) (i : ℕ) := WordList.get (pairSnd c) i
noncomputable def datum (c : List Bool) (i : ℕ) := pair (header c) (pair (BinaryNatCode.encode i) (choice c i))
noncomputable def base (c : List Bool) := pair (FormulaSignSlotRadialJointLayout.source true (header c)) []
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialJointLayout.dimension (header c)
noncomputable def count (c : List Bool) := FormulaSignSlotRadialJointLayout.spatialCount (header c)
noncomputable def degree (c : List Bool) := FormulaSignSlotRadialEliminantPacked.resultDegree (base c)
noncomputable def mass (c : List Bool) := FormulaSignSlotRadialEliminantFormalMass.budget (base c)

theorem arity_eq (c : List Bool) (i : ℕ) : FormulaSignSlotRadialJointGridSource.source.arity (datum c i)=arity c := by
  change FormulaSignSlotRadialJointLayout.dimension (FormulaSignSlotRadialJointGridLayout.header (datum c i))=_
  simp only [FormulaSignSlotRadialJointGridLayout.header,datum,pairFst_pair,arity]
theorem root_eq (c : List Bool) (i : ℕ) :
    pairFst (FormulaSignSlotRadialJointGridLayout.radial (datum c i))=pairFst (base c) := by
  rw [FormulaSignSlotRadialJointGridLayout.radial_root]
  simp only [base,FormulaSignSlotRadialJointGridLayout.header,datum,pairFst_pair]
theorem degree_eq (c : List Bool) (i : ℕ) : FormulaSignSlotRadialJointGridSource.source.degree (datum c i)=degree c :=
  FormulaSignSlotRadialEliminantRootProfiles.degree_eq _ _ (root_eq c i)
theorem mass_eq (c : List Bool) (i : ℕ) : FormulaSignSlotRadialJointGridSource.source.mass (datum c i)=mass c :=
  FormulaSignSlotRadialEliminantRootProfiles.mass_eq _ _ (root_eq c i)

noncomputable def feature (c : List Bool) (i : ℕ) : MvPolynomial (Fin (arity c)) ℤ :=
  rename (Fin.cast (arity_eq c i)) (FormulaSignSlotRadialJointGridSource.source.polynomial (datum c i))
theorem feature_degree (c : List Bool) (i : ℕ) : (feature c i).totalDegree ≤ degree c := by
  exact ((totalDegree_rename_le _ _).trans
    (FormulaSignSlotRadialJointGridSource.source.polynomial_degree _)).trans_eq (degree_eq c i)
theorem feature_mass (c : List Bool) (i : ℕ) : MvMass.mass (feature c i)≤2^mass c := by
  exact ((MvMass.rename_le _ _).trans
    (FormulaSignSlotRadialJointGridSource.source.polynomial_mass _)).trans_eq (congrArg (2^·) (mass_eq c i))

noncomputable def family : SquareFeatureProductFamily.Family where
  arity := arity
  count := count
  degree := degree
  mass := mass
  feature := feature
  feature_degree c i _ := feature_degree c i
  feature_mass c i _ := feature_mass c i

theorem base_FP : base ∈ FP := mem_FP_pair
  (mem_FP_comp (f := header) (g := FormulaSignSlotRadialJointLayout.source true)
    pairFst_mem_FP (FormulaSignSlotRadialJointLayout.source_FP true)) (constFn_mem_FP [])
theorem arity_unary : UnaryFn arity := FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP
theorem count_unary : UnaryFn count := FormulaSignSlotRadialJointLayout.spatialCount_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp base_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp base_FP

private theorem eval_cast {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (v : ℕ → ℝ) :
    (rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun j => v j.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]

theorem feature_eval (c : List Bool) (i : ℕ) (v : ℕ → ℝ) :
    (feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialJointGridSource.source.polynomial (datum c i)).eval₂
        (Int.castRingHom ℝ) (fun j => v j.val) := by
  exact eval_cast (arity_eq c i) (FormulaSignSlotRadialJointGridSource.source.polynomial (datum c i)) v

theorem feature_selected_evaluation (c : List Bool) (i : ℕ) (v : ℕ → ℝ) (D : ℕ)
    (H : FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial (datum c i))
      (FormulaSignSlotRadialJointGridSource.center (datum c i) v)
      (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord (datum c i))) D) :
    (feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      (FormulaSignSlotRadialParameterEliminant.coordinate
        (pairFst (FormulaSignSlotRadialJointGridLayout.radial (datum c i)))
        (FormulaSignSlotRadialJointGridSource.center (datum c i) v)
        (FormulaSignSlotRadialEliminantInput.coordinate (FormulaSignSlotRadialJointGridLayout.radial (datum c i)))).eval₂
          (Polynomial.evalRingHom (v (FormulaSignSlotRadialJointLayout.radiusVariable
            (FormulaSignSlotRadialJointGridLayout.header (datum c i)))))
          (v (FormulaSignSlotRadialJointLayout.column 2 (FormulaSignSlotRadialJointGridLayout.selected (datum c i)))) :=
  (feature_eval c i v).trans (FormulaSignSlotRadialJointGridSource.selected_evaluation (datum c i) v D H)

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogue
