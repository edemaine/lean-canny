/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridSource
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRootProfiles
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
/-! # Literal grid-anchor features with an original binary catalogue

The coordinate and perturbation indices are decoded from one bounded ordinal.
This source-only catalogue does not depend on a stratum or its sampler.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridCompleteCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointGridSource.source

noncomputable def base (c :List Bool) :=pair (FormulaSignSlotRadialJointLayout.source true c) []
noncomputable def degree (c :List Bool) :=FormulaSignSlotRadialEliminantPacked.resultDegree (base c)
noncomputable def mass (c :List Bool) :=FormulaSignSlotRadialEliminantFormalMass.budget (base c)
noncomputable def limit (c :List Bool) :=degree c+1
noncomputable def count (c :List Bool) :=FormulaSignSlotRadialJointLayout.spatialCount c*limit c
noncomputable def coordinate (c :List Bool) (i :ℕ) :=i/limit c
noncomputable def tau (c :List Bool) (i :ℕ) :=i%limit c
noncomputable def encode (c :List Bool) (j t :ℕ) :=t+limit c*j
noncomputable def row (q :List Bool) :=pair (pairFst q)
  (pair (BinaryNatCode.encode (coordinate (pairFst q) (Nat.fromBitsLE (pairSnd q))))
    (BinaryNatCode.encode (tau (pairFst q) (Nat.fromBitsLE (pairSnd q)))))

theorem root_eq (c :List Bool) (i :ℕ) :
    pairFst (FormulaSignSlotRadialJointGridLayout.radial (row (pair c (BinaryNatCode.encode i))))=pairFst (base c) :=by
  rw [FormulaSignSlotRadialJointGridLayout.radial_root]
  simp only [FormulaSignSlotRadialJointGridLayout.header,row,base,pairFst_pair]
theorem arity_eq (c :List Bool) (i :ℕ) :
    (S).arity (row (pair c (BinaryNatCode.encode i)))=FormulaSignSlotRadialJointLayout.dimension c :=by
  change FormulaSignSlotRadialJointLayout.dimension (FormulaSignSlotRadialJointGridLayout.header (row (pair c (BinaryNatCode.encode i))))=_
  simp only [FormulaSignSlotRadialJointGridLayout.header,row,pairFst_pair]
theorem degree_eq (c :List Bool) (i :ℕ) : (S).degree (row (pair c (BinaryNatCode.encode i)))=degree c :=
  FormulaSignSlotRadialEliminantRootProfiles.degree_eq _ _ (root_eq c i)
theorem mass_eq (c :List Bool) (i :ℕ) : (S).mass (row (pair c (BinaryNatCode.encode i)))=mass c :=
  FormulaSignSlotRadialEliminantRootProfiles.mass_eq _ _ (root_eq c i)

noncomputable def input :ChargedPolynomialCatalogue.Input where
  source:=S
  row:=row
  arity:=FormulaSignSlotRadialJointLayout.dimension
  count:=count
  degree:=degree
  mass:=mass
  dimension:=arity_eq
  degree_bound c i:=(degree_eq c i).le
  mass_bound c i:=(mass_eq c i).le
noncomputable def family :=ChargedPolynomialCatalogue.family input

theorem base_FP :base∈FP :=mem_FP_pair (FormulaSignSlotRadialJointLayout.source_FP true) (constFn_mem_FP [])
theorem degree_binary :BinaryFn degree :=FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp base_FP
theorem mass_binary :BinaryFn mass :=FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp base_FP
theorem limit_binary :BinaryFn limit :=degree_binary.add (BinaryFn.const 1)
theorem count_binary :BinaryFn count :=(BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).mul limit_binary
theorem row_FP :row∈FP :=by
  have HI :BinaryFn (fun q=>Nat.fromBitsLE (pairSnd q)):=BinaryFn.fromBits pairSnd_mem_FP
  have HL :BinaryFn (fun q=>limit (pairFst q)):=limit_binary.comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (HI.div HL).bits_mem_FP (HI.mod HL).bits_mem_FP)
theorem source_fit (z :List Bool) :(S).degree z<2^(S).width z :=by
  dsimp only [FormulaSignSlotRadialJointGridSource.source,IntegralFramedBankPolynomialEmbedding.source]
  exact FormulaSignSlotRadialJointGridSource.degree_fit z
noncomputable def input_access :ChargedPolynomialCatalogue.Access input where
  source:=FormulaSignSlotRadialJointGridSource.access
  row:=row_FP
  arity:=FormulaSignSlotRadialJointLayout.dimension_unary
  count:=count_binary
  degree:=degree_binary
  mass:=mass_binary
  fit:=source_fit
noncomputable def access :SquareFeatureProductFamily.Access family :=ChargedPolynomialCatalogue.access input input_access

theorem row_encode (c :List Bool) (j t :ℕ) (ht :t<limit c) :
    row (pair c (BinaryNatCode.encode (encode c j t)))=
      pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t)) :=by
  have HB :0<limit c:=by unfold limit;omega
  have HD :encode c j t/limit c=j:=by
    rw [encode,Nat.add_mul_div_left _ _ HB,Nat.div_eq_of_lt ht,Nat.zero_add]
  have HM :encode c j t%limit c=t:=by
    rw [encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]
  simp only [row,coordinate,tau,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HD,HM]
theorem encode_lt (c :List Bool) (j t :ℕ)
    (hj :j<FormulaSignSlotRadialJointLayout.spatialCount c) (ht :t<limit c) :encode c j t<count c :=by
  calc
    _ < limit c+limit c*j :=Nat.add_lt_add_right ht _
    _ = limit c*(j+1) :=by ring
    _ ≤ limit c*FormulaSignSlotRadialJointLayout.spatialCount c :=Nat.mul_le_mul_left _ (by omega)
    _ = count c :=by unfold count;ring

private theorem eval_cast {a b :ℕ} (h :a=b) (p :MvPolynomial (Fin a) ℤ) (v :ℕ→ℝ) :
    (rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val) :=by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]
theorem feature_value (c :List Bool) (i :ℕ) (v :ℕ→ℝ) :
    (family.feature c i).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      ((S).polynomial (row (pair c (BinaryNatCode.encode i)))).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val) :=
  eval_cast (arity_eq c i) ((S).polynomial _) v

theorem feature_encode (c :List Bool) (j t :ℕ) (ht :t<limit c) (v :ℕ→ℝ) :
    (family.feature c (encode c j t)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((S).polynomial (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t)))).eval₂
        (Int.castRingHom ℝ) (fun i=>v i.val) :=by
  rw [feature_value,row_encode c j t ht]

/-- The selected feature is the actual eliminant precisely under the genuine
same-center perturbation/degree guard. The guard is not inferred from a count. -/
theorem selected_feature (c :List Bool) (j t :ℕ) (ht :t<limit c) (v :ℕ→ℝ) (D :ℕ)
    (hg :let z:=pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
      FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
        (FormulaSignSlotRadialJointGridSource.center z v)
        (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D) :
    (family.feature c (encode c j t)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      let z:=pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
      (FormulaSignSlotRadialParameterEliminant.coordinate
        (pairFst (FormulaSignSlotRadialJointGridLayout.radial z))
        (FormulaSignSlotRadialJointGridSource.center z v)
        (FormulaSignSlotRadialEliminantInput.coordinate (FormulaSignSlotRadialJointGridLayout.radial z))).eval₂
          (Polynomial.evalRingHom (v (FormulaSignSlotRadialJointLayout.radiusVariable
            (FormulaSignSlotRadialJointGridLayout.header z))))
          (v (FormulaSignSlotRadialJointLayout.column 2 (FormulaSignSlotRadialJointGridLayout.selected z))) :=
  (feature_encode c j t ht v).trans (FormulaSignSlotRadialJointGridSource.selected_evaluation _ v D hg)

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridCompleteCatalogue
