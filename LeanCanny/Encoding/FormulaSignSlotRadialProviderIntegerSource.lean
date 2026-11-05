/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackAccess
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerBounds
/-! # One native OLD or EXTERNAL n+8 integer source

Both roles retain the old spatial source and the SAME metadata radius.
The external role reads its own grid coordinates and one certified slack
algebra, without identifying that point with the old candidate label.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
open FormulaSignSlotRadialExternalPrelude (number radius radius_binary)

def tag (q : List Bool) := Nat.fromBitsLE (pairSnd q)
noncomputable def saved (q : List Bool) := FormulaSignSlotRadialExternalSlackSource.key (pairFst q)
theorem saved_FP : saved ∈ FP := mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialExternalSlackSource.key_FP
noncomputable def power (E : List Bool → ℕ) := PowerIntegerPolynomial.source (fun _ => False) E

noncomputable def externalSource : IntegerPolynomialRootQueriesBits.Source :=
  choose (fun q => tag q<number (pairFst q)) FormulaSignSlotRadialExternalCoordinates.source
  (choose (fun q => tag q=number (pairFst q))
    (reindex FormulaSignSlotRadialExternalSlackSource.sphereSource saved)
  (choose (fun q => tag q=number (pairFst q)+2)
    (reindex FormulaSignSlotRadialExternalSlackSource.regularSource saved)
  (choose (fun q => tag q=number (pairFst q)+4) (power (radius ∘ pairFst))
  (choose (fun q => tag q=number (pairFst q)+5) (power (FormulaSignSlotRadialExternalSlackSource.Lam ∘ saved))
  (choose (fun q => tag q=number (pairFst q)+6) (power (FormulaSignSlotRadialExternalSlackSource.beta ∘ saved))
  (choose (fun q => tag q=number (pairFst q)+7) (power (FormulaSignSlotRadialExternalSlackSource.K ∘ saved))
    IntegerPolynomialZeroRootSource.source))))))

noncomputable def oldSource := IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius
noncomputable def source := choose (fun q => FormulaSignSlotRadialExternalContext.external (pairFst q)) externalSource oldSource

theorem external_access : IntegerPolynomialRootQueriesBits.Access externalSource := by
  have HI : BinaryFn tag := BinaryFn.fromBits pairSnd_mem_FP
  have HN : BinaryFn (fun q => number (pairFst q)) :=
    (BinaryFn.ofUnary FormulaSignSlotRadialExternalContext.number_unary).comp pairFst_mem_FP
  have HP : FPPred (fun _ : List Bool => False) := FPPred.const False
  unfold externalSource
  exact choose_access (HI.lt HN) _ _ FormulaSignSlotRadialExternalCoordinates.access
    (choose_access (HI.eq HN) _ _
      (reindex_access _ FormulaSignSlotRadialExternalSlackAccess.sphere_access saved_FP)
    (choose_access (HI.eq (HN.add (BinaryFn.const 2))) _ _
      (reindex_access _ FormulaSignSlotRadialExternalSlackAccess.regular_access saved_FP)
    (choose_access (HI.eq (HN.add (BinaryFn.const 4))) _ _ (PowerIntegerPolynomial.access HP (radius_binary.comp pairFst_mem_FP))
    (choose_access (HI.eq (HN.add (BinaryFn.const 5))) _ _
      (PowerIntegerPolynomial.access HP (FormulaSignSlotRadialExternalSlackSource.Lam_binary.comp saved_FP))
    (choose_access (HI.eq (HN.add (BinaryFn.const 6))) _ _
      (PowerIntegerPolynomial.access HP (FormulaSignSlotRadialExternalSlackSource.beta_binary.comp saved_FP))
    (choose_access (HI.eq (HN.add (BinaryFn.const 7))) _ _
      (PowerIntegerPolynomial.access HP (FormulaSignSlotRadialExternalSlackSource.K_binary.comp saved_FP))
      IntegerPolynomialZeroRootSource.access))))))

theorem old_access : IntegerPolynomialRootQueriesBits.Access oldSource :=
  IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha radius_binary

theorem access : IntegerPolynomialRootQueriesBits.Access source := choose_access
  (FormulaSignSlotRadialExternalContext.external_FP.comp pairFst_mem_FP) _ _ external_access old_access

private theorem choose_nonzero (p : List Bool → Prop) (S T : IntegerPolynomialRootQueriesBits.Source)
    (hS : ∀ q, S.polynomial q ≠ 0) (hT : ∀ q, T.polynomial q ≠ 0) : ∀ q, (choose p S T).polynomial q ≠ 0 := by
  intro q
  dsimp only [choose]
  split_ifs
  · exact hS q
  · exact hT q
private theorem power_nonzero (E : List Bool → ℕ) (q : List Bool) : (power E).polynomial q ≠ 0 := by
  intro H
  have HD := PowerIntegerPolynomial.degree False (E q)
  change (PowerIntegerPolynomial.polynomial False (E q)).natDegree=1 at HD
  rw [show PowerIntegerPolynomial.polynomial False (E q)=0 from H,Polynomial.natDegree_zero] at HD
  omega

theorem external_nonzero (q : List Bool) : externalSource.polynomial q ≠ 0 := by
  unfold externalSource
  exact choose_nonzero _ _ _ FormulaSignSlotRadialExternalCoordinates.nonzero
    (choose_nonzero _ _ _ (fun q => FormulaSignSlotRadialExternalSlackSource.sphere_nonzero (saved q))
    (choose_nonzero _ _ _ (fun q => FormulaSignSlotRadialExternalSlackSource.regular_nonzero (saved q))
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _) (fun _ => Polynomial.X_ne_zero))))))) q

theorem nonzero (q : List Bool) : source.polynomial q ≠ 0 := choose_nonzero _ _ _ external_nonzero
  (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius) q

noncomputable def externalDegreeBound (ctx : List Bool) :=
  FormulaSignSlotRadialExternalCoordinates.degreeBound ctx+
    FormulaSignSlotRadialExternalSlackSource.sphereSource.degree (FormulaSignSlotRadialExternalSlackSource.key ctx)+
    FormulaSignSlotRadialExternalSlackSource.regularSource.degree (FormulaSignSlotRadialExternalSlackSource.key ctx)+1
noncomputable def degreeBound (ctx : List Bool) :=
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha ctx+externalDegreeBound ctx

theorem externalDegreeBound_binary : BinaryFn externalDegreeBound :=
  (((FormulaSignSlotRadialExternalCoordinates.degreeBound_binary.add
    (FormulaSignSlotRadialExternalSlackAccess.sphere_access.degree.comp FormulaSignSlotRadialExternalSlackSource.key_FP)).add
    (FormulaSignSlotRadialExternalSlackAccess.regular_access.degree.comp FormulaSignSlotRadialExternalSlackSource.key_FP))).add
      (BinaryFn.const 1)

theorem degreeBound_binary : BinaryFn degreeBound :=
  (IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound_binary hn ht ha).add externalDegreeBound_binary

attribute [local irreducible] FormulaSignSlotRadialExternalCoordinates.source
  FormulaSignSlotRadialExternalCoordinates.degreeBound FormulaSignSlotRadialExternalSlackSource.sphereSource
  FormulaSignSlotRadialExternalSlackSource.regularSource

theorem external_degree_le (q : List Bool) : externalSource.degree q ≤ externalDegreeBound (pairFst q) := by
  have HC := FormulaSignSlotRadialExternalCoordinates.degree_le q
  unfold externalSource externalDegreeBound
  simp only [choose,reindex,Function.comp_apply,saved]
  split_ifs <;> first | omega | (change 1 ≤ _; omega)

theorem degree_le (q : List Bool) : source.degree q ≤ degreeBound (pairFst q) := by
  have HO := IntegralMixedAuxiliaryMarkedIntegerSource.degree_le hn ht ha radius q
  have HE := external_degree_le q
  change oldSource.degree q ≤ _ at HO
  dsimp only [source,choose,degreeBound]
  split_ifs <;> omega

theorem polynomial_external (q : List Bool) (h : FormulaSignSlotRadialExternalContext.external (pairFst q)) :
    source.polynomial q=externalSource.polynomial q := by dsimp only [source,choose]; rw [ite_eq_left h]
theorem polynomial_old (q : List Bool) (h : ¬FormulaSignSlotRadialExternalContext.external (pairFst q)) :
    source.polynomial q=oldSource.polynomial q := by dsimp only [source,choose]; rw [ite_eq_right h]

theorem external_polynomial (q : List Bool) : externalSource.polynomial q =
    if tag q < number (pairFst q) then FormulaSignSlotRadialExternalCoordinates.source.polynomial q else
    if tag q = number (pairFst q) then FormulaSignSlotRadialExternalSlackSource.sphereSource.polynomial (saved q) else
    if tag q = number (pairFst q)+2 then FormulaSignSlotRadialExternalSlackSource.regularSource.polynomial (saved q) else
    if tag q = number (pairFst q)+4 then (power (radius ∘ pairFst)).polynomial q else
    if tag q = number (pairFst q)+5 then (power (FormulaSignSlotRadialExternalSlackSource.Lam ∘ saved)).polynomial q else
    if tag q = number (pairFst q)+6 then (power (FormulaSignSlotRadialExternalSlackSource.beta ∘ saved)).polynomial q else
    if tag q = number (pairFst q)+7 then (power (FormulaSignSlotRadialExternalSlackSource.K ∘ saved)).polynomial q else
    Polynomial.X := by
  simp only [externalSource,choose,reindex,Function.comp_apply,IntegerPolynomialZeroRootSource.source]

theorem external_coordinate (q : List Bool) (h : tag q < number (pairFst q)) :
    externalSource.polynomial q = FormulaSignSlotRadialExternalCoordinates.source.polynomial q := by
  rw [external_polynomial,ite_eq_left h]
theorem external_sphere (q : List Bool) (h : tag q = number (pairFst q)) :
    externalSource.polynomial q = FormulaSignSlotRadialExternalSlackSource.sphereSource.polynomial (saved q) := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_left h]
theorem external_regular (q : List Bool) (h : tag q = number (pairFst q)+2) :
    externalSource.polynomial q = FormulaSignSlotRadialExternalSlackSource.regularSource.polynomial (saved q) := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left h]
theorem external_radius (q : List Bool) (h : tag q = number (pairFst q)+4) :
    externalSource.polynomial q = (power (radius ∘ pairFst)).polynomial q := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left h]
theorem external_lam (q : List Bool) (h : tag q = number (pairFst q)+5) :
    externalSource.polynomial q = (power (FormulaSignSlotRadialExternalSlackSource.Lam ∘ saved)).polynomial q := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_left h]
theorem external_beta (q : List Bool) (h : tag q = number (pairFst q)+6) :
    externalSource.polynomial q = (power (FormulaSignSlotRadialExternalSlackSource.beta ∘ saved)).polynomial q := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left h]
theorem external_kappa (q : List Bool) (h : tag q = number (pairFst q)+7) :
    externalSource.polynomial q = (power (FormulaSignSlotRadialExternalSlackSource.K ∘ saved)).polynomial q := by
  rw [external_polynomial,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),
    ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left h]
theorem external_zero (q : List Bool) (h : tag q = number (pairFst q)+1 ∨ tag q = number (pairFst q)+3) :
    externalSource.polynomial q = Polynomial.X := by
  rw [external_polynomial]
  split_ifs <;> first | rfl | omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerSource
