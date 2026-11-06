/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialValueWindowCatalogue
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiIntervalSigns
/-! # The actual value source's window head is the selected certificate coefficient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialValueWindowMeaning
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialCenterValuePacking.source
  FormulaSignSlotRadialValueCertificate.polynomial
local notation "Raw"=>FormulaSignSlotRadialValueRadiusSource.source

noncomputable def certificate (u:List Bool) (a:ℕ→ℝ):Polynomial (Polynomial ℝ):=
  FormulaSignSlotRadialValueCertificate.polynomial u (fun j=>a j.val)
noncomputable def Guard (C:List Bool) (a:ℕ→ℝ):Prop:=FormulaSignSlotRadialCenterValueFamily.Guards
  (FormulaSignSlotRadialCenterValueLayout.original C) (fun j=>a j.val)
  (fun i=>FormulaSignSlotRadialCenterValueLayout.tau C i.val)
  (fun i=>FormulaSignSlotRadialCenterValueLayout.degree C i.val)
noncomputable def head (C:List Bool) (ell:ℕ) (a:ℕ→ℝ):Polynomial ℝ:=
  ((FormulaSignSlotRadialCenterValuePacking.source C).coeff ell).map
    (FormulaSignSlotRadialFormalCenter.centerMap (FormulaSignSlotRadialCenterValueLayout.original C) (fun j=>a j.val))
noncomputable def rawHead (c:List Bool) (a:ℕ→ℝ):Polynomial ℝ:=
  IntegralPolynomialWindowTarski.baseHead Raw FormulaSignSlotRadialValueWindowCatalogue.centers
    FormulaSignSlotRadialValueWindowCatalogue.dimension_eq c (fun j=>a j.val)

private theorem one_inverse {n:ℕ} (p:Polynomial (MvPolynomial (Fin n) ℤ)):
    MvPolynomial.finSuccEquiv ℤ n (TriplePolynomialParameterFlatten.one p)=p:=
  (MvPolynomial.finSuccEquiv ℤ n).apply_symm_apply p

theorem raw_head_eq_head (c:List Bool) (a:ℕ→ℝ):rawHead c a=
    head (pairFst c) (Nat.fromBitsLE (pairSnd c)) a:=by
  unfold rawHead IntegralPolynomialWindowTarski.baseHead IntegralPolynomialRadiusReader.polynomial
    IntegralPolynomialRadiusReader.castPolynomial
  simp only [Fin.cast_refl,MvPolynomial.rename_id]
  exact congrArg (fun p:Polynomial (MvPolynomial (Fin (d (FormulaSignSlotRadialCenterValueLayout.original (pairFst c)))) ℤ)=>
    p.map (FormulaSignSlotRadialFormalCenter.centerMap
      (FormulaSignSlotRadialCenterValueLayout.original (pairFst c)) (fun j=>a j.val))) (one_inverse _)

attribute [local irreducible] head rawHead certificate

theorem raw_head_packet (C:List Bool) (ell:ℕ) (a:ℕ→ℝ):rawHead (pair C (BinaryNatCode.encode ell)) a=head C ell a:=by
  rw [raw_head_eq_head]
  simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem specialization (C:List Bool) (a:ℕ→ℝ) (HG:Guard C a):
    (FormulaSignSlotRadialCenterValuePacking.source C).map
      (Polynomial.mapRingHom (FormulaSignSlotRadialFormalCenter.centerMap
        (FormulaSignSlotRadialCenterValueLayout.original C) (fun j=>a j.val)))=
      certificate (FormulaSignSlotRadialCenterValueLayout.original C) a:=by
  simpa only [FormulaSignSlotRadialCenterValuePacking.source,certificate] using
    (FormulaSignSlotRadialCenterValueFamily.specialization _ _ _ _ HG)

theorem head_specialization (C:List Bool) (ell:ℕ) (a:ℕ→ℝ) (HG:Guard C a):
    head C ell a=(certificate (FormulaSignSlotRadialCenterValueLayout.original C) a).coeff ell:=by
  have H:=congrArg (fun p:Polynomial (Polynomial ℝ)=>p.coeff ell) (specialization C a HG)
  simpa only [head,Polynomial.coeff_map,Polynomial.coe_mapRingHom] using H

theorem certificate_degree (C:List Bool) (a:ℕ→ℝ) (HG:Guard C a):
    (certificate (FormulaSignSlotRadialCenterValueLayout.original C) a).natDegree≤
      FormulaSignSlotRadialCenterValuePacking.degree C:=by
  rw [←specialization C a HG]
  exact Polynomial.natDegree_map_le.trans (FormulaSignSlotRadialValueCatalogueBounds.target_degree C)

theorem guard_from_values (C u:List Bool) (HO:FormulaSignSlotRadialCenterValueLayout.original C=u)
    (a:ℕ→ℝ) (tau deg:ℕ→ℕ)
    (HT:∀i,i<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→FormulaSignSlotRadialCenterValueLayout.tau C i=tau i)
    (HD:∀i,i<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→FormulaSignSlotRadialCenterValueLayout.degree C i=deg i)
    (HG:FormulaSignSlotRadialCenterValueFamily.Guards u (fun j=>a j.val) (fun i=>tau i.val) (fun i=>deg i.val)):
    Guard C a:=by
  cases HO
  unfold Guard
  have HT0:(fun i:Fin (N (FormulaSignSlotRadialCenterValueLayout.original C)+d (FormulaSignSlotRadialCenterValueLayout.original C)+1)=>
      FormulaSignSlotRadialCenterValueLayout.tau C i.val)=(fun i=>tau i.val):=funext (fun i=>HT i.val i.isLt)
  have HD0:(fun i:Fin (N (FormulaSignSlotRadialCenterValueLayout.original C)+d (FormulaSignSlotRadialCenterValueLayout.original C)+1)=>
      FormulaSignSlotRadialCenterValueLayout.degree C i.val)=(fun i=>deg i.val):=funext (fun i=>HD i.val i.isLt)
  rw [HT0,HD0]
  exact HG


noncomputable def flatIndex (u:List Bool) (o k:ℕ):=o*FormulaSignSlotRadialValueWindowCatalogue.innerCount u+k
theorem flat_lt (u:List Bool) (o k:ℕ) (ho:o<FormulaSignSlotRadialValueCatalogueLayout.outerCount u)
    (hk:k<FormulaSignSlotRadialValueWindowCatalogue.innerCount u):
    flatIndex u o k<FormulaSignSlotRadialValueWindowCatalogue.count u:=by
  unfold flatIndex FormulaSignSlotRadialValueWindowCatalogue.count
  calc
    _<o*FormulaSignSlotRadialValueWindowCatalogue.innerCount u+FormulaSignSlotRadialValueWindowCatalogue.innerCount u:=Nat.add_lt_add_left hk _
    _=(o+1)*FormulaSignSlotRadialValueWindowCatalogue.innerCount u:=(Nat.succ_mul _ _).symm
    _≤_:=Nat.mul_le_mul_right _ ho

theorem row_flat (u:List Bool) (o k:ℕ) (hk:k<FormulaSignSlotRadialValueWindowCatalogue.innerCount u):
    FormulaSignSlotRadialValueWindowCatalogue.row (pair u (BinaryNatCode.encode (flatIndex u o k)))=
      IntegralPolynomialWindowTarskiCatalogue.row Raw
        (pair (FormulaSignSlotRadialValueCatalogueLayout.context (pair u (BinaryNatCode.encode o))) (BinaryNatCode.encode k)):=by
  have HO:FormulaSignSlotRadialValueWindowCatalogue.outerIndex u (flatIndex u o k)=o:=by
    unfold FormulaSignSlotRadialValueWindowCatalogue.outerIndex flatIndex
    rw [Nat.mul_comm o _,Nat.add_comm,Nat.add_mul_div_left _ _ (FormulaSignSlotRadialValueWindowCatalogue.innerCount_pos u),
      Nat.div_eq_of_lt hk,Nat.zero_add]
  have HK:FormulaSignSlotRadialValueWindowCatalogue.innerIndex u (flatIndex u o k)=k:=by
    unfold FormulaSignSlotRadialValueWindowCatalogue.innerIndex flatIndex
    rw [Nat.mul_comm o _,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hk]
  rw [FormulaSignSlotRadialValueWindowCatalogue.row_packet,FormulaSignSlotRadialValueWindowCatalogue.rawContext,HO,HK]

private theorem eval_cast {n m:ℕ} (hn:n=m) (p:MvPolynomial (Fin n) ℤ) (v:ℕ→ℝ):
    (MvPolynomial.rename (Fin.cast hn) p).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>v i.val):=by
  cases hn
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]

private noncomputable def sourceValue (S:IntegralFramedBankPolynomialModel.Source) (z:List Bool) (v:ℕ→ℝ):ℝ:=
  (S.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)
private theorem charged_value (C:ChargedPolynomialCatalogue.Input) (u:List Bool) (i:ℕ) (v:ℕ→ℝ):
    (ChargedPolynomialCatalogue.feature C u i).eval₂ (Int.castRingHom ℝ) (fun j=>v j.val)=
      sourceValue C.source (C.row (pair u (BinaryNatCode.encode i))) v:=
  eval_cast (C.dimension u i) _ v
attribute [local irreducible] sourceValue

theorem feature_inner (u:List Bool) (o k:ℕ) (hk:k<FormulaSignSlotRadialValueWindowCatalogue.innerCount u) (v:ℕ→ℝ):
    (FormulaSignSlotRadialValueWindowCatalogue.family.feature u (flatIndex u o k)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=
      ((IntegralPolynomialWindowTarskiCatalogue.family Raw FormulaSignSlotRadialValueWindowCatalogue.centers
        FormulaSignSlotRadialValueWindowCatalogue.dimension_eq).feature
          (FormulaSignSlotRadialValueCatalogueLayout.context (pair u (BinaryNatCode.encode o))) k).eval₂
            (Int.castRingHom ℝ) (fun i=>v i.val):=by
  have HX:(FormulaSignSlotRadialValueWindowCatalogue.family.feature u (flatIndex u o k)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=sourceValue FormulaSignSlotRadialValueWindowCatalogue.source
        (FormulaSignSlotRadialValueWindowCatalogue.row (pair u (BinaryNatCode.encode (flatIndex u o k)))) v:=
    charged_value FormulaSignSlotRadialValueWindowCatalogue.input u (flatIndex u o k) v
  have HY:((IntegralPolynomialWindowTarskiCatalogue.family Raw FormulaSignSlotRadialValueWindowCatalogue.centers
      FormulaSignSlotRadialValueWindowCatalogue.dimension_eq).feature
        (FormulaSignSlotRadialValueCatalogueLayout.context (pair u (BinaryNatCode.encode o))) k).eval₂
          (Int.castRingHom ℝ) (fun i=>v i.val)=sourceValue FormulaSignSlotRadialValueWindowCatalogue.source
            (IntegralPolynomialWindowTarskiCatalogue.row Raw
              (pair (FormulaSignSlotRadialValueCatalogueLayout.context (pair u (BinaryNatCode.encode o)))
                (BinaryNatCode.encode k))) v:=
    charged_value (IntegralPolynomialWindowTarskiCatalogue.input Raw FormulaSignSlotRadialValueWindowCatalogue.centers
      FormulaSignSlotRadialValueWindowCatalogue.dimension_eq) _ k v
  rw [row_flat u o k hk] at HX
  exact HX.trans HY.symm

theorem inner_count_le (u:List Bool) (o:ℕ):
    IntegralPolynomialWindowTarskiCatalogue.count Raw
      (FormulaSignSlotRadialValueCatalogueLayout.context (pair u (BinaryNatCode.encode o)))≤
        FormulaSignSlotRadialValueWindowCatalogue.innerCount u:=by
  have H:=FormulaSignSlotRadialValueCatalogueLayout.source_degree u o
  have HL:=Nat.add_le_add_right H 2
  unfold IntegralPolynomialWindowTarskiCatalogue.count IntegralPolynomialWindowTarskiCatalogue.limit
    FormulaSignSlotRadialValueWindowCatalogue.innerCount
  exact (Nat.mul_le_mul_left 6 (Nat.mul_le_mul HL (Nat.mul_le_mul HL HL))).trans_eq (by ring)

end LeanCanny.Encoding.FormulaSignSlotRadialValueWindowMeaning
