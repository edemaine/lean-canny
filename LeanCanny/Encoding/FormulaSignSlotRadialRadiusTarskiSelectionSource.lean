/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSource
/-! # Actual head and pseudo-seed coefficient sources for finite degree selection -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def seed (c:List Bool):=PseudoRemainder.seed (head c) (query c) (degree c) (bound c)
noncomputable def seedCoefficientDegree (c:List Bool):=
  MultivariateTarskiDegreeBounds.seedDegreeBound (bound c) (inputBound c) 2
noncomputable def seedInputMass (c:List Bool):=
  FixedWidthTarskiMass.seedMass (bound c) (inputBound c) 4 (headInputMass c) 2
noncomputable def selectionMass (c:List Bool):=headInputMass c+seedInputMass c

theorem seedCoefficientDegree_binary :BinaryFn seedCoefficientDegree:=
  MultivariateTarskiDegreeBounds.seedDegreeBound_binary bound_binary inputBound_binary (BinaryFn.const 2)
theorem seedInputMass_binary :BinaryFn seedInputMass:=FixedWidthTarskiMass.seedMass_binary
  bound_binary inputBound_binary (BinaryFn.const 4) headInputMass_binary (BinaryFn.const 2)
theorem selectionMass_binary :BinaryFn selectionMass:=headInputMass_binary.add seedInputMass_binary

theorem seed_degree (c:List Bool):(seed c).natDegree<degree c:=
  PseudoRemainder.seed_natDegree_lt _ _ _ _ (family.degree_pos c) (input_degree c)
theorem seed_coefficient_degree (c:List Bool) (i:ℕ):((seed c).coeff i).totalDegree≤seedCoefficientDegree c:=
  MultivariateTarskiDegreeBounds.seed_coefficient _ _ _ _ _ _ (head_coefficient_degree c) (query_coefficient_degree c) i

theorem input_le_output (c:List Bool):inputBound c≤outputBound c:=by
  unfold outputBound MultivariateTarskiDegreeBounds.principalDegreeBound
  exact (le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
theorem seed_le_output (c:List Bool):seedCoefficientDegree c≤outputBound c:=by
  unfold seedCoefficientDegree outputBound MultivariateTarskiDegreeBounds.principalDegreeBound
  exact (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))

attribute [local irreducible] head query arity width inputBound outputBound degree seedDegree bound seed

theorem seed_coefficient_mass (c:List Bool) (i:ℕ):MvMass.mass ((seed c).coeff i)≤2^seedInputMass c:=by
  let p:=(seed c).coeff i
  let W:=p.totalDegree.size
  let enc:MvPolynomial (Fin (arity c)) ℤ→+*ℤ[X]:=FixedWidthKronecker.encode (arity c) W
  apply (FixedWidthTarskiMass.mass_le_encoded_exact (arity c) W p ?_).trans
  · change coefficientMass (enc p)≤_
    have HE:enc p=(PseudoRemainder.seed ((head c).map enc) ((query c).map enc) (degree c) (bound c)).coeff i:=by
      rw [PseudoRemainder.seed_map,Polynomial.coeff_map]
      simp only [p,seed]
    rw [HE]
    apply (NestedMass.coeff_le _ i).trans
    apply FixedWidthTarskiMass.encoded_seed_mass _ _ _ _ (inputBound c) 4 (headInputMass c) 2
    · exact Polynomial.natDegree_map_le.trans (head_degree c)
    · exact Polynomial.natDegree_map_le.trans (query_degree c)
    · intro k
      rw [Polynomial.coeff_map]
      exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (head_coefficient_mass c k)
    · intro k
      rw [Polynomial.coeff_map]
      exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (query_coefficient_mass c k)
  · intro e he j
    exact ((MvPolynomial.monomial_le_degreeOf j he).trans (MvPolynomial.degreeOf_le_totalDegree _ j)).trans_lt
      (Nat.lt_size_self _)

noncomputable def decodedSeedReader (G:FixedWidthTarskiPrincipalBits.Family)
    (B:FixedWidthTarskiPrincipalBits.Access G):CertifiedPolynomial.BivariateReader
      (FixedWidthBivariateReader.polynomial G.arity G.width
        (fun c=>PseudoRemainder.seed (G.head c) (G.query c) (G.degree c) (G.bound c))):=by
  have HE:(fun c=>(FixedWidthTarskiPrincipalBits.seedFamily G).seed c)=
      FixedWidthBivariateReader.polynomial G.arity G.width
        (fun c=>PseudoRemainder.seed (G.head c) (G.query c) (G.degree c) (G.bound c)):=by
    funext c
    exact FixedWidthTarskiPrincipalBits.seed_encoded G c
  exact HE ▸ BivariateTarskiSeedBits.reader (FixedWidthTarskiPrincipalBits.seedAccess B)

noncomputable def seedReader:CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial arity width seed):=by
  unfold seed
  exact decodedSeedReader family access

theorem output_fit (c:List Bool):outputBound c<2^width c:=by
  unfold width
  exact (by omega:outputBound c≤outputBound c+inputBound c+1).trans_lt (Nat.lt_size_self _)

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily

namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSelectionSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotRadialRadiusTarskiSource (original order arity width)
open RationalSubstitution.IntegerBits (context context_mem_FP selectedDegree selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRadiusTarskiFamily.head
  FormulaSignSlotRadialRadiusTarskiFamily.seed FormulaSignSlotRadialRadiusTarskiFamily.arity
  FormulaSignSlotRadialRadiusTarskiFamily.width FormulaSignSlotRadialRadiusTarskiFamily.inputBound
  FormulaSignSlotRadialRadiusTarskiFamily.outputBound FormulaSignSlotRadialRadiusTarskiFamily.degree
  FormulaSignSlotRadialRadiusTarskiFamily.seedDegree FormulaSignSlotRadialRadiusTarskiFamily.bound
  FormulaSignSlotRadialRadiusTarskiFamily.seedCoefficientDegree FormulaSignSlotRadialRadiusTarskiFamily.selectionMass
  FormulaSignSlotRadialRadiusTarskiFamily.seedInputMass FormulaSignSlotRadialRadiusTarskiFamily.headInputMass
local notation "F"=>FormulaSignSlotRadialRadiusTarskiFamily.family

noncomputable def polynomial (headOnly:Bool) (z:List Bool):MvPolynomial (Fin (arity z)) ℤ:=
  if headOnly then (FormulaSignSlotRadialRadiusTarskiFamily.head (original z)).coeff (order z)
  else (FormulaSignSlotRadialRadiusTarskiFamily.seed (original z)).coeff (order z)
noncomputable def mass (z:List Bool):=FormulaSignSlotRadialRadiusTarskiFamily.selectionMass (original z)

theorem polynomial_degree (headOnly:Bool) (z:List Bool):(polynomial headOnly z).totalDegree≤
    FormulaSignSlotRadialRadiusTarskiSource.degree z:=by
  cases headOnly
  · exact (FormulaSignSlotRadialRadiusTarskiFamily.seed_coefficient_degree _ _).trans
      (FormulaSignSlotRadialRadiusTarskiFamily.seed_le_output _)
  · exact (FormulaSignSlotRadialRadiusTarskiFamily.head_coefficient_degree _ _).trans
      (FormulaSignSlotRadialRadiusTarskiFamily.input_le_output _)
theorem polynomial_mass (headOnly:Bool) (z:List Bool):MvMass.mass (polynomial headOnly z)≤2^mass z:=by
  cases headOnly
  · exact (FormulaSignSlotRadialRadiusTarskiFamily.seed_coefficient_mass _ _).trans
      (Nat.pow_le_pow_right (by decide) (by unfold mass FormulaSignSlotRadialRadiusTarskiFamily.selectionMass;omega))
  · exact (FormulaSignSlotRadialRadiusTarskiFamily.head_coefficient_mass _ _).trans
      (Nat.pow_le_pow_right (by decide) (by unfold mass FormulaSignSlotRadialRadiusTarskiFamily.selectionMass;omega))

noncomputable def source (headOnly:Bool):IntegralFramedBankPolynomialModel.Source where
  arity:=arity
  width:=width
  degree:=FormulaSignSlotRadialRadiusTarskiSource.degree
  mass:=mass
  polynomial:=polynomial headOnly
  fit z i:=(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((polynomial_degree headOnly z).trans_lt (FormulaSignSlotRadialRadiusTarskiSource.degree_fit z))
  polynomial_degree:=polynomial_degree headOnly
  polynomial_mass:=polynomial_mass headOnly

noncomputable def coefficient (headOnly:Bool):=FixedWidthRowBits.value (arity∘context) (width∘context)
  (fun q=>polynomial headOnly (context q)) selectedDegree pairSnd

theorem evaluator (headOnly:Bool):SpaceFunction (coefficient headOnly):=by
  let read:=original∘context
  let y:=order∘context
  have HR:read∈FP:=mem_FP_comp context_mem_FP FormulaSignSlotRadialRadiusTarskiSource.original_FP
  have HY:BinaryFn y:=FormulaSignSlotRadialRadiusTarskiSource.order_binary.comp context_mem_FP
  cases headOnly
  · exact FixedWidthBivariateRowBits.evaluator FormulaSignSlotRadialRadiusTarskiFamily.arity
      FormulaSignSlotRadialRadiusTarskiFamily.width FormulaSignSlotRadialRadiusTarskiFamily.seed
      FormulaSignSlotRadialRadiusTarskiFamily.seedReader FormulaSignSlotRadialRadiusTarskiFamily.arity_unary
      FormulaSignSlotRadialRadiusTarskiFamily.width_unary
      (fun c i=>((FormulaSignSlotRadialRadiusTarskiFamily.seed_coefficient_degree c i).trans
        (FormulaSignSlotRadialRadiusTarskiFamily.seed_le_output c)).trans_lt
          (FormulaSignSlotRadialRadiusTarskiFamily.output_fit c)) read HR y HY
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  · exact FixedWidthBivariateRowBits.evaluator FormulaSignSlotRadialRadiusTarskiFamily.arity
      FormulaSignSlotRadialRadiusTarskiFamily.width FormulaSignSlotRadialRadiusTarskiFamily.head
      FormulaSignSlotRadialRadiusTarskiFamily.headReader FormulaSignSlotRadialRadiusTarskiFamily.arity_unary
      FormulaSignSlotRadialRadiusTarskiFamily.width_unary
      (fun c i=>((FormulaSignSlotRadialRadiusTarskiFamily.head_coefficient_degree c i).trans
        (FormulaSignSlotRadialRadiusTarskiFamily.input_le_output c)).trans_lt
          (FormulaSignSlotRadialRadiusTarskiFamily.output_fit c)) read HR y HY
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP

theorem packet (headOnly:Bool) (z bits modulus:List Bool):coefficient headOnly (pair (pair z bits) modulus)=
    residueBits ((((source headOnly).polynomial z).coeff (nativeExponent (Equiv.refl _) ((source headOnly).width z)
      (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=
  FormulaSignSlotRadialRadiusTarskiSource.row_packet arity width (polynomial headOnly) z bits modulus

noncomputable def access (headOnly:Bool):IntegralFramedBankPolynomialModel.Access (source headOnly) where
  arity:=FormulaSignSlotRadialRadiusTarskiSource.arity_unary
  width:=FormulaSignSlotRadialRadiusTarskiSource.width_unary
  degree:=FormulaSignSlotRadialRadiusTarskiSource.degree_binary
  mass:=FormulaSignSlotRadialRadiusTarskiFamily.selectionMass_binary.comp FormulaSignSlotRadialRadiusTarskiSource.original_FP
  coefficient:=coefficient headOnly
  evaluator:=evaluator headOnly
  packet:=packet headOnly

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSelectionSource
