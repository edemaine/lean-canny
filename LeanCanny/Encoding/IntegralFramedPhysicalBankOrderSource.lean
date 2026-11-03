/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixPoint
public import LeanCanny.Algebra.IntegralMixedFramedWindowQuery
public import LeanCanny.Geometry.IntegralMixedFramedWindowQuery
/-! # Sparse positive-cleared order tests on one full physical tuple

The two binary powers remain implicit. Original current-Q scalar readers
supply both coefficients; no integer syntax or ordering reader is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalBankOrderSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (B : Bank) (left right : List Bool→ℕ)

noncomputable def window (index : List Bool→ℕ) :=IntegralMixedFramedWindowQuery.family
  B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key index
noncomputable def raw (index : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (atKey B.parameters B.plan B.data (B.key c)).count) ℤ :=
  RationalMonomialWindowQuery.raw (window B index) c
noncomputable def polynomial (c : List Bool) :=raw B right c-raw B left c
noncomputable def degree (c : List Bool) :=max ((window B left).weight c) ((window B right).weight c)
noncomputable def mass (c : List Bool) :=
  2*IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (B.key c)+1

theorem polynomial_degree (c : List Bool) : (polynomial B left right c).totalDegree≤degree B left right c :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le
    ((RationalMonomialWindowQuery.raw_degree (window B right) c).trans (le_max_right _ _))
    ((RationalMonomialWindowQuery.raw_degree (window B left) c).trans (le_max_left _ _)))

theorem polynomial_mass (c : List Bool) : MvMass.mass (polynomial B left right c)≤2^mass B c :=by
  have HR:=RationalMonomialWindowQuery.raw_mass (window B right) c
  have HL:=RationalMonomialWindowQuery.raw_mass (window B left) c
  apply (MvMass.sub_le _ _).trans
  apply (Nat.add_le_add HR HL).trans
  change 2^(2*IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (B.key c))+
    2^(2*IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (B.key c))≤2^(_+1)
  rw [pow_succ]
  omega

noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B) where
  arity c _:=(atKey B.parameters B.plan B.data (B.key c)).count
  newer _ _:=0
  polynomial c _:=polynomial B left right c
  degree c _:=degree B left right c
  mass c _:=mass B c
  dimension _ _:=Nat.zero_add _
  polynomial_degree c _:=polynomial_degree B left right c
  polynomial_mass c _:=polynomial_mass B left right c

private def origin (q : List Bool) :=pairFst (RationalSubstitution.IntegerBits.context q)
private theorem origin_FP : origin∈FP :=mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP
private def scalarPacket (q : List Bool) :=pair (pair (origin q) []) (pairSnd q)
private theorem scalarPacket_FP : scalarPacket∈FP :=mem_FP_pair (mem_FP_pair origin_FP (constFn_mem_FP [])) pairSnd_mem_FP

theorem degree_binary (h : IntegralFramedBankQuery.Access B) (hl : BinaryFn left) (hr : BinaryFn right) :
    BinaryFn (degree B left right) :=by
  have HL:=IntegralMixedFramedWindowQuery.weight_binary B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key left h.parameters h.key hl
  have HR:=IntegralMixedFramedWindowQuery.weight_binary B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key right h.parameters h.key hr
  exact (BinaryFn.ite (HL.le HR) HR HL).of_eq (fun _=>by simp only [degree,max_def];rfl)

theorem mass_binary (h : IntegralFramedBankQuery.Access B) : BinaryFn (mass B) :=
  ((BinaryFn.const 2).mul ((IntegralMixedFramedBankTermBits.coordinateMass_binary
    B.parameters h.parameters B.plan B.data h.nodes h.factor h.seed).comp h.key)).add (BinaryFn.const 1)

private theorem raw_coefficient (h : IntegralFramedBankQuery.Access B) (index : List Bool→ℕ) (hi : BinaryFn index)
    (W : List Bool→ℕ) (hW : UnaryFn W) :
    SpaceFunction (FixedWidthRowBits.value
      (fun q=>(atKey B.parameters B.plan B.data (B.key (origin q))).count) W
      (fun q=>RationalMonomialWindowQuery.raw (window B index) (origin q))
      RationalSubstitution.IntegerBits.selectedDegree pairSnd) :=by
  let F:=window B index
  let A:=IntegralMixedFramedBankScalars.access B.parameters h.parameters B.plan B.data
    h.liftedData h.controls h.bounds h.nodes h.factor h.seed B.bounds h.key hi
  have ED : SpaceFunction (fun q=>residueBits
      (F.scalars.denominator (origin q):ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=by
    refine (A.denominator.precompose scalarPacket scalarPacket_FP).congr (funext fun q=>?_)
    exact congrArg₂ (fun (v : ℤ) (m : ℕ)=>residueBits (v:ZMod m))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair];rfl)
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])
  have EN : SpaceFunction (fun q=>residueBits
      (F.scalars.numerator (origin q):ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=by
    refine (A.numerator.precompose scalarPacket scalarPacket_FP).congr (funext fun q=>?_)
    exact congrArg₂ (fun (v : ℤ) (m : ℕ)=>residueBits (v:ZMod m))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair];rfl)
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])
  have EP:=ModularResidueSpace.mulEvaluator pairSnd _ _ pairSnd_mem_FP ED EN
  have Eprod : SpaceFunction (fun q=>residueBits
      ((F.scalars.denominator (origin q)*F.scalars.numerator (origin q):ℤ):ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=
    EP.congr (funext fun _=>by simp only [Int.cast_mul])
  have HA : UnaryFn (fun q=>(atKey B.parameters B.plan B.data (B.key (origin q))).count) :=
    ((IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp h.key).comp origin_FP
  have HW:=IntegralMixedFramedWindowQuery.weight_binary B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key index h.parameters h.key hi
  have E:=FixedWidthMonomialBits.coefficient_evaluator
    (fun q=>(atKey B.parameters B.plan B.data (B.key (origin q))).count) W (index∘origin)
    (fun q=>F.weight (origin q)) RationalSubstitution.IntegerBits.selectedDegree
    (fun q=>F.scalars.denominator (origin q)*F.scalars.numerator (origin q)) pairSnd _ Eprod (fun _=>rfl)
    HA hW (hi.comp origin_FP) (HW.comp origin_FP) RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  exact E

theorem access (h : IntegralFramedBankQuery.Access B) (hl : BinaryFn left) (hr : BinaryFn right) :
    (source B left right).Access :=by
  have HD : BinaryFn (fun q=>degree B left right (origin q)):=(degree_binary B left right h hl hr).comp origin_FP
  have HW : UnaryFn (fun q=>(degree B left right (origin q)).size):=
    (UnaryFn.length HD.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  have EL:=raw_coefficient B h left hl _ HW
  have ER:=raw_coefficient B h right hr _ HW
  exact {
    newer:=UnaryFn.const 0
    degree:=(degree_binary B left right h hl hr).comp pairFst_mem_FP
    mass:=(mass_binary B h).comp pairFst_mem_FP
    coefficient:=FixedWidthRowBits.sub_evaluator _ _ _ _
      RationalSubstitution.IntegerBits.selectedDegree pairSnd pairSnd_mem_FP ER EL }

theorem raw_eval (index : List Bool→ℕ) (c : List Bool)
    (hi : index c<(atKey B.parameters B.plan B.data (B.key c)).count)
    (z : Fin (atKey B.parameters B.plan B.data (B.key c)).count→ℝ) :
    (raw B index c).eval₂ (Int.castRingHom ℝ) z=
      ((atKey B.parameters B.plan B.data (B.key c)).common:ℝ)^2*
        LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c)) z ⟨index c,hi⟩ :=by
  let F:=window B index
  have HE:=LeanCanny.Geometry.IntegralMixedFramedWindowQuery.coordinate
    B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key index c hi z
  have HQ : (F.scalars.denominator c:ℝ)≠0:=Int.cast_ne_zero.mpr
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero B.parameters B.plan B.data (B.key c))
  rw [raw,RationalMonomialWindowQuery.raw_eval (window B index) c z hi]
  have HC : (F.scalars.denominator c:ℝ)*(F.scalars.numerator c:ℝ)*z ⟨index c,hi⟩^F.weight c=
      (F.scalars.denominator c:ℝ)^2*((F.scalars.numerator c:ℝ)*z ⟨index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)) :=by
    field_simp
  exact HC.trans (congrArg (fun v : ℝ=>(F.scalars.denominator c:ℝ)^2*v) HE)

theorem polynomial_eval (c : List Bool)
    (hl : left c<(atKey B.parameters B.plan B.data (B.key c)).count)
    (hr : right c<(atKey B.parameters B.plan B.data (B.key c)).count)
    (z : Fin (atKey B.parameters B.plan B.data (B.key c)).count→ℝ) :
    (polynomial B left right c).eval₂ (Int.castRingHom ℝ) z=
      ((atKey B.parameters B.plan B.data (B.key c)).common:ℝ)^2*
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c)) z ⟨right c,hr⟩-
         LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c)) z ⟨left c,hl⟩) :=by
  rw [polynomial,MvPolynomial.eval₂_sub,raw_eval B right c hr z,raw_eval B left c hl z]
  ring

variable (T : IntegralMixedHeaderTablesBits.Tables)
  (hT : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)

noncomputable def value :=IntegralFramedPhysicalSuffixTest.value B T hT (source B left right)

theorem evaluator (h : IntegralFramedBankQuery.Access B) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hl : BinaryFn left) (hr : BinaryFn right)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalBankTerm.input B))) :
    SpaceFunction (value B left right T hT) :=
  IntegralFramedPhysicalSuffixTest.evaluator B T hT (source B left right) h ht
    (access B left right h hl hr) ER

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (hl : left c<(atKey B.parameters B.plan B.data (B.key c)).count)
    (hr : right c<(atKey B.parameters B.plan B.data (B.key c)).count) :
    value B left right T hT (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (
        LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c))
          (IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv) ⟨right c,hr⟩-
        LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c))
          (IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv) ⟨left c,hl⟩)) :=by
  have HE:=IntegralFramedPhysicalSuffixTest.packet_scalar B T hT (source B left right) c w d hv
  have HC (i : Fin (atKey B.parameters B.plan B.data (B.key c)).count) :
      Fin.cast ((source B left right).dimension c d) (FixedWidthSuffixLiftBits.shift 0 i)=i :=by
    apply Fin.ext
    change 0+i.val=i.val
    omega
  change value B left right T hT (pair (pair c w) d)=_ at HE
  have HQ : (0:ℝ)<((atKey B.parameters B.plan B.data (B.key c)).common:ℝ)^2 :=
    sq_pos_of_ne_zero (Int.cast_ne_zero.mpr
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero B.parameters B.plan B.data (B.key c)))
  simpa only [source,HC,polynomial_eval B left right c hl hr,sign_mul,sign_pos HQ,one_mul] using HE


end LeanCanny.Encoding.IntegralFramedPhysicalBankOrderSource
