/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalContext
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
public import LeanCanny.Encoding.ImplicitSourceGramGridCoordinateSource
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
public import LeanCanny.Algebra.IntegerPolynomialZeroRootSource
/-! # One own external tuple supplies the finite coordinate algebra

The auxiliary coordinate prelude has n coordinate leaves followed by zero.
The last zero makes its retained index n-i match the existing slack algebra.
The later marked prelude still has exactly n+8 births.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalCoordinates
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open FormulaSignSlotRadialExternalContext IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "A" => FormulaSignSlotRadialJointStratumNative.access
local notation "positive" => FormulaSignSlotRadialJointStratumSampler.positive
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
attribute [local irreducible] ImplicitSourceGramGrid.polynomial CoerciveBoxGramEliminant.polynomial
  FormulaSignSlotRadialJointStratum.polynomial ImplicitSourceGramGrid.degree ImplicitSourceGramGrid.mass

def tag (q : List Bool) := Nat.fromBitsLE (pairSnd q)
noncomputable def source : IntegerPolynomialRootQueriesBits.Source :=
  choose (fun q => tag q<number (pairFst q))
    (reindex (ImplicitSourceGramGridCoordinateSource.source S positive) slotQuery)
    IntegerPolynomialZeroRootSource.source

theorem access : IntegerPolynomialRootQueriesBits.Access source :=
  choose_access ((BinaryFn.fromBits pairSnd_mem_FP).lt
    ((BinaryFn.ofUnary number_unary).comp pairFst_mem_FP)) _ _
    (reindex_access _ (ImplicitSourceGramGridCoordinateSource.access S A positive) slotQuery_FP)
    IntegerPolynomialZeroRootSource.access

theorem nonzero (q : List Bool) : source.polynomial q≠0 := by
  dsimp only [source,choose,reindex]
  split_ifs
  · exact ImplicitSourceGramGridCoordinateSource.nonzero S positive _
  · exact Polynomial.X_ne_zero

noncomputable def degreeBound (ctx : List Bool) := ImplicitSourceGramGrid.degree S (gridContext ctx)+1
noncomputable def massBound (ctx : List Bool) := ImplicitSourceGramGrid.mass S (gridContext ctx)+1
theorem degreeBound_binary : BinaryFn degreeBound := by
  have H : BinaryFn (fun c => ImplicitSourceGramGrid.degree S (gridContext c)) :=
    (ImplicitSourceGramGrid.degree_binary S A).comp gridContext_FP
  exact H.add (BinaryFn.const 1)
theorem massBound_binary : BinaryFn massBound := by
  have H : BinaryFn (fun c => ImplicitSourceGramGrid.mass S (gridContext c)) :=
    (ImplicitSourceGramGrid.mass_binary S A).comp gridContext_FP
  exact H.add (BinaryFn.const 1)

private theorem coordinate_degree (Q : IntegralFramedBankPolynomialModel.Source) (hp : ∀u,0<Q.arity u) (q : List Bool) :
    (ImplicitSourceGramGridCoordinateSource.source Q hp).degree q=ImplicitSourceGramGrid.degree Q (pairFst q) := rfl
private theorem coordinate_mass (Q : IntegralFramedBankPolynomialModel.Source) (hp : ∀u,0<Q.arity u) (q : List Bool) :
    (ImplicitSourceGramGridCoordinateSource.source Q hp).mass q=ImplicitSourceGramGrid.mass Q (pairFst q) := rfl
private theorem choose_degree_le (p : List Bool → Prop) (Q T : IntegerPolynomialRootQueriesBits.Source)
    (f : List Bool → List Bool) (B : List Bool → ℕ) (q : List Bool)
    (hQ : Q.degree (f q)≤B q) (hT : T.degree q≤B q) :
    (choose p (reindex Q f) T).degree q≤B q := by
  change (if p q then Q.degree (f q) else T.degree q)≤B q
  split_ifs <;> assumption
private theorem choose_mass_le (p : List Bool → Prop) (Q T : IntegerPolynomialRootQueriesBits.Source)
    (f : List Bool → List Bool) (B : List Bool → ℕ) (q : List Bool)
    (hQ : Q.mass (f q)≤B q) (hT : T.mass q≤B q) :
    (choose p (reindex Q f) T).mass q≤B q := by
  change (if p q then Q.mass (f q) else T.mass q)≤B q
  split_ifs <;> assumption

theorem degree_le (q : List Bool) : source.degree q≤degreeBound (pairFst q) := by
  apply choose_degree_le _ _ _ _ (fun q => degreeBound (pairFst q)) q
  · rw [coordinate_degree,show pairFst (slotQuery q)=gridContext (pairFst q) from pairFst_pair _ _]
    exact Nat.le_succ _
  · exact Nat.succ_le_succ (Nat.zero_le _)

theorem mass_le (q : List Bool) : source.mass q≤massBound (pairFst q) := by
  apply choose_mass_le _ _ _ _ (fun q => massBound (pairFst q)) q
  · rw [coordinate_mass,show pairFst (slotQuery q)=gridContext (pairFst q) from pairFst_pair _ _]
    exact Nat.le_succ _
  · exact Nat.zero_le _

def OwnValid (ctx : List Bool) : Prop :=
  SquareSampleCompleteVertices.Valid F (gridContext ctx) (ownWord ctx)
noncomputable def index (ctx : List Bool) (i : ℕ) : Fin ((F).count (gridContext ctx)) :=
  SquareSampleInput.selected F (gridContext ctx) (BinaryNatCode.encode (slot ctx i))
noncomputable def point (ctx : List Bool) (hw : OwnValid ctx) (i : ℕ) : ℝ :=
  (SquareSampleCompleteVertices.candidate F (gridContext ctx) (ownWord ctx) hw).val (index ctx i)
noncomputable def values (ctx : List Bool) (hw : OwnValid ctx) (i : ℕ) : ℝ :=
  if i<number ctx then point ctx hw i else 0

theorem coordinate_polynomial (ctx : List Bool) (i : ℕ) (hi : i<number ctx) :
    source.polynomial (pair ctx (BinaryNatCode.encode i))=
      (ImplicitSourceGramGridCoordinateSource.source S positive).polynomial
        (pair (gridContext ctx) (BinaryNatCode.encode (slot ctx i))) := by
  simp only [source,choose,reindex,Function.comp_apply,slotQuery,tag,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,hi,ite_true]

theorem roots (ctx : List Bool) (hw : OwnValid ctx) (i : ℕ) :
    (source.polynomial (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (values ctx hw i)=0 := by
  by_cases hi : i<number ctx
  · rw [values,ite_eq_left hi,coordinate_polynomial ctx i hi]
    exact ImplicitSourceGramGridCoordinateSource.point_root_query S positive
      (gridContext ctx) (ownWord ctx) (BinaryNatCode.encode (slot ctx i)) hw
  · have HC : ¬tag (pair ctx (BinaryNatCode.encode i))<number (pairFst (pair ctx (BinaryNatCode.encode i))) := by
      simpa only [tag,pairSnd_pair,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hi
    simp only [source,choose,reindex,HC,ite_false,values,hi,IntegerPolynomialZeroRootSource.source,
      Polynomial.eval₂_X]

theorem count_packet (H : List Bool) (K : ℕ) (Gamma : List Bool) :
    (F).count (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)=
      FormulaSignSlotRadialJointLayout.dimension H+1 := by
  change FormulaSignSlotRadialJointLayout.dimension
    (FormulaSignSlotRadialJointStratum.header (ImplicitSourceGramGrid.header
      (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma)))+1=_
  rw [ImplicitSourceGramGrid.header,pairFst_pair,FormulaSignSlotRadialJointStratum.header,
    FormulaSignSlotRadialJointStratum.packet,pairFst_pair]

theorem index_packet_val (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (w : List Bool)
    (i : Fin (FormulaSignSlotRadialJointLayout.circleCount s H)) :
    (index (packet H K Gamma label s w) i.val).val=FormulaSignSlotRadialJointLayout.column (if s then 1 else 0) i.val := by
  have HI := slot_lt H s i
  have HC := count_packet H K Gamma
  simp only [index,gridContext_packet,slot_packet,SquareSampleInput.selected,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (by omega)

end LeanCanny.Encoding.FormulaSignSlotRadialExternalCoordinates
