/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalTest
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
public import LeanCanny.Encoding.IntegralFramedBankPolynomialEmbedding
/-! # Actual principal-coefficient features on the joint center columns

Context is pair joint-header [coordinate,tau,target-degree,principal-order,radius-degree].
All center variables are retained as the same joint original coordinates.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialRetainedPrincipalTest.source

def header (z : List Bool) := pairFst z
def slot (i : ℕ) (z : List Bool) := WordList.reader (pair (pairSnd z) (BinaryNatCode.encode i))
noncomputable def read (z : List Bool) := pair
  (pair (FormulaSignSlotRadialCoordinatePacket.writer
    (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (slot 0 z)))
    (pair (slot 1 z) (slot 2 z))) (pair (slot 3 z) (slot 4 z))
noncomputable def radial (z : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.original (pairFst (read z))
theorem slot_FP (i : ℕ) : slot i ∈ FP := mem_FP_comp
  (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP _)) WordList.reader_FP
theorem read_FP : read ∈ FP := by
  have HS : (fun z => FormulaSignSlotRadialJointLayout.source true (header z)) ∈ FP :=
    mem_FP_comp (f := header) (g := FormulaSignSlotRadialJointLayout.source true)
      pairFst_mem_FP (FormulaSignSlotRadialJointLayout.source_FP true)
  have HC : (fun z => pair (FormulaSignSlotRadialJointLayout.source true (header z)) (slot 0 z)) ∈ FP :=
    mem_FP_pair HS (slot_FP 0)
  have HR : (fun z => FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (slot 0 z))) ∈ FP :=
    mem_FP_comp (f := fun z => pair (FormulaSignSlotRadialJointLayout.source true (header z)) (slot 0 z))
      (g := FormulaSignSlotRadialCoordinatePacket.writer) HC FormulaSignSlotRadialCoordinatePacket.writer_FP
  exact mem_FP_pair (mem_FP_pair HR (mem_FP_pair (slot_FP 1) (slot_FP 2)))
    (mem_FP_pair (slot_FP 3) (slot_FP 4))
theorem radial_root (z : List Bool) : pairFst (radial z)=FormulaSignSlotRadialJointLayout.source true (header z) := by
  simp only [radial,read,FormulaSignSlotRadialCenterPrincipalFamily.original,FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]
theorem center_count (z : List Bool) : (S).arity (read z)=FormulaSignSlotRadialJointLayout.centerCount (header z) :=
  congrArg FormulaSignSlotCenteredRadialGraph.d (radial_root z)

noncomputable def dimension (z : List Bool) := FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary : UnaryFn dimension := FormulaSignSlotRadialJointLayout.dimension_unary.comp pairFst_mem_FP
theorem column_lt (z : List Bool) (i : Fin ((S).arity (read z))) : 4*i.val<dimension z := by
  have HI := i.isLt
  have HC := center_count z
  have HF := FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
  change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
    (FormulaSignSlotRadialJointLayout.centerCount (header z)+1)≤_ at HF
  unfold dimension FormulaSignSlotRadialJointLayout.dimension
  omega
noncomputable def embedding (z : List Bool) : Fin ((S).arity (read z)) → Fin (dimension z) :=
  fun i => ⟨4*i.val,column_lt z i⟩
theorem injective (z : List Bool) : Function.Injective (embedding z) := by
  intro i j H
  apply Fin.ext
  have HE := congrArg Fin.val H
  change 4*i.val=4*j.val at HE
  omega
def columnCode (q : List Bool) := BinaryNatCode.encode (4*Nat.fromBitsLE (pairSnd q))
theorem columnCode_FP : columnCode ∈ FP := ((BinaryFn.const 4).mul (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP
theorem columnCode_packet (z : List Bool) (i : Fin ((S).arity (read z))) :
    columnCode (pair z (BinaryNatCode.encode i.val))=BinaryNatCode.encode (embedding z i).val := by
  simp only [columnCode,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]
attribute [local irreducible] read
theorem degree_fit (z : List Bool) : (S).degree (read z)<2^(S).width (read z) := by
  dsimp only [FormulaSignSlotRadialRetainedPrincipalTest.source,FormulaSignSlotRadialCenterPrincipalSource.degree,
    FormulaSignSlotRadialCenterPrincipalSource.width,FormulaSignSlotRadialCenterPrincipalFamily.width]
  have H : FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (pairFst (read z)) ≤
      FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (pairFst (read z))+
        FormulaSignSlotRadialCenterPrincipalFamily.inputBound (pairFst (read z)) := Nat.le_add_right _ _
  exact H.trans_lt (Nat.lt_size_self _)

noncomputable def source : IntegralFramedBankPolynomialModel.Source :=
  IntegralFramedBankPolynomialEmbedding.source S read dimension embedding degree_fit
noncomputable def access : IntegralFramedBankPolynomialModel.Access source :=
  IntegralFramedBankPolynomialEmbedding.access S read dimension embedding degree_fit
    FormulaSignSlotRadialRetainedPrincipalTest.access read_FP dimension_unary injective columnCode columnCode_FP columnCode_packet

private theorem eval_four {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (f : Fin a → Fin b)
    (hf : ∀ i, (f i).val=4*i.val) (v : ℕ → ℝ) :
    (rename f p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      p.eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val)) := by
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext i
  exact congrArg v (hf i)

theorem evaluation (z : List Bool) (v : ℕ → ℝ) :
    (source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)=
      ((S).polynomial (read z)).eval₂ (Int.castRingHom ℝ) (fun i => v (4*i.val)) :=
  eval_four ((S).polynomial (read z)) (embedding z) (fun _ => rfl) v

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalSource
