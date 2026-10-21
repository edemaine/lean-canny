/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzAffinePolynomialSpace
public import LeanCanny.Algebra.MacaulayPolynomialSpace
public import LeanCanny.Algebra.PrincipalPadding

/-! # Costed polynomial principal minors on the original index space

An FP row selector keeps an original entry or supplies the appropriate identity
coefficient. The original entry child is space-bounded only on selected rows.
The affine determinant backend therefore evaluates a selected coefficient of
the padded principal deformation with the original child workspace included.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialPrincipalBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

def identityInput (q : List Bool) : List Bool :=
  pair (pair (pairFst q) (PolynomialAffineEntryBits.target q))
    (pair (PolynomialAffineEntryBits.row q) (PolynomialAffineEntryBits.col q))

theorem identityInput_mem_FP : identityInput ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP PolynomialAffineEntryBits.target_mem_FP)
    (mem_FP_pair PolynomialAffineEntryBits.row_mem_FP PolynomialAffineEntryBits.col_mem_FP)

theorem identityInput_packet (c : List Bool) (r s d : ℕ) :
    identityInput (PolynomialAffineEntryBits.packet c r s d) =
      MacaulayBits.packet (pair c (BinaryNatCode.encode d)) r s := by
  simp only [identityInput, PolynomialAffineEntryBits.packet, PolynomialAffineEntryBits.row,
    PolynomialAffineEntryBits.col, PolynomialAffineEntryBits.target, MacaulayBits.packet, pairFst_pair, pairSnd_pair]

noncomputable def entry (pred : List Bool → Prop) (modulus reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if pred q then reader q else MacaulayPolynomial.constantEntry modulus (identityInput q)

theorem evaluator {pred : List Bool → Prop} {modulus reader : List Bool → List Bool}
    (hp : FPPred pred) (hm : modulus ∈ FP) (E : SpaceFunction reader) : SpaceFunction (entry pred modulus reader) := by
  have EC := SpaceFunction.ofFP _ (mem_FP_comp identityInput_mem_FP (MacaulayPolynomial.constantEntry_mem_FP hm))
  have ES := SpaceFunction.branch (fun q => decide (pred q)) hp.flag_mem_FP E EC
  exact ES.congr (funext fun q => by simp only [entry, Function.comp_apply, decide_eq_true_eq])

end PolynomialPrincipalBits

namespace BerkowitzPolynomial
open Complexity LeanCanny.Encoding LeanCanny.Computation
open MatrixPower
open scoped Classical

noncomputable def ModularFamily.principal (F : ModularFamily) (s : (c : List Bool) → Finset (Fin (F.dimension c))) : ModularFamily where
  dimension := F.dimension
  modulus := F.modulus
  degree := F.degree
  matrix c := PrincipalPadding.matrix (F.matrix c) (s c)
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def ModularAccess.principal {F : ModularFamily} (a : ModularAccess F)
    (s : (c : List Bool) → Finset (Fin (F.dimension c))) (pred : List Bool → Prop)
    (hpred : ∀ c (r t : Fin (F.dimension c)) d, pred (PolynomialAffineEntryBits.packet c r.val t.val d) ↔ r ∈ s c) :
    ModularAccess (F.principal s) where
  dimension := a.dimension
  modulus := a.modulus
  degree := a.degree
  entry := PolynomialPrincipalBits.entry pred a.modulus a.entry
  dimension_eq := a.dimension_eq
  modulus_eq := a.modulus_eq
  degree_eq := a.degree_eq
  entry_eq c r t d := by
    change Fin (F.dimension c) at r t
    change PolynomialPrincipalBits.entry pred a.modulus a.entry (PolynomialAffineEntryBits.packet c r.val t.val d) =
      residueBits ((PrincipalPadding.matrix (F.matrix c) (s c) r t).coeff d)
    by_cases hr : r ∈ s c
    · rw [PolynomialPrincipalBits.entry, ite_eq_left ((hpred c r t d).mpr hr)]
      simpa only [PrincipalPadding.matrix, ite_eq_left hr, PolynomialAffineEntryBits.packet] using a.entry_eq c r t d
    · rw [PolynomialPrincipalBits.entry, ite_eq_right (fun h => hr ((hpred c r t d).mp h)), PolynomialPrincipalBits.identityInput_packet]
      have h := MacaulayPolynomial.constantEntry_packet a.modulus c (F.modulus c) d r.val t.val (a.modulus_eq c)
      have he : (if r.val = t.val then (1 : Polynomial (ZMod (F.modulus c))) else 0) =
          (1 : Matrix (Fin (F.dimension c)) (Fin (F.dimension c)) (Polynomial (ZMod (F.modulus c)))) r t := by
        simp only [Matrix.one_apply, Fin.ext_iff]
      rw [he] at h
      simpa only [PrincipalPadding.matrix, ite_eq_right hr] using h

attribute [local irreducible] PolynomialPrincipalBits.entry

theorem ModularAccess.principalEntryEvaluator {F : ModularFamily} (a : ModularAccess F)
    (s : (c : List Bool) → Finset (Fin (F.dimension c))) (pred : List Bool → Prop)
    (hpred : ∀ c (r t : Fin (F.dimension c)) d, pred (PolynomialAffineEntryBits.packet c r.val t.val d) ↔ r ∈ s c)
    (hp : FPPred pred) (hm : a.modulus ∈ FP) (E : SpaceFunction a.entry) :
    SpaceFunction (a.principal s pred hpred).entry := by
  have ES := PolynomialPrincipalBits.evaluator hp hm E
  change SpaceFunction (PolynomialPrincipalBits.entry pred a.modulus a.entry)
  exact ES

end BerkowitzPolynomial

namespace BerkowitzAffinePolynomial
open Complexity LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

noncomputable def Family.principal (F : Family) (s : (c : List Bool) → Finset (Fin (F.source.dimension c))) : Family where
  source := F.source.principal s
  inner := F.inner
  outer := F.outer
  bound := F.bound
  entry_degree c r t := by
    change Fin (F.source.dimension c) at r t
    change (if r ∈ s c then F.source.matrix c r t else
      (if r = t then (1 : Polynomial (ZMod (F.source.modulus c))) else 0)).natDegree ≤ F.bound c
    split_ifs with hr hrt
    · exact F.entry_degree c r t
    · simp
    · simp

noncomputable def Access.principal {F : Family} (a : Access F)
    (s : (c : List Bool) → Finset (Fin (F.source.dimension c))) (pred : List Bool → Prop)
    (hpred : ∀ c (r t : Fin (F.source.dimension c)) d, pred (PolynomialAffineEntryBits.packet c r.val t.val d) ↔ r ∈ s c) : Access (F.principal s) where
  original := a.original.principal s pred hpred
  inner := a.inner
  outer := a.outer
  bound := a.bound
  inner_eq := a.inner_eq
  outer_eq := a.outer_eq
  bound_eq := a.bound_eq

theorem Family.matrix_eq_affine (F : Family) (c : List Bool) :
    F.matrix c = AffineCharacteristic.affineMatrix (F.source.matrix c) := by
  funext r t
  by_cases hrt : r = t <;>
    simp [Family.matrix, AffineCharacteristic.affineMatrix, PolynomialAffineDeformation.affine, Matrix.one_apply, hrt]
  ring

theorem Family.principal_matrix (F : Family) (s : (c : List Bool) → Finset (Fin (F.source.dimension c))) (c : List Bool) :
    (F.principal s).matrix c = PrincipalPadding.matrix (F.matrix c) (s c) := by
  rw [Family.matrix_eq_affine, Family.matrix_eq_affine]
  change AffineCharacteristic.affineMatrix (PrincipalPadding.matrix (F.source.matrix c) (s c)) =
    PrincipalPadding.matrix (AffineCharacteristic.affineMatrix (F.source.matrix c)) (s c)
  exact (PrincipalPadding.matrix_affine _ _).symm

theorem Access.principalEvaluator {F : Family} (a : Access F)
    (s : (c : List Bool) → Finset (Fin (F.source.dimension c))) (pred : List Bool → Prop)
    (hpred : ∀ c (r t : Fin (F.source.dimension c)) d, pred (PolynomialAffineEntryBits.packet c r.val t.val d) ↔ r ∈ s c)
    (hp : FPPred pred) (hN : a.original.dimension ∈ FP) (hm : a.original.modulus ∈ FP)
    (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP) (E : SpaceFunction a.original.entry) :
    SpaceFunction (F.principal s).value :=
  (a.principal s pred hpred).evaluator hN hm hb hi ho (a.original.principalEntryEvaluator s pred hpred hp hm E)

end BerkowitzAffinePolynomial
end LeanCanny.Algebra
