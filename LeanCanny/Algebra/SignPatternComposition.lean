/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternCountSpace
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native reindexing and concatenation of sign-pattern constraints

Concatenation retains the left root polynomial and appends the right family's
sign constraints. Binary index shifting preserves the queried degree and
modulus. Only the left root reader and the two constraint readers are needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.SignPatternBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.sub

def Family.comp (F : Family) (f : List Bool → List Bool) : Family where
  root := F.root ∘ f
  polynomial c := F.polynomial (f c)
  pattern c := F.pattern (f c)
  count := F.count ∘ f
  rootDegree := F.rootDegree ∘ f
  degree := F.degree ∘ f
  rootMass := F.rootMass ∘ f
  mass := F.mass ∘ f
  rootDegree_pos c := F.rootDegree_pos (f c)
  root_degree c := F.root_degree (f c)
  root_mass c := F.root_mass (f c)
  polynomial_degree c := F.polynomial_degree (f c)
  polynomial_mass c := F.polynomial_mass (f c)

theorem comp_controls {F : Family} (hF : ControlsPolyTime F) {f : List Bool → List Bool} (hf : f ∈ FP) :
    ControlsPolyTime (F.comp f) := by
  constructor
  · change (F.count ∘ f) ∈ FP
    exact mem_FP_comp hf hF.count
  · exact hF.countUnary.comp hf
  · change (F.rootDegree ∘ f) ∈ FP
    exact mem_FP_comp hf hF.rootDegree
  · change (F.degree ∘ f) ∈ FP
    exact mem_FP_comp hf hF.degree
  · change (F.rootMass ∘ f) ∈ FP
    exact mem_FP_comp hf hF.rootMass
  · change (F.mass ∘ f) ∈ FP
    exact mem_FP_comp hf hF.mass

def compQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (original q)) (queryIndex q)) (pairSnd q)
def compPattern (f : List Bool → List Bool) (q : List Bool) : List Bool := pair (f (pairFst q)) (pairSnd q)

theorem compQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : compQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp original_mem_FP hf)
    queryIndex_mem_FP) pairSnd_mem_FP
theorem compPattern_FP {f : List Bool → List Bool} (hf : f ∈ FP) : compPattern f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

def Access.comp {F : Family} (A : Access F) (f : List Bool → List Bool) : Access (F.comp f) where
  rootCoefficient := A.rootCoefficient ∘ compQuery f
  polynomialCoefficient := A.polynomialCoefficient ∘ compQuery f
  pattern := A.pattern ∘ compPattern f
  root_eq c k m hm := by
    simpa only [Function.comp_apply, compQuery, original, queryIndex, pairFst_pair, pairSnd_pair, Family.comp] using
      A.root_eq (f c) k m hm
  polynomial_eq c i hi k m hm := by
    simpa only [Function.comp_apply, compQuery, original, queryIndex, pairFst_pair, pairSnd_pair, Family.comp] using
      A.polynomial_eq (f c) i hi k m hm
  pattern_eq c i := by
    simpa only [Function.comp_apply, compPattern, pairFst_pair, pairSnd_pair, Family.comp] using A.pattern_eq (f c) i

def Family.append (F G : Family) : Family where
  root := F.root
  polynomial c i := if i < Nat.fromBitsLE (F.count c) then F.polynomial c i
    else G.polynomial c (i - Nat.fromBitsLE (F.count c))
  pattern c i := if i < Nat.fromBitsLE (F.count c) then F.pattern c i
    else G.pattern c (i - Nat.fromBitsLE (F.count c))
  count c := BinaryNatCode.encode (Nat.fromBitsLE (F.count c) + Nat.fromBitsLE (G.count c))
  rootDegree := F.rootDegree
  degree c := BinaryNatCode.encode (Nat.fromBitsLE (F.degree c) + Nat.fromBitsLE (G.degree c))
  rootMass := F.rootMass
  mass c := BinaryNatCode.encode (Nat.fromBitsLE (F.mass c) + Nat.fromBitsLE (G.mass c))
  rootDegree_pos := F.rootDegree_pos
  root_degree := F.root_degree
  root_mass := F.root_mass
  polynomial_degree c i hi := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi ⊢
    split_ifs with h
    · exact (F.polynomial_degree c i h).trans (Nat.le_add_right _ _)
    · exact (G.polynomial_degree c _ (by omega)).trans (Nat.le_add_left _ _)
  polynomial_mass c i hi := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi ⊢
    split_ifs with h
    · exact (F.polynomial_mass c i h).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · exact (G.polynomial_mass c _ (by omega)).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

theorem append_controls {F G : Family} (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) :
    ControlsPolyTime (F.append G) := by
  refine ⟨((BinaryFn.fromBits hF.count).add (BinaryFn.fromBits hG.count)).bits_mem_FP, ?_,
    hF.rootDegree, ((BinaryFn.fromBits hF.degree).add (BinaryFn.fromBits hG.degree)).bits_mem_FP,
    hF.rootMass, ((BinaryFn.fromBits hF.mass).add (BinaryFn.fromBits hG.mass)).bits_mem_FP⟩
  simpa only [Family.append, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hF.countUnary.add hG.countUnary

theorem append_signs (F G : Family) (c : List Bool) (x : ℝ) :
    (∀ i, i < Nat.fromBitsLE ((F.append G).count c) →
      SignType.sign ((((F.append G).polynomial c i).map (algebraMap ℤ ℝ)).eval x) = (F.append G).pattern c i) ↔
    (∀ i, i < Nat.fromBitsLE (F.count c) →
      SignType.sign (((F.polynomial c i).map (algebraMap ℤ ℝ)).eval x) = F.pattern c i) ∧
    (∀ i, i < Nat.fromBitsLE (G.count c) →
      SignType.sign (((G.polynomial c i).map (algebraMap ℤ ℝ)).eval x) = G.pattern c i) := by
  have hc : Nat.fromBitsLE ((F.append G).count c) = Nat.fromBitsLE (F.count c) + Nat.fromBitsLE (G.count c) :=
    Nat.fromBitsLE_bits _
  constructor
  · intro H
    constructor
    · intro i hi
      have h := H i (by rw [hc]; omega)
      simpa only [Family.append, hi, ite_true] using h
    · intro i hi
      have hj : ¬Nat.fromBitsLE (F.count c) + i < Nat.fromBitsLE (F.count c) := by omega
      have h := H (Nat.fromBitsLE (F.count c) + i) (by rw [hc]; omega)
      simpa only [Family.append, hj, ite_false, Nat.add_sub_cancel_left] using h
  · rintro ⟨L, R⟩ i hi
    rw [hc] at hi
    by_cases h : i < Nat.fromBitsLE (F.count c)
    · simpa only [Family.append, h, ite_true] using L i h
    · simpa only [Family.append, h, ite_false] using R (i - Nat.fromBitsLE (F.count c)) (by omega)

def leftConstraint (F : Family) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd q) < Nat.fromBitsLE (F.count (pairFst q))
def polynomialRow (q : List Bool) : List Bool := pair (original q) (pairFst (queryIndex q))
def shiftPattern (F : Family) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.sub (pair (pairSnd q) (F.count (pairFst q))))
def shiftCoefficient (F : Family) (q : List Bool) : List Bool :=
  pair (pair (original q) (pair (BinaryNat.sub (pair (pairFst (queryIndex q)) (F.count (original q))))
    (pairSnd (queryIndex q)))) (pairSnd q)

theorem leftConstraint_FP {F : Family} (hF : ControlsPolyTime F) : FPPred (leftConstraint F) :=
  (BinaryFn.fromBits pairSnd_mem_FP).lt (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP hF.count))
theorem polynomialRow_FP : polynomialRow ∈ FP :=
  mem_FP_pair original_mem_FP
    (mem_FP_comp queryIndex_mem_FP pairFst_mem_FP)
theorem shiftPattern_FP {F : Family} (hF : ControlsPolyTime F) : shiftPattern F ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp
    (mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hF.count)) BinaryNat.sub_mem_FP)
theorem shiftCoefficient_FP {F : Family} (hF : ControlsPolyTime F) : shiftCoefficient F ∈ FP :=
  mem_FP_pair (mem_FP_pair original_mem_FP (mem_FP_pair
    (mem_FP_comp (mem_FP_pair (mem_FP_comp queryIndex_mem_FP pairFst_mem_FP)
      (mem_FP_comp original_mem_FP hF.count)) BinaryNat.sub_mem_FP)
    (mem_FP_comp queryIndex_mem_FP pairSnd_mem_FP))) pairSnd_mem_FP

noncomputable def appendCoefficient {F G : Family} (A : Access F) (B : Access G) (q : List Bool) : List Bool :=
  if leftConstraint F (polynomialRow q) then A.polynomialCoefficient q else B.polynomialCoefficient (shiftCoefficient F q)
noncomputable def appendPattern {F G : Family} (A : Access F) (B : Access G) (q : List Bool) : List Bool :=
  if leftConstraint F q then A.pattern q else B.pattern (shiftPattern F q)

noncomputable def Access.append {F G : Family} (A : Access F) (B : Access G) : Access (F.append G) where
  rootCoefficient := A.rootCoefficient
  polynomialCoefficient := appendCoefficient A B
  pattern := appendPattern A B
  root_eq := A.root_eq
  polynomial_eq c i hi k m hm := by
    have hi' : i < Nat.fromBitsLE (F.count c) + Nat.fromBitsLE (G.count c) := by
      simpa only [Family.append, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi
    simp only [appendCoefficient, leftConstraint, polynomialRow, original, queryIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.append]
    by_cases h : i < Nat.fromBitsLE (F.count c)
    · simp only [h, ite_true]
      exact A.polynomial_eq c i h k m hm
    · simp only [h, ite_false]
      simpa only [shiftCoefficient, original, queryIndex, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits] using B.polynomial_eq c (i - Nat.fromBitsLE (F.count c)) (by omega) k m hm
  pattern_eq c i := by
    simp only [appendPattern, leftConstraint, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.append]
    by_cases h : i < Nat.fromBitsLE (F.count c)
    · simp only [h, ite_true]
      exact A.pattern_eq c i
    · simp only [h, ite_false]
      simpa only [shiftPattern, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
        B.pattern_eq c (i - Nat.fromBitsLE (F.count c))

theorem appendCoefficient_evaluator {F G : Family} {A : Access F} {B : Access G}
    (hF : ControlsPolyTime F) (P : SpaceFunction A.polynomialCoefficient) (Q : SpaceFunction B.polynomialCoefficient) :
    SpaceFunction (appendCoefficient A B) := by
  have E := SpaceFunction.branch (fun q => decide (leftConstraint F (polynomialRow q)))
    ((leftConstraint_FP hF).comp polynomialRow_FP).flag_mem_FP P (Q.precompose _ (shiftCoefficient_FP hF))
  exact E.congr (funext fun q => by simp only [appendCoefficient, decide_eq_true_eq, Function.comp_apply])

theorem appendPattern_FP {F G : Family} {A : Access F} {B : Access G}
    (hF : ControlsPolyTime F) (hA : A.pattern ∈ FP) (hB : B.pattern ∈ FP) : appendPattern A B ∈ FP :=
  (leftConstraint_FP hF).ite_mem_FP hA (mem_FP_comp (shiftPattern_FP hF) hB)

theorem appendCountEvaluator {F G : Family} (A : Access F) (B : Access G)
    (hF : ControlsPolyTime F) (hG : ControlsPolyTime G) (hA : A.pattern ∈ FP) (hB : B.pattern ∈ FP)
    (H : SpaceFunction A.rootCoefficient) (P : SpaceFunction A.polynomialCoefficient) (Q : SpaceFunction B.polynomialCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (rootCount (F.append G) c)) :=
  rootCountEvaluator (A.append B) (append_controls hF hG) (appendPattern_FP hF hA hB)
    H (appendCoefficient_evaluator hF P Q)

end LeanCanny.Algebra.SignPatternBits
