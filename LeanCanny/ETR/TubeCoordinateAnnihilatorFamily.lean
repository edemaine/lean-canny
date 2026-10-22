/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorReaders

/-! # Uniform native coordinate-annihilator coefficient families

A binary coordinate index selects the original projection or one spatial basis
direction. The latter includes the reciprocal coordinate. Packet and mask
selection are FP, while large rational constants need only native modular
coefficient readers.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

def selectedDirection (ell : List Bool → ℕ → ℤ) (c : List Bool) (j : ℕ) : ℤ :=
  if Nat.fromBitsLE (pairSnd c) = 0 then ell (pairFst c) j
  else if j = Nat.fromBitsLE (pairSnd c) then 1 else 0

def originalDirectionQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
def coordinateCode (q : List Bool) : List Bool := pairSnd (pairFst q)

def selectedDirectionRead (read : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (coordinateCode q) = 0 then read (originalDirectionQuery q)
  else if Nat.fromBitsLE (pairSnd q) = Nat.fromBitsLE (coordinateCode q)
    then (Codec.integer 1).toBits else (Codec.integer 0).toBits

theorem originalDirectionQuery_FP : originalDirectionQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem coordinateCode_FP : coordinateCode ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem selectedDirectionRead_FP {read : List Bool → List Bool} (hr : read ∈ FP) : selectedDirectionRead read ∈ FP := by
  have hz := TubeBivariate.zero_fppred coordinateCode_FP
  have he : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = Nat.fromBitsLE (coordinateCode q)) :=
    BinaryNat.eq_fppred pairSnd_mem_FP coordinateCode_FP
  exact hz.ite_mem_FP (mem_FP_comp originalDirectionQuery_FP hr)
    (he.ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _))

theorem selectedDirectionRead_correct (read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (hr : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (c : List Bool) (i : ℕ) :
    selectedDirectionRead read (pair c (BinaryNatCode.encode i)) =
      (Codec.integer (selectedDirection ell c i)).toBits := by
  simp only [selectedDirectionRead, coordinateCode, originalDirectionQuery, pairFst_pair,
    pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, selectedDirection]
  split_ifs <;> first | exact hr _ _ | rfl

noncomputable def indexedPacket (packet : List Bool → List Bool) (c : List Bool) : List Bool := packet (pairFst c)

noncomputable def indexedData (packet mask read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    TubeBivariate.Data (pairFst ∘ indexedPacket packet) (mask ∘ pairFst)
      (fun _ => []) (fun _ => []) (fun _ => [])
      (fun c => numerator (indexedPacket packet c)) (fun c => denominator (indexedPacket packet c))
      (selectedDirection ell) where
  coordinates := readers.precomposeUniform (indexedPacket packet) (mem_FP_comp pairFst_mem_FP hp)
  bounds := bounds.precomposeUniform (indexedPacket packet) (mem_FP_comp pairFst_mem_FP hp)
  direction := selectedDirectionRead read
  sourceFP := mem_FP_comp (mem_FP_comp pairFst_mem_FP hp) pairFst_mem_FP
  activeFP := mem_FP_comp pairFst_mem_FP hm
  modulusFP := constFn_mem_FP []
  innerFP := constFn_mem_FP []
  outerFP := constFn_mem_FP []
  directionFP := selectedDirectionRead_FP hr
  direction_eq c i _ := selectedDirectionRead_correct read ell he c i

noncomputable def family (packet mask : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (a b : List Bool → ℤ) (c : List Bool) : Polynomial ℤ :=
  integerAnnihilator (packet (pairFst c)) (mask (pairFst c)) (selectedDirection ell c)
    (a (pairFst c)) (b (pairFst c))

theorem family_evaluator (packet mask read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (a b : List Bool → ℤ)
    (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (A : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (a (pairFst (pairFst c))))))
    (B : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (b (pairFst (pairFst c)))))) :
    SpaceFunction (PrimitivePairBits.coefficient (family packet mask ell a b)) := by
  have hP := mem_FP_comp pairFst_mem_FP hp
  have E := lowestSpecialization_evaluator (indexedData packet mask read ell hp hm hr he)
    (annihilatorInnerDegree ∘ indexedPacket packet) (a ∘ pairFst) (b ∘ pairFst)
    (annihilatorInnerDegree_binary.comp hP) A B
  refine E.congr (funext fun q => ?_)
  rfl

end LeanCanny.ETR.TubeCoordinateAnnihilator

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Algebra Polynomial TubeLevelPacket TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det integerAnnihilator

theorem family_coordinate (packet mask : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (a b : List Bool → ℤ) (c : List Bool)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    family packet mask ell a b (pair c (BinaryNatCode.encode i.val)) =
      integerCoordinateAnnihilator (packet c) (mask c) (ell c) (a c) (b c) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [family, pairFst_pair]
    change integerAnnihilator (packet c) (mask c)
      (selectedDirection ell (pair c (BinaryNatCode.encode 0))) (a c) (b c) =
        integerAnnihilator (packet c) (mask c) (ell c) (a c) (b c)
    congr 1
    funext k
    simp only [selectedDirection, pairSnd_pair, pairFst_pair]
    rw [show Nat.fromBitsLE (BinaryNatCode.encode 0) = 0 from rfl]
    rfl
  · simp only [family, pairFst_pair]
    change integerAnnihilator (packet c) (mask c)
      (selectedDirection ell (pair c (BinaryNatCode.encode j.succ.val))) (a c) (b c) =
        integerAnnihilator (packet c) (mask c) (coordinateDirection j.val) (a c) (b c)
    congr 1
    funext k
    simp [selectedDirection, coordinateDirection, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.ETR.TubeCoordinateAnnihilator
