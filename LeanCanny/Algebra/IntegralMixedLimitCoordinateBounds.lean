/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRoot
public import LeanCanny.Algebra.IntegralMixedCoordinateBounds

/-! # Original-source entry heights for actual limit-coordinate factors

The old swept coefficient matrix is multiplied by bankQ^(d-k). Its additional
logarithmic height is at most d*m*G from the actual bank denominator bounds.
The final ceiling is one original-spatial factor times the current bank height;
no later norm degree or coefficient evaluator is an input.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateBounds
open LeanCanny.Encoding FixedWidthPolynomial IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCutSource Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem entry_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound P r))
    (G H : ℕ) (hG : x.bank.Bounds G)
    (hH : ∀ k e u v, (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (((coordinate x hm r j).coeff k).coeff e) u v).natAbs ≤ 2^H)
    (k : ℕ) (u v : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((IntegralMixedLimitCoordinate.factor x hm r j c).coeff k) u v).natAbs ≤
        2^(H+IntegralMixedLimitCoordinate.degree P r*m*G) := by
  rw [IntegralMixedLimitCoordinate.factor_coefficient]
  split_ifs with HK
  · rw [← Int.cast_pow,mul_comm _ ((commonDenominator x ^ (IntegralMixedLimitCoordinate.degree P r-k):ℤ):x.sampler.scalarPrefix.carrier),
      IntegralActionHeightBounds.int_multiply_entry,Int.natAbs_mul,Int.natAbs_pow]
    have HQ := commonDenominator_height x G hG
    calc
      _ ≤ (2^(m*G))^(IntegralMixedLimitCoordinate.degree P r-k)*2^H := by
        gcongr
        exact hH k (c.val-k) u v
      _ = 2^(H+(IntegralMixedLimitCoordinate.degree P r-k)*m*G) := by
        rw [← pow_mul,← pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
        (Nat.mul_le_mul_right G (Nat.mul_le_mul_right m (Nat.sub_le _ _))) H)
  · simp only [map_zero,Matrix.zero_apply,Int.natAbs_zero,Nat.zero_le]

def factor (n M W D S L : ℕ) : ℕ :=
  IntegralCriticalFactorCeiling.factor (n+1) M W D * IntegralMixedCoordinateBounds.inputFactor n S L+
    PurePowerReductionBounds.dimension (n+1) D*S

def height (n M W D S L G : ℕ) : ℕ :=
  IntegralMixedCoordinateBounds.height n M W D S L G+PurePowerReductionBounds.dimension (n+1) D*S*G

theorem height_eq_factor (n M W D S L G : ℕ) : height n M W D S L G=factor n M W D S L*G := by
  unfold height factor IntegralMixedCoordinateBounds.height
  ring

theorem height_binary {n M W D S L G : List Bool → ℕ}
    (hn : UnaryFn n) (hM : BinaryFn M) (hW : UnaryFn W) (hD : BinaryFn D)
    (hS : BinaryFn S) (hL : BinaryFn L) (hG : BinaryFn G) :
    BinaryFn (fun q => height (n q) (M q) (W q) (D q) (S q) (L q) (G q)) :=
  (IntegralMixedCoordinateBounds.height_binary hn hM hW hD hS hL hG).add
    (((PurePowerReductionBounds.dimension_binary (hn.add (UnaryFn.const 1)) hD).mul hS).mul hG)

theorem factor_binary {n M W D S L : List Bool → ℕ}
    (hn : UnaryFn n) (hM : BinaryFn M) (hW : UnaryFn W) (hD : BinaryFn D)
    (hS : BinaryFn S) (hL : BinaryFn L) :
    BinaryFn (fun q => factor (n q) (M q) (W q) (D q) (S q) (L q)) := by
  have H := height_binary hn hM hW hD hS hL (BinaryFn.const 1)
  exact H.of_eq (fun q => by rw [height_eq_factor,Nat.mul_one])

noncomputable def oldHeight (F : Family) (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool) : ℕ :=
  IntegralMixedCoordinateBounds.height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
    (F.cap q) (H.nodes q) (H.bankHeight q)

theorem original_coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool) (k e : ℕ)
    (u v : Fin (count (F.birth q) (F.width q))) :
    (Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
      (((coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).coeff k).coeff e) u v).natAbs ≤
        2^oldHeight F H q := by
  by_cases HK : k<IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q)
  · let index : Fin (IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial q) (F.rule q)) := ⟨k,HK⟩
    have HB := IntegralMixedCoordinateBounds.coefficient_height F I H.bankHeight H.sourceHeight H.bank H.coefficient q
      (H.rank q) (H.sourceWidth q) (H.spatialDegree q) (H.nodes q)
      (H.rank_bound q) (H.width_bound q) (H.degree_bound q) (H.leading q)
      (H.expression_nodes q) (H.expression_coefficients q) (H.scales q) (H.slope q)
      (H.source_le_bank q) index e u v
    exact HB
  · have HD : (coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).natDegree<k :=
      (coordinate_degree _ _ _ _).trans_lt (by
        change ¬k < IntegralMixedLimitCoordinate.degree (F.spatial q) (F.rule q)+1 at HK
        change IntegralMixedLimitCoordinate.degree (F.spatial q) (F.rule q)<k
        omega)
    rw [coeff_eq_zero_of_natDegree_lt HD,coeff_zero,map_zero,Matrix.zero_apply,Int.natAbs_zero]
    exact Nat.zero_le _

theorem coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (H : IntegralMixedCoordinateBounds.OriginalBounds F) (q : List Bool)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (F.spatial q) (F.rule q)))
    (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (Algebra.leftMulMatrix (F.state q).sampler.scalarPrefix.basis.finBasis
      ((IntegralMixedLimitCoordinate.factor (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q) c).coeff k) u v).natAbs ≤
        2^height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
          (F.cap q) (H.nodes q) (H.bankHeight q) := by
  have HB := entry_height (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q) c
    (H.bankHeight q) (oldHeight F H q) (H.bank q) (original_coefficient_height F I H q) k u v
  have HD : IntegralMixedLimitCoordinate.degree (F.spatial q) (F.rule q) ≤
      PurePowerReductionBounds.dimension (F.ambient q+1) (H.spatialDegree q) :=
    IntegralCriticalFactorCeiling.dimension_mono (Nat.add_le_add_right (Nat.sub_le _ _) 1) (H.degree_bound q)
  apply HB.trans (Nat.pow_le_pow_right (by decide) ?_)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (H.bankHeight q) (Nat.mul_le_mul HD (F.birth_bound q))) _

theorem family_height_binary (F : Family) (H : IntegralMixedCoordinateBounds.OriginalBounds F)
    (hn : UnaryFn F.ambient) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap)
    (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (fun q => height (F.ambient q) (H.rank q) (H.sourceWidth q) (H.spatialDegree q)
      (F.cap q) (H.nodes q) (H.bankHeight q)) :=
  height_binary hn hM hW hD hS hL hG

end LeanCanny.Algebra.IntegralMixedLimitCoordinateBounds
