/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSpace
public import LeanCanny.Encoding.SquareSampleAccess
/-! # Total native full-row query reader with exact external exponent words

The scalar and critical branches both derive their costs from original
controls. The extra original root field budgets the caller modulus; it never
changes the literal source script. Semantic identification with a full input
is proved separately from these native query and dispatch constructions.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value IntegralMixedFramedPhysicalFreshRowBits.value

def saved (key : List Bool→List Bool) :=key∘SquareSampleInput.source
noncomputable abbrev count (P : Parameters) (D : Plan P) (key : List Bool→List Bool) :=
  IntegralMixedFramedFullScalarRowBits.fullCount P D (saved key)
noncomputable def row (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :=
  min (Nat.fromBitsLE (SquareSampleInput.indexWord q)) (count P D key q-1)
def width (q : List Bool) :=(SquareSampleInput.widthWord q).length

def liftedKey (key : List Bool→List Bool) (q : List Bool) :=
  pair (pair (pairFst (saved key q)) (SquareSampleInput.modulusWord q))
    (pair (pairFst (pairSnd (saved key q))) (pair (pairSnd (pairSnd (saved key q))) q))
noncomputable def datum (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :=
  pair (pair (liftedKey key q) (BinaryNatCode.encode (row P D key q))) (SquareSampleInput.modulusWord q)

def origin (q : List Bool) :=pairSnd (pairSnd (pairSnd (pairFst (pairFst q))))
theorem origin_FP : origin∈FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

theorem origin_datum (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    origin (datum P D key q)=q :=by
  simp only [origin,datum,liftedKey,pairFst_pair,pairSnd_pair]

theorem saved_FP (key : List Bool→List Bool) (hk : key∈FP) : saved key∈FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hk

theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (count P D key) :=
  IntegralMixedFramedFullScalarRowBits.fullCount_unary P a D J T ht hT (saved key) (saved_FP key hk)

theorem row_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (row P D key) :=
  UnaryFn.fromBitsLE_min (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
    ((count_unary P a D J T ht hT key hk).sub (UnaryFn.const 1))

theorem width_unary : UnaryFn width :=UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem datum_FP (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool→List Bool) (hk : key∈FP) : datum P D key∈FP := by
  have HK:=saved_FP key hk
  have HM : SquareSampleInput.modulusWord∈FP:=SquareSampleInput.modulusWord_FP
  have HC : (fun q=>pair (pairFst (pairSnd (saved key q))) (pair (pairSnd (pairSnd (saved key q))) q))∈FP :=
    mem_FP_pair (mem_FP_comp (mem_FP_comp HK pairSnd_mem_FP) pairFst_mem_FP)
      (mem_FP_pair (mem_FP_comp (mem_FP_comp HK pairSnd_mem_FP) pairSnd_mem_FP) id_mem_FP)
  have HL : liftedKey key∈FP:=mem_FP_pair (mem_FP_pair (mem_FP_comp HK pairFst_mem_FP) HM) HC
  exact mem_FP_of_eq (mem_FP_pair (mem_FP_pair HL (BinaryFn.ofUnary (row_unary P a D J T ht hT key hk)).bits_mem_FP) HM)
    (fun _=>by unfold datum;rfl)

noncomputable def value (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (key : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q) (q : List Bool) :=
  if IntegralMixedFramedPhysicalRowSelector.IsScalar P T
      (pair (saved key q) (BinaryNatCode.encode (row P D key q))) then
    FixedWidthRowBits.value (count P D key) width
      (IntegralMixedFramedPhysicalScalarRowBits.polynomial P D J T hT (saved key) (row P D key) hpos)
      SquareSampleInput.rankWord SquareSampleInput.modulusWord q
  else IntegralMixedFramedPhysicalFreshRowBits.value (lifted P) (liftedPlan P D) Jnew
    c.critical.tables c.critical.represents (width∘origin) (SquareSampleInput.rankWord∘origin) (datum P D key q)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Jnew c)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q) :
    SpaceFunction (value P D J T hT Jnew c key hpos) := by
  have HK:=saved_FP key hk
  have HR:=row_unary P a D J T ht hT key hk
  have HM : SquareSampleInput.modulusWord∈FP:=SquareSampleInput.modulusWord_FP
  have HG:=((IntegralMixedFramedPhysicalRowSelector.isScalar_fppred P a T ht).comp
    (mem_FP_pair HK (BinaryFn.ofUnary HR).bits_mem_FP)).flag_mem_FP
  have HE:=IntegralMixedFramedPhysicalScalarRowBits.evaluator P a D J T ht hT (saved key) HK (row P D key)
    (BinaryFn.ofUnary HR) hpos width width_unary SquareSampleInput.rankWord SquareSampleInput.modulusWord
    (SquareSampleInput.rankWord_FP) HM Jnew c hc
  have HP:=IntegralMixedFramedPhysicalFreshRowBits.evaluator (lifted P)
    (IntegralMixedFramedCompanionUniformBits.lifted_access P a) (liftedPlan P D) Jnew c hc (width∘origin)
    (width_unary.comp origin_FP) (SquareSampleInput.rankWord∘origin)
    (mem_FP_comp origin_FP (SquareSampleInput.rankWord_FP))
  have HF:=HP.precompose (datum P D key) (datum_FP P a D J T ht hT key hk)
  have E:=SpaceFunction.branch _ HG HE HF
  exact E.congr (funext fun _=>by unfold value;simp only [decide_eq_true_eq,Function.comp_apply])

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
