/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts
/-! # Original metadata packets for physical critical-coordinate correlation

The caller retains one full saved key and a chronological creating birth.
Only original header tags and coordinate fields choose the two physical
columns. Powers use the fixed original schedule; the actual retained
integer denominator is read with its caller modulus unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (prefixLength)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedPhysicalIndex (prefixArity scalarColumn)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (key : List Bool→List Bool) (b : List Bool→ℕ) (q : List Bool) :=pair (key q) (List.replicate (b q) true)
theorem packet_FP {key : List Bool→List Bool} {b : List Bool→ℕ} (hk : key∈FP) (hb : UnaryFn b) : packet key b∈FP :=
  mem_FP_pair hk hb.mem_FP

def count (P : Parameters) (T : Tables) (key : List Bool→List Bool) (q : List Bool) :=
  prefixArity P T (packet key (prefixLength P ∘ key) q)
theorem count_unary (P : Parameters) (a : Access P) (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (count P T key) :=
  (IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T hT).comp
    (packet_FP hk ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk))

def age (P : Parameters) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=prefixLength P (key q)-1-stage q
theorem age_unary (P : Parameters) (a : Access P) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (hk : key∈FP) (hj : UnaryFn stage) : UnaryFn (age P key stage) :=
  (((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk).sub (UnaryFn.const 1)).sub hj

def header (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  IntegralMixedCommandHeaderBits.lookup (T.commands (pairFst (key q))) (stage q)
theorem header_readers (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (hk : key∈FP) (hj : UnaryFn stage) :
    IntegralMixedCommandHeaderBits.Readers (header T key stage) :=
  IntegralMixedCommandHeaderBits.lookup_readers _ _ (mem_FP_comp (mem_FP_comp hk pairFst_mem_FP) hT.commands) (BinaryFn.ofUnary hj)

def Active (P : Parameters) (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  stage q<prefixLength P (key q) ∧ (header T key stage q).context=1
instance (P : Parameters) (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :
    Decidable (Active P T key stage q) := inferInstanceAs (Decidable (_∧_))
theorem active_FP (P : Parameters) (a : Access P) (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (hk : key∈FP) (hj : UnaryFn stage) :
    FPPred (Active P T key stage) :=
  ((BinaryFn.ofUnary hj).lt (BinaryFn.ofUnary ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk))).and
    ((header_readers T hT key stage hk hj).context.eq (BinaryFn.const 1))

def scalar (P : Parameters) (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  scalarColumn P T (pair (key q) (BinaryNatCode.encode (age P key stage q)))
theorem scalar_unary (P : Parameters) (a : Access P) (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (hk : key∈FP) (hj : UnaryFn stage) : UnaryFn (scalar P T key stage) :=
  (IntegralMixedFramedPhysicalIndex.scalarColumn_unary P a T hT).comp
    (mem_FP_pair hk (BinaryFn.ofUnary (age_unary P a key stage hk hj)).bits_mem_FP)

def physical (P : Parameters) (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  prefixArity P T (packet key stage q)+(header T key stage q).offset+(header T key stage q).coordinate
theorem physical_binary (P : Parameters) (a : Access P) (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (hk : key∈FP) (hj : UnaryFn stage) : BinaryFn (physical P T key stage) :=
  ((BinaryFn.ofUnary ((IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T hT).comp (packet_FP hk hj))).add
    (header_readers T hT key stage hk hj).offset).add (header_readers T hT key stage hk hj).coordinate

def scalarPower (P : Parameters) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  UniformIntegralPowerSchedule.birth (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q))) (stage q)
def physicalPower (P : Parameters) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  UniformIntegralPowerSchedule.physical (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q))) (stage q)
theorem scalarPower_binary (P : Parameters) (a : Access P) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (hk : key∈FP) (hj : UnaryFn stage) : BinaryFn (scalarPower P key stage) :=
  UniformIntegralPowerSchedule.birth_binary ((a.cap.comp (mem_FP_comp hk pairFst_mem_FP)).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hk pairFst_mem_FP))) hj
theorem physicalPower_binary (P : Parameters) (a : Access P) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (hk : key∈FP) (hj : UnaryFn stage) : BinaryFn (physicalPower P key stage) :=
  UniformIntegralPowerSchedule.physical_binary ((a.cap.comp (mem_FP_comp hk pairFst_mem_FP)).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hk pairFst_mem_FP))) hj

def denominatorPacket (P : Parameters) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (modulus : List Bool→List Bool) (q : List Bool) :=
  pair (pair (key q) (modulus q)) (pair (BinaryNatCode.encode (age P key stage q)) [])
theorem denominatorPacket_FP (P : Parameters) (a : Access P) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (modulus : List Bool→List Bool) (hk : key∈FP) (hj : UnaryFn stage) (hm : modulus∈FP) :
    denominatorPacket P key stage modulus∈FP :=
  mem_FP_pair (mem_FP_pair hk hm)
    (mem_FP_pair (BinaryFn.ofUnary (age_unary P a key stage hk hj)).bits_mem_FP (constFn_mem_FP []))
end LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
