/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
public import LeanCanny.Algebra.IntegerPolynomialZeroRootSource
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSource
public import LeanCanny.Algebra.IntegralMixedIntegerFamilyOriginalSource
/-! # Framed integer preludes from native original polynomial sources

Integer coefficients remain in a charged source. Only the count and uniform
original degree ceiling determine the task horizon and scalar width.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def ceiling (ambient degree bound : List Bool → ℕ) (root : List Bool) :=
  IntegralMixedExceptionalBounds.auxiliaryCap (ambient root+1) (degree root)+bound root

def parameters (ambient degree bound count : List Bool → ℕ) : Parameters where
  cap root := count root+2
  width root := (ceiling ambient degree bound root).size
  ambient := ambient
  sourceWidth root := (degree root).size
  degree := degree
  height _ := 0
  modulusBound _ := 2

theorem ceiling_binary {ambient degree bound : List Bool → ℕ}
    (hn : UnaryFn ambient) (hd : BinaryFn degree) (hb : BinaryFn bound) : BinaryFn (ceiling ambient degree bound) :=
  (IntegralMixedExceptionalBounds.auxiliaryCap_binary (hn.add (UnaryFn.const 1)) hd).add hb

theorem access {ambient degree bound count : List Bool → ℕ}
    (hn : UnaryFn ambient) (hd : BinaryFn degree) (hb : BinaryFn bound) (hc : UnaryFn count) :
    Access (parameters ambient degree bound count) where
  cap := hc.add (UnaryFn.const 2)
  width := (UnaryFn.length (ceiling_binary hn hd hb).bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  ambient := hn
  sourceWidth := (UnaryFn.length hd.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  degree := hd
  height := BinaryFn.const 0
  modulusBound := BinaryFn.const 2

theorem source_cap (ambient degree bound count : List Bool → ℕ) (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (ambient root+1) (degree root)≤
      2^(parameters ambient degree bound count).width root :=
  (Nat.le_add_right _ _).trans (Nat.lt_size_self _).le

theorem bound_cap (ambient degree bound count : List Bool → ℕ) (root : List Bool) :
    bound root≤2^(parameters ambient degree bound count).width root :=
  (Nat.le_add_left _ _).trans (Nat.lt_size_self _).le

noncomputable def instruction (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) (i : Fin (count root)) : Instruction (P.ambient root) (P.width root) where
  source := Q root
  source_cap := hq root
  command := .integer (S.polynomial (pair root (BinaryNatCode.encode (count root-1-i.val))))
    (hz _) ((S.degree_bound _).trans (hd root _))

noncomputable def commands (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) := List.ofFn (instruction P Q hq S count hz hd root)

theorem commands_length (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) : (commands P Q hq S count hz hd root).length=count root := List.length_ofFn

noncomputable def plan (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hdegree : ∀root,(Q root).degree=P.degree root)
    (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (hroom : ∀root,count root+2≤P.cap root+1) : Plan P where
  initialSource := Q
  initial_degree := hdegree
  scalar_cap := hcap
  rules := commands P Q (fun root=>by
    rw [hdegree]
    exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
      PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root)≤
        IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (hcap root)) S count hz hd
  room root := by rw [commands_length]; exact hroom root

def query (P : Parameters) (key : List Bool) :=
  pair (pairFst key) (BinaryNatCode.encode (IntegralMixedFramedHistoryFamilyBits.prefixLength P key))
theorem query_FP (P : Parameters) (a : Access P) : query P∈FP :=
  mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).bits_mem_FP

noncomputable def source (P : Parameters) (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ) :=
  IntegerPolynomialSourceChoice.choose
    (fun key=>IntegralMixedFramedHistoryFamilyBits.prefixLength P key<count (pairFst key))
    (IntegerPolynomialSourceChoice.reindex S (query P)) IntegerPolynomialZeroRootSource.source

theorem native_access (P : Parameters) (a : Access P) (S : IntegerPolynomialRootQueriesBits.Source)
    (hS : IntegerPolynomialRootQueriesBits.Access S) {count : List Bool → ℕ} (hc : UnaryFn count) :
    IntegerPolynomialRootQueriesBits.Access (source P S count) :=
  IntegerPolynomialSourceChoice.choose_access
    ((BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).lt ((BinaryFn.ofUnary hc).comp pairFst_mem_FP))
    _ _ (IntegerPolynomialSourceChoice.reindex_access S hS (query_FP P a)) IntegerPolynomialZeroRootSource.access

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
