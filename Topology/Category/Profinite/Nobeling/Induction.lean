/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Topology.Category.Profinite.Nobeling.Span
public import Mathlib.Topology.Category.Profinite.Nobeling.Successor
public import Mathlib.Topology.Category.Profinite.Nobeling.ZeroLimit

/-!
# Nöbeling's theorem

This file proves Nöbeling's theorem. For the overall proof outline see
`Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main result

* `LocallyConstant.freeOfProfinite`: Nöbeling's theorem.
  For `S : Profinite`, the `ℤ`-module `LocallyConstant S ℤ` is free.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open Module Topology

universe u

namespace Profinite

namespace NobelingProof

variable {I : Type u} (C : Set (I -> Bool)) [LinearOrder I] [WellFoundedLT I]

section Induction

/--
theorem `GoodProducts.P0` / 定理 `GoodProducts.P0`

English:
theorem GoodProducts.P0
  statement: P I 0
  proof: fun _ C _ hsC => by
  have : C subseteq {(fun _ => false)} := fun c hc => by
    ext x; exact Bool.eq_false_iff.mpr (fun ht => not_lt_zero (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

中文:
定理 GoodProducts.P0
  结论: P I 0
  证明: fun _ C _ hsC => by
  have : C subseteq {(fun _ => false)} := fun c hc => by
    ext x; exact Bool.eq_false_iff.mpr (fun ht => not_lt_zero (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

Depends on / 依赖: Bool.eq_false_iff.mpr, Set.subset_singleton_iff_eq, eq_false_iff, linearIndependentEmpty, linearIndependentSingleton, not_lt_zero, subset_singleton_iff_eq, subseteq
-/
theorem GoodProducts.P0 : P I 0 := fun _ C _ hsC => by
  have : C subseteq {(fun _ => false)} := fun c hc => by
    ext x; exact Bool.eq_false_iff.mpr (fun ht => not_lt_zero (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

/--
theorem `GoodProducts.Plimit` / 定理 `GoodProducts.Plimit`

English:
theorem GoodProducts.Plimit
  given: (o : Ordinal) (ho : Order.IsSuccLimit o)
  proof: by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]; rw [linearIndependent_subtype_iff]
  exact linearIndepOn_iUnion_of_directed
    (Monotone.directed_le fun _ _ h => GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ =>
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (ho'.le.trans hho)
    (π C (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))

中文:
定理 GoodProducts.Plimit
  条件: (o : 序数) (ho : Order.是SuccLimit o)
  证明: by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]; rw [linearIndependent_subtype_iff]
  exact linearIndepOn_iUnion_of_directed
    (Monotone.directed_le fun _ _ h => GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ =>
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (ho'.le.trans hho)
    (π C (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))

Depends on / 依赖: GoodProducts, GoodProducts.smaller_mono, Monotone, Monotone.directed_le, contained_proj, directed_le, isClosed_proj, le.trans, linearIndepOn_iUnion_of_directed, linearIndependent_iff_smaller, linearIndependent_iff_union_smaller, linearIndependent_subtype_iff, smaller_mono
-/
theorem GoodProducts.Plimit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    (forall (o' : Ordinal), o' < o -> P I o') -> P I o := by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]; rw [linearIndependent_subtype_iff]
  exact linearIndepOn_iUnion_of_directed
    (Monotone.directed_le fun _ _ h => GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ =>
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (ho'.le.trans hho)
    (π C (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))

/--
theorem `GoodProducts.linearIndependentAux` / 定理 `GoodProducts.linearIndependentAux`

English:
theorem GoodProducts.linearIndependentAux
  given: (μ : Ordinal)
  statement: P I μ
  proof: by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC => ?_)
      (fun o ho h => (GoodProducts.Plimit o ho (fun o' ho' => (h o' ho'))))
  have ho' : o < Ordinal.type (· < · : I -> I -> Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC ho') ?_ ?_ (succ_mono C o)
    (square_commutes C ho')
  · exact h (le_of_lt ho') (π C (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (π C (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))

中文:
定理 GoodProducts.linearIndependentAux
  条件: (μ : 序数)
  结论: P I μ
  证明: by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC => ?_)
      (fun o ho h => (GoodProducts.Plimit o ho (fun o' ho' => (h o' ho'))))
  have ho' : o < Ordinal.type (· < · : I -> I -> Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC ho') ?_ ?_ (succ_mono C o)
    (square_commutes C ho')
  · exact h (le_of_lt ho') (π C (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (π C (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))

Depends on / 依赖: GoodProducts, GoodProducts.Plimit, ModuleCat, ModuleCat.linearIndependent_leftExact, Order.lt_succ, Ordinal, Ordinal.limitRecOn, Ordinal.type, Plimit, contained_proj, isClosed_proj, le_of_lt, limitRecOn, linearIndependent_com, linearIndependent_iff_sum, linearIndependent_leftExact, lt_of_lt_of_le, lt_succ, square_commutes, succ_exact
-/
theorem GoodProducts.linearIndependentAux (μ : Ordinal) : P I μ := by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC => ?_)
      (fun o ho h => (GoodProducts.Plimit o ho (fun o' ho' => (h o' ho'))))
  have ho' : o < Ordinal.type (· < · : I -> I -> Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC ho') ?_ ?_ (succ_mono C o)
    (square_commutes C ho')
  · exact h (le_of_lt ho') (π C (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (π C (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))

/--
theorem `GoodProducts.linearIndependent` / 定理 `GoodProducts.linearIndependent`

English:
theorem GoodProducts.linearIndependent
  given: (hC : IsClosed C)
  proof: GoodProducts.linearIndependentAux (Ordinal.type (· < · : I -> I -> Prop)) (le_refl _)
    C hC (fun _ _ _ _ => Ordinal.typein_lt_type _ _)

中文:
定理 GoodProducts.linearIndependent
  条件: (hC : 是闭集 C)
  证明: GoodProducts.linearIndependentAux (Ordinal.type (· < · : I -> I -> Prop)) (le_refl _)
    C hC (fun _ _ _ _ => Ordinal.typein_lt_type _ _)

Depends on / 依赖: GoodProducts, GoodProducts.linearIndependentAux, Ordinal, Ordinal.type, Ordinal.typein_lt_type, le_refl, linearIndependentAux, typein_lt_type
-/
theorem GoodProducts.linearIndependent (hC : IsClosed C) :
    LinearIndependent Int (GoodProducts.eval C) :=
  GoodProducts.linearIndependentAux (Ordinal.type (· < · : I -> I -> Prop)) (le_refl _)
    C hC (fun _ _ _ _ => Ordinal.typein_lt_type _ _)

/-- `GoodProducts C` as a `ℤ`-basis for `LocallyConstant C ℤ`. -/
noncomputable
/--
Definition of `GoodProducts.Basis` / `GoodProducts.Basis` 的定义

English:
definition GoodProducts.Basis
  signature: (hC : IsClosed C)
  body: Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

中文:
定义 GoodProducts.基
  签名: (hC : 是闭集 C)
  定义体: Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

Depends on / 依赖: Basis.mk, GoodProducts, GoodProducts.linearIndependent, GoodProducts.span, linearIndependent
-/
def GoodProducts.Basis (hC : IsClosed C) :
    Basis (GoodProducts C) Int (LocallyConstant C Int) :=
  Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S -> I -> Bool} (hι : IsClosedEmbedding ι)
include hι

/--
theorem `Nobeling_aux` / 定理 `Nobeling_aux`

English:
theorem Nobeling_aux
  statement: Module.Free Int (LocallyConstant S Int)
  proof: Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ Int
    hι.isEmbedding.toHomeomorph).symm

中文:
定理 Nobeling_aux
  结论: 模.自由 整数 (局部常数 S 整数)
  证明: Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ Int
    hι.isEmbedding.toHomeomorph).symm

Depends on / 依赖: Module, Module.Free.of_equiv, of_equiv
-/
theorem Nobeling_aux : Module.Free Int (LocallyConstant S Int) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ Int
    hι.isEmbedding.toHomeomorph).symm

end NobelingProof

variable (S : Profinite.{u})

open scoped Classical in
/-- The embedding `S → (I → Bool)` where `I` is the set of clopens of `S`. -/
noncomputable
/--
Definition of `Nobeling.ι` / `Nobeling.ι` 的定义

English:
definition Nobeling.ι
  signature: : S -> ({C : Set S // IsClopen C} -> Bool)
  body: fun s C => decide (s in C.1)

中文:
定义 Nobeling.ι
  签名: : S -> ({C : 集合 S // IsClopen C} -> 布尔值)
  定义体: fun s C => decide (s in C.1)
-/
def Nobeling.ι : S -> ({C : Set S // IsClopen C} -> Bool) := fun s C => decide (s in C.1)

/--
theorem `Nobeling.isClosedEmbedding` / 定理 `Nobeling.isClosedEmbedding`

English:
theorem Nobeling.isClosedEmbedding
  statement: IsClosedEmbedding (Nobeling.ι S)
  proof: by
  classical
  apply Continuous.isClosedEmbedding
  · dsimp +unfoldPartialApp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert! C.2
      ext x
      simp
    · refine IsClopen.isOpen ?_
      convert! C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp +unfoldPartialApp [ι] at h
    rw [← congr_fun h ⟨C]; rw [hC⟩]
    exact decide_eq_true hh.1

中文:
定理 Nobeling.isClosedEmbedding
  结论: 是闭嵌入 (Nobeling.ι S)
  证明: by
  classical
  apply Continuous.isClosedEmbedding
  · dsimp +unfoldPartialApp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert! C.2
      ext x
      simp
    · refine IsClopen.isOpen ?_
      convert! C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp +unfoldPartialApp [ι] at h
    rw [← congr_fun h ⟨C]; rw [hC⟩]
    exact decide_eq_true hh.1

Depends on / 依赖: Continuous, Continuous.isClosedEmbedding, IsClopen, IsClopen.isOpen, IsLocallyConstant, IsLocallyConstant.iff_continuous, IsLocallyConstant.tfae, Set.mem_preimage, Set.mem_singleton_iff, classical, continuous_pi, convert, decide_eq_true_eq, exists_isClopen_of_totally_separated, iff_continuous, isClopen_compl_iff, isClopen_compl_iff.mp, isClosedEmbedding, isOpen, mem_preimage
-/
theorem Nobeling.isClosedEmbedding : IsClosedEmbedding (Nobeling.ι S) := by
  classical
  apply Continuous.isClosedEmbedding
  · dsimp +unfoldPartialApp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert! C.2
      ext x
      simp
    · refine IsClopen.isOpen ?_
      convert! C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp +unfoldPartialApp [ι] at h
    rw [← congr_fun h ⟨C]; rw [hC⟩]
    exact decide_eq_true hh.1

end Profinite

open Profinite NobelingProof

/--
Instance `LocallyConstant.freeOfProfinite` / 实例 `LocallyConstant.freeOfProfinite`

English:
instance LocallyConstant.freeOfProfinite
  signature: (S : Profinite.{u})
  body: by
  obtain ⟨_, _⟩ := exists_wellFoundedLT {C : Set S // IsClopen C}
  exact @Nobeling_aux {C : Set S // IsClopen C} _ _ S (Nobeling.ι S) (Nobeling.isClosedEmbedding S)

中文:
实例 局部常数.freeOfProfinite
  签名: (S : Profinite.{u})
  定义体: by
  obtain ⟨_, _⟩ := exists_wellFoundedLT {C : Set S // IsClopen C}
  exact @Nobeling_aux {C : Set S // IsClopen C} _ _ S (Nobeling.ι S) (Nobeling.isClosedEmbedding S)

Depends on / 依赖: IsClopen, Nobeling, Nobeling.isClosedEmbedding, Nobeling_aux, exists_wellFoundedLT, isClosedEmbedding
-/
instance LocallyConstant.freeOfProfinite (S : Profinite.{u}) :
    Module.Free Int (LocallyConstant S Int) := by
  obtain ⟨_, _⟩ := exists_wellFoundedLT {C : Set S // IsClopen C}
  exact @Nobeling_aux {C : Set S // IsClopen C} _ _ S (Nobeling.ι S) (Nobeling.isClosedEmbedding S)
