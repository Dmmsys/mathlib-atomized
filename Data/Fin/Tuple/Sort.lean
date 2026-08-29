/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fintype.Fin

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : Fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ Tuple.sort f`.

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`

-/

@[expose] public section


namespace Tuple

variable {n : Nat}
variable {α : Type*} [LinearOrder α]

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (f : Fin n -> α)
  body: Finset.univ.image fun i => (f i, i)

中文:
定义 graph
  签名: (f : 有限集 n -> α)
  定义体: Finset.univ.image fun i => (f i, i)

Depends on / 依赖: Finset, Finset.univ.image
-/
def graph (f : Fin n -> α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

/--
Definition of `graph.proj` / `graph.proj` 的定义

English:
definition graph.proj
  signature: {f : Fin n -> α}
  body: fun p => p.1.1

中文:
定义 graph.proj
  签名: {f : 有限集 n -> α}
  定义体: fun p => p.1.1
-/
def graph.proj {f : Fin n -> α} : graph f -> α := fun p => p.1.1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `graph.card` / 定理 `graph.card`

English:
theorem graph.card
  given: (f : Fin n -> α)
  statement: (graph f).card = n
  proof: by
  rw [graph]; rw [Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: proof was `simp`
    rw [Prod.ext_iff]
    simp

中文:
定理 graph.card
  条件: (f : 有限集 n -> α)
  结论: (graph f).card = n
  证明: by
  rw [graph]; rw [Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: proof was `simp`
    rw [Prod.ext_iff]
    simp

Depends on / 依赖: Finset, Finset.card_fin, Finset.card_image_of_injective, card_fin, card_image_of_injective
-/
theorem graph.card (f : Fin n -> α) : (graph f).card = n := by
  rw [graph]; rw [Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: proof was `simp`
    rw [Prod.ext_iff]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `graphEquiv₁` / `graphEquiv₁` 的定义

English:
definition graphEquiv₁
  signature: (f : Fin n -> α)
  body: ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

@[simp]

中文:
定义 graphEquiv₁
  签名: (f : 有限集 n -> α)
  定义体: ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

@[simp]
-/
def graphEquiv₁ (f : Fin n -> α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

@[simp]
/--
theorem `proj_equiv₁'` / 定理 `proj_equiv₁'`

English:
theorem proj_equiv₁'
  given: (f : Fin n -> α)
  statement: graph.proj ∘ graphEquiv₁ f = f
  proof: rfl

中文:
定理 proj_equiv₁'
  条件: (f : 有限集 n -> α)
  结论: graph.proj ∘ graphEquiv₁ f = f
  证明: rfl
-/
theorem proj_equiv₁' (f : Fin n -> α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/--
Definition of `graphEquiv₂` / `graphEquiv₂` 的定义

English:
definition graphEquiv₂
  signature: (f : Fin n -> α)
  body: Finset.orderIsoOfFin _ (by simp)

中文:
定义 graphEquiv₂
  签名: (f : 有限集 n -> α)
  定义体: Finset.orderIsoOfFin _ (by simp)

Depends on / 依赖: Finset, Finset.orderIsoOfFin, orderIsoOfFin
-/
def graphEquiv₂ (f : Fin n -> α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

/--
Definition of `sort` / `sort` 的定义

English:
definition sort
  signature: (f : Fin n -> α)
  body: (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

中文:
定义 sort
  签名: (f : 有限集 n -> α)
  定义体: (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

Depends on / 依赖: toEquiv, toEquiv.trans
-/
def sort (f : Fin n -> α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

/--
theorem `graphEquiv₂_apply` / 定理 `graphEquiv₂_apply`

English:
theorem graphEquiv₂_apply
  given: (f : Fin n -> α) (i : Fin n)
  proof: ((graphEquiv₁ f).apply_symm_apply _).symm

中文:
定理 graphEquiv₂_apply
  条件: (f : 有限集 n -> α) (i : 有限集 n)
  证明: ((graphEquiv₁ f).apply_symm_apply _).symm

Depends on / 依赖: apply_symm_apply
-/
theorem graphEquiv₂_apply (f : Fin n -> α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm

/--
theorem `self_comp_sort` / 定理 `self_comp_sort`

English:
theorem self_comp_sort
  given: (f : Fin n -> α)
  statement: f ∘ sort f = graph.proj ∘ graphEquiv₂ f
  proof: show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp

中文:
定理 self_comp_sort
  条件: (f : 有限集 n -> α)
  结论: f ∘ sort f = graph.proj ∘ graphEquiv₂ f
  证明: show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp

Depends on / 依赖: graph.proj, toEquiv
-/
theorem self_comp_sort (f : Fin n -> α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp

/--
theorem `monotone_proj` / 定理 `monotone_proj`

English:
theorem monotone_proj
  given: (f : Fin n -> α)
  statement: Monotone (graph.proj : graph f -> α)
  proof: by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]

中文:
定理 monotone_proj
  条件: (f : 有限集 n -> α)
  结论: 递增 (graph.proj : graph f -> α)
  证明: by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]

Depends on / 依赖: graph.proj, le_of_lt
-/
theorem monotone_proj (f : Fin n -> α) : Monotone (graph.proj : graph f -> α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]

/--
theorem `monotone_sort` / 定理 `monotone_sort`

English:
theorem monotone_sort
  given: (f : Fin n -> α)
  statement: Monotone (f ∘ sort f)
  proof: by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

中文:
定理 monotone_sort
  条件: (f : 有限集 n -> α)
  结论: 递增 (f ∘ sort f)
  证明: by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

Depends on / 依赖: monotone, monotone_proj, self_comp_sort
-/
theorem monotone_sort (f : Fin n -> α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

end Tuple

namespace Tuple

open List

variable {n : Nat} {α : Type*}

section

open Finset

variable {j : Fin n} {f : Fin n -> α} [Preorder α] {a : α}

/--
theorem `lt_card_le_iff_apply_le_of_monotone` / 定理 `lt_card_le_iff_apply_le_of_monotone`

English:
theorem lt_card_le_iff_apply_le_of_monotone
  given: [DecidableLE α] (h_sorted : Monotone f)
  proof: Fin.lt_card_filter_univ_iff_apply_of_imp (f · <= a) (by grind [Monotone])

中文:
定理 lt_card_le_iff_apply_le_of_monotone
  条件: [DecidableLE α] (h_sorted : 递增 f)
  证明: Fin.lt_card_filter_univ_iff_apply_of_imp (f · <= a) (by grind [Monotone])

Depends on / 依赖: Fin.lt_card_filter_univ_iff_apply_of_imp, Monotone, lt_card_filter_univ_iff_apply_of_imp
-/
theorem lt_card_le_iff_apply_le_of_monotone [DecidableLE α] (h_sorted : Monotone f) :
    j < #{i | f i <= a} ↔ f j <= a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · <= a) (by grind [Monotone])

/--
theorem `lt_card_ge_iff_apply_ge_of_antitone` / 定理 `lt_card_ge_iff_apply_ge_of_antitone`

English:
theorem lt_card_ge_iff_apply_ge_of_antitone
  given: [DecidableLE α] (h_sorted : Antitone f)
  proof: Fin.lt_card_filter_univ_iff_apply_of_imp (a <= f ·) (by grind [Antitone])

中文:
定理 lt_card_ge_iff_apply_ge_of_antitone
  条件: [DecidableLE α] (h_sorted : 递减 f)
  证明: Fin.lt_card_filter_univ_iff_apply_of_imp (a <= f ·) (by grind [Antitone])

Depends on / 依赖: Antitone, Fin.lt_card_filter_univ_iff_apply_of_imp, lt_card_filter_univ_iff_apply_of_imp
-/
theorem lt_card_ge_iff_apply_ge_of_antitone [DecidableLE α] (h_sorted : Antitone f) :
    j < #{i | a <= f i} ↔ a <= f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a <= f ·) (by grind [Antitone])

/--
theorem `lt_card_lt_iff_apply_lt_of_monotone` / 定理 `lt_card_lt_iff_apply_lt_of_monotone`

English:
theorem lt_card_lt_iff_apply_lt_of_monotone
  given: [DecidableLT α] (h_sorted : Monotone f)
  proof: Fin.lt_card_filter_univ_iff_apply_of_imp (f · < a) (by grind [Monotone])

中文:
定理 lt_card_lt_iff_apply_lt_of_monotone
  条件: [DecidableLT α] (h_sorted : 递增 f)
  证明: Fin.lt_card_filter_univ_iff_apply_of_imp (f · < a) (by grind [Monotone])

Depends on / 依赖: Fin.lt_card_filter_univ_iff_apply_of_imp, Monotone, lt_card_filter_univ_iff_apply_of_imp
-/
theorem lt_card_lt_iff_apply_lt_of_monotone [DecidableLT α] (h_sorted : Monotone f) :
    j < #{i | f i < a} ↔ f j < a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · < a) (by grind [Monotone])

/--
theorem `lt_card_gt_iff_apply_gt_of_antitone` / 定理 `lt_card_gt_iff_apply_gt_of_antitone`

English:
theorem lt_card_gt_iff_apply_gt_of_antitone
  given: [DecidableLT α] (h_sorted : Antitone f)
  proof: Fin.lt_card_filter_univ_iff_apply_of_imp (a < f ·) (by grind [Antitone])

中文:
定理 lt_card_gt_iff_apply_gt_of_antitone
  条件: [DecidableLT α] (h_sorted : 递减 f)
  证明: Fin.lt_card_filter_univ_iff_apply_of_imp (a < f ·) (by grind [Antitone])

Depends on / 依赖: Antitone, Fin.lt_card_filter_univ_iff_apply_of_imp, lt_card_filter_univ_iff_apply_of_imp
-/
theorem lt_card_gt_iff_apply_gt_of_antitone [DecidableLT α] (h_sorted : Antitone f) :
    j < #{i | a < f i} ↔ a < f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a < f ·) (by grind [Antitone])

end

/--
theorem `unique_monotone` / 定理 `unique_monotone`

English:
theorem unique_monotone
  statement: [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n)}
  proof: ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedLE_ofFn.pairwise hfτ.sortedLE_ofFn.pairwise

中文:
定理 unique_monotone
  结论: [偏序 α] {f : 有限集 n -> α} {σ τ : 等价.置换 (有限集 n)}
  证明: ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedLE_ofFn.pairwise hfτ.sortedLE_ofFn.pairwise

Depends on / 依赖: eq_of_pairwise, ofFn_comp_perm, ofFn_injective, pairwise, sortedLE_ofFn, sortedLE_ofFn.pairwise
-/
theorem unique_monotone [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedLE_ofFn.pairwise hfτ.sortedLE_ofFn.pairwise

/--
theorem `unique_antitone` / 定理 `unique_antitone`

English:
theorem unique_antitone
  statement: [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n)}
  proof: ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedGE_ofFn.pairwise hfτ.sortedGE_ofFn.pairwise

中文:
定理 unique_antitone
  结论: [偏序 α] {f : 有限集 n -> α} {σ τ : 等价.置换 (有限集 n)}
  证明: ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedGE_ofFn.pairwise hfτ.sortedGE_ofFn.pairwise

Depends on / 依赖: eq_of_pairwise, ofFn_comp_perm, ofFn_injective, pairwise, sortedGE_ofFn, sortedGE_ofFn.pairwise
-/
theorem unique_antitone [PartialOrder α] {f : Fin n -> α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Antitone (f ∘ σ)) (hfτ : Antitone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
ofFn_injective
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedGE_ofFn.pairwise hfτ.sortedGE_ofFn.pairwise

variable [LinearOrder α] {f : Fin n -> α} {σ : Equiv.Perm (Fin n)}

/--
theorem `eq_sort_iff'` / 定理 `eq_sort_iff'`

English:
theorem eq_sort_iff'
  statement: σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f)
  proof: by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).eq_symm_apply.2 (DFunLike.congr_fun this x)

中文:
定理 eq_sort_iff'
  结论: σ = sort f ↔ 严格递增 (σ.trans <| graphEquiv₁ f)
  证明: by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).eq_symm_apply.2 (DFunLike.congr_fun this x)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Equiv.surjective, Equiv.symm_trans_self, Equiv.trans_assoc, Subsingleton, Subsingleton.elim, congr_fun, eq_symm_apply, h.orderIsoOfSurjective, orderIsoOfSurjective, strictMono, surjective, symm_trans_self, trans_assoc
-/
theorem eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f) := by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).eq_symm_apply.2 (DFunLike.congr_fun this x).symm

/--
theorem `eq_sort_iff` / 定理 `eq_sort_iff`

English:
theorem eq_sort_iff
  proof: by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨

中文:
定理 eq_sort_iff
  证明: by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨

Depends on / 依赖: Or.inl, Or.inr, Prod.Lex.toLex_lt_toLex, eq_or_lt, eq_sort_iff, exacts, h.monotone, hfij.not_lt, hij.le, monotone, monotone_proj, not_lt, resolve_left, toLex_lt_toLex
-/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ forall i j, i < j -> f (σ i) = f (σ j) -> σ i < σ j := by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]

/--
theorem `sort_eq_refl_iff_monotone` / 定理 `sort_eq_refl_iff_monotone`

English:
theorem sort_eq_refl_iff_monotone
  statement: sort f = Equiv.refl _ ↔ Monotone f
  proof: by
  rw [eq_comm]; rw [eq_sort_iff]; rw [Equiv.coe_refl]; rw [Function.comp_id]
  simp only [id, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

中文:
定理 sort_eq_refl_iff_monotone
  结论: sort f = 等价.refl _ ↔ 递增 f
  证明: by
  rw [eq_comm]; rw [eq_sort_iff]; rw [Equiv.coe_refl]; rw [Function.comp_id]
  simp only [id, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

Depends on / 依赖: Equiv.coe_refl, Function, Function.comp_id, and_iff_left_iff_imp, coe_refl, comp_id, eq_comm, eq_sort_iff
-/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm]; rw [eq_sort_iff]; rw [Equiv.coe_refl]; rw [Function.comp_id]
  simp only [id, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

/--
theorem `comp_sort_eq_comp_iff_monotone` / 定理 `comp_sort_eq_comp_iff_monotone`

English:
theorem comp_sort_eq_comp_iff_monotone
  statement: f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ)
  proof: ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

中文:
定理 comp_sort_eq_comp_iff_monotone
  结论: f ∘ σ = f ∘ sort f ↔ 递增 (f ∘ σ)
  证明: ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

Depends on / 依赖: h.symm, monotone_sort, unique_monotone
-/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

/--
theorem `comp_perm_comp_sort_eq_comp_sort` / 定理 `comp_perm_comp_sort_eq_comp_sort`

English:
theorem comp_perm_comp_sort_eq_comp_sort
  statement: (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f
  proof: by
  rw [Function.comp_assoc]; rw [← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

中文:
定理 comp_perm_comp_sort_eq_comp_sort
  结论: (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f
  证明: by
  rw [Function.comp_assoc]; rw [← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

Depends on / 依赖: Equiv.Perm.coe_mul, Function, Function.comp_assoc, coe_mul, comp_assoc, monotone_sort, unique_monotone
-/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp_assoc]; rw [← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

/--
theorem `antitone_pair_of_not_sorted'` / 定理 `antitone_pair_of_not_sorted'`

English:
theorem antitone_pair_of_not_sorted'
  given: (h : f ∘ σ != f ∘ sort f)
  proof: by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)

中文:
定理 antitone_pair_of_not_sorted'
  条件: (h : f ∘ σ != f ∘ sort f)
  证明: by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)

Depends on / 依赖: comp_sort_eq_comp_iff_monotone, comp_sort_eq_comp_iff_monotone.mpr, contrapose, monotone_iff_forall_lt, monotone_iff_forall_lt.mpr
-/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ != f ∘ sort f) :
    exists i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i := by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)

/--
theorem `antitone_pair_of_not_sorted` / 定理 `antitone_pair_of_not_sorted`

English:
theorem antitone_pair_of_not_sorted
  given: (h : f != f ∘ sort f)
  statement: exists i j, i < j ∧ f j < f i
  proof: antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ != _)

中文:
定理 antitone_pair_of_not_sorted
  条件: (h : f != f ∘ sort f)
  结论: 存在 i j, i < j ∧ f j < f i
  证明: antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ != _)

Depends on / 依赖: Equiv.refl, antitone_pair_of_not_sorted
-/
theorem antitone_pair_of_not_sorted (h : f != f ∘ sort f) : exists i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ != _)

/-- The sorted version of a permutation `σ` is its inverse `σ⁻¹`. -/
@[simp]
/--
theorem `sort_perm` / 定理 `sort_perm`

English:
theorem sort_perm
  given: (σ : Equiv.Perm (Fin n))
  proof: by
  apply (eq_sort_iff.2 ⟨?_ , ?_⟩).symm
  · simpa using monotone_id
  · intro _ _ hij h
    exact (hij.ne (by simpa using h)).elim

中文:
定理 sort_perm
  条件: (σ : 等价.置换 (有限集 n))
  证明: by
  apply (eq_sort_iff.2 ⟨?_ , ?_⟩).symm
  · simpa using monotone_id
  · intro _ _ hij h
    exact (hij.ne (by simpa using h)).elim

Depends on / 依赖: eq_sort_iff, hij.ne, monotone_id
-/
theorem sort_perm (σ : Equiv.Perm (Fin n)) :
    sort σ = σ⁻¹ := by
  apply (eq_sort_iff.2 ⟨?_ , ?_⟩).symm
  · simpa using monotone_id
  · intro _ _ hij h
    exact (hij.ne (by simpa using h)).elim

end Tuple

/--
theorem `Equiv.Perm.monotone_iff` / 定理 `Equiv.Perm.monotone_iff`

English:
theorem Equiv.Perm.monotone_iff
  given: {n : Nat} (σ : Perm (Fin n))
  proof: by
  rw [← Tuple.sort_eq_refl_iff_monotone]; rw [Tuple.sort_perm]; rw [← inv_eq_one]; rw [one_def]

中文:
定理 等价.置换.monotone_iff
  条件: {n : 自然数} (σ : 置换 (有限集 n))
  证明: by
  rw [← Tuple.sort_eq_refl_iff_monotone]; rw [Tuple.sort_perm]; rw [← inv_eq_one]; rw [one_def]

Depends on / 依赖: Tuple.sort_eq_refl_iff_monotone, Tuple.sort_perm, inv_eq_one, one_def, sort_eq_refl_iff_monotone, sort_perm
-/
theorem Equiv.Perm.monotone_iff {n : Nat} (σ : Perm (Fin n)) :
    Monotone σ ↔ σ = 1 := by
  rw [← Tuple.sort_eq_refl_iff_monotone]; rw [Tuple.sort_perm]; rw [← inv_eq_one]; rw [one_def]
