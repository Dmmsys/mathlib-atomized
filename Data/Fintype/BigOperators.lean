/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Vector

/-!
Results about "big operations" over a `Fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `Data.Fintype.Basic`, but was moved here to avoid
requiring `Algebra.BigOperators` (and hence many other imports) as a
dependency of `Fintype`.

However many of the results here really belong in `Algebra.BigOperators.Group.Finset`
and should be moved at some point.
-/

public section

assert_not_exists MulAction

open Mathlib

universe u v

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Fintype

@[to_additive]
/--
theorem `prod_bool` / 定理 `prod_bool`

English:
theorem prod_bool
  given: [CommMonoid α] (f : Bool -> α)
  statement: ∏ b, f b = f true * f false
  proof: by simp

中文:
定理 prod_bool
  条件: [交换幺半群 α] (f : 布尔值 -> α)
  结论: ∏ b, f b = f true * f false
  证明: by simp
-/
theorem prod_bool [CommMonoid α] (f : Bool -> α) : ∏ b, f b = f true * f false := by simp

/--
theorem `card_eq_sum_ones` / 定理 `card_eq_sum_ones`

English:
theorem card_eq_sum_ones
  given: {α} [Fintype α]
  statement: Fintype.card α = ∑ _a : α, 1
  proof: Finset.card_eq_sum_ones _

中文:
定理 card_eq_sum_ones
  条件: {α} [有限类型 α]
  结论: 有限类型.card α = ∑ _a : α, 1
  证明: Finset.card_eq_sum_ones _

Depends on / 依赖: Finset, Finset.card_eq_sum_ones, card_eq_sum_ones
-/
theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ _a : α, 1 :=
  Finset.card_eq_sum_ones _

section

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

@[to_additive]
/--
theorem `prod_extend_by_one` / 定理 `prod_extend_by_one`

English:
theorem prod_extend_by_one
  given: [CommMonoid α] (s : Finset ι) (f : ι -> α)
  proof: by
  rw [← prod_filter]; rw [filter_mem_eq_inter]; rw [univ_inter]

中文:
定理 prod_extend_by_one
  条件: [交换幺半群 α] (s : 有限集 ι) (f : ι -> α)
  证明: by
  rw [← prod_filter]; rw [filter_mem_eq_inter]; rw [univ_inter]

Depends on / 依赖: filter_mem_eq_inter, prod_filter, univ_inter
-/
theorem prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι -> α) :
    ∏ i, (if i in s then f i else 1) = ∏ i in s, f i := by
  rw [← prod_filter]; rw [filter_mem_eq_inter]; rw [univ_inter]

end

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive]
/--
theorem `prod_eq_one` / 定理 `prod_eq_one`

English:
theorem prod_eq_one
  given: (f : α -> M) (h : forall a, f a = 1)
  statement: ∏ a, f a = 1
  proof: Finset.prod_eq_one fun a _ha => h a

@[to_additive]

中文:
定理 prod_eq_one
  条件: (f : α -> M) (h : 对任意 a, f a = 1)
  结论: ∏ a, f a = 1
  证明: Finset.prod_eq_one fun a _ha => h a

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_one, prod_eq_one
-/
theorem prod_eq_one (f : α -> M) (h : forall a, f a = 1) : ∏ a, f a = 1 :=
  Finset.prod_eq_one fun a _ha => h a

@[to_additive]
/--
theorem `prod_congr` / 定理 `prod_congr`

English:
theorem prod_congr
  given: (f g : α -> M) (h : forall a, f a = g a)
  statement: ∏ a, f a = ∏ a, g a
  proof: Finset.prod_congr rfl fun a _ha => h a

@[to_additive]

中文:
定理 prod_congr
  条件: (f g : α -> M) (h : 对任意 a, f a = g a)
  结论: ∏ a, f a = ∏ a, g a
  证明: Finset.prod_congr rfl fun a _ha => h a

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_congr, prod_congr
-/
theorem prod_congr (f g : α -> M) (h : forall a, f a = g a) : ∏ a, f a = ∏ a, g a :=
  Finset.prod_congr rfl fun a _ha => h a

@[to_additive]
/--
theorem `prod_eq_single` / 定理 `prod_eq_single`

English:
theorem prod_eq_single
  given: {f : α -> M} (a : α) (h : forall x != a, f x = 1)
  statement: ∏ x, f x = f a
  proof: Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim

@[to_additive]

中文:
定理 prod_eq_single
  条件: {f : α -> M} (a : α) (h : 对任意 x != a, f x = 1)
  结论: ∏ x, f x = f a
  证明: Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim

@[to_additive]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_eq_single, mem_univ, prod_eq_single
-/
theorem prod_eq_single {f : α -> M} (a : α) (h : forall x != a, f x = 1) : ∏ x, f x = f a :=
  Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim

@[to_additive]
/--
theorem `prod_eq_mul` / 定理 `prod_eq_mul`

English:
theorem prod_eq_mul
  given: {f : α -> M} (a b : α) (h₁ : a != b) (h₂ : forall x, x != a ∧ x != b -> f x = 1)
  proof: by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim

中文:
定理 prod_eq_mul
  条件: {f : α -> M} (a b : α) (h₁ : a != b) (h₂ : 对任意 x, x != a ∧ x != b -> f x = 1)
  证明: by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_eq_mul, mem_univ, prod_eq_mul
-/
theorem prod_eq_mul {f : α -> M} (a b : α) (h₁ : a != b) (h₂ : forall x, x != a ∧ x != b -> f x = 1) :
    ∏ x, f x = f a * f b := by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim

/-- If a product of a `Finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive /-- If a sum of a `Finset` of a subsingleton type has a given
  value, so do the terms in that sum. -/]
/--
theorem `eq_of_subsingleton_of_prod_eq` / 定理 `eq_of_subsingleton_of_prod_eq`

English:
theorem eq_of_subsingleton_of_prod_eq
  statement: {ι : Type*} [Subsingleton ι] {s : Finset ι} {f : ι -> M}
  proof: Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

中文:
定理 eq_of_subsingleton_of_prod_eq
  结论: {ι : 类型} [子单例 ι] {s : 有限集 ι} {f : ι -> M}
  证明: Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

Depends on / 依赖: Finset, Finset.card_le_one_of_subsingleton, Finset.eq_of_card_le_one_of_prod_eq, card_le_one_of_subsingleton, eq_of_card_le_one_of_prod_eq
-/
theorem eq_of_subsingleton_of_prod_eq {ι : Type*} [Subsingleton ι] {s : Finset ι} {f : ι -> M}
    {b : M} (h : ∏ i in s, f i = b) : forall i in s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

end

end Fintype

open Finset

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive (attr := simp)]
/--
theorem `Fintype.prod_option` / 定理 `Fintype.prod_option`

English:
theorem Fintype.prod_option
  given: (f : Option α -> M)
  statement: ∏ i, f i = f none * ∏ i, f (some i)
  proof: Finset.prod_insertNone f univ

@[to_additive]

中文:
定理 有限类型.prod_option
  条件: (f : 选项类型 α -> M)
  结论: ∏ i, f i = f none * ∏ i, f (some i)
  证明: Finset.prod_insertNone f univ

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_insertNone, prod_insertNone
-/
theorem Fintype.prod_option (f : Option α -> M) : ∏ i, f i = f none * ∏ i, f (some i) :=
  Finset.prod_insertNone f univ

@[to_additive]
/--
theorem `Fintype.prod_eq_mul_prod_subtype_ne` / 定理 `Fintype.prod_eq_mul_prod_subtype_ne`

English:
theorem Fintype.prod_eq_mul_prod_subtype_ne
  given: [DecidableEq α] (f : α -> M) (a : α)
  proof: by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]

中文:
定理 有限类型.prod_eq_mul_prod_subtype_ne
  条件: [DecidableEq α] (f : α -> M) (a : α)
  证明: by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]

Depends on / 依赖: Equiv.optionSubtypeNe, Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some, optionSubtypeNe, optionSubtypeNe_none, optionSubtypeNe_some, prod_comp, prod_option, simp_rw
-/
theorem Fintype.prod_eq_mul_prod_subtype_ne [DecidableEq α] (f : α -> M) (a : α) :
    ∏ i, f i = f a * ∏ i : {i // i != a}, f i.1 := by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]

end

section Pi
variable {ι κ : Type*} {α : ι -> Type*} [DecidableEq ι] [DecidableEq κ]

/--
lemma `Finset.card_pi` / 引理 `Finset.card_pi`

English:
lemma Finset.card_pi
  given: (s : Finset ι) (t : forall i, Finset (α i))
  proof: Multiset.card_pi _ _

中文:
引理 有限集.card_pi
  条件: (s : 有限集 ι) (t : 对任意 i, 有限集 (α i))
  证明: Multiset.card_pi _ _
-/
@[simp] lemma Finset.card_pi (s : Finset ι) (t : forall i, Finset (α i)) :
    #(s.pi t) = ∏ i in s, #(t i) := Multiset.card_pi _ _

namespace Fintype

variable [Fintype ι]

/--
lemma `card_piFinset` / 引理 `card_piFinset`

English:
lemma card_piFinset
  given: (s : forall i, Finset (α i))
  proof: by simp [piFinset, card_map]

中文:
引理 card_piFinset
  条件: (s : 对任意 i, 有限集 (α i))
  证明: by simp [piFinset, card_map]
-/
@[simp] lemma card_piFinset (s : forall i, Finset (α i)) :
    #(piFinset s) = ∏ i, #(s i) := by simp [piFinset, card_map]

/--
lemma `card_piFinset_const` / 引理 `card_piFinset_const`

English:
lemma card_piFinset_const
  given: {α : Type*} (s : Finset α) (n : Nat)
  proof: by simp

中文:
引理 card_piFinset_const
  条件: {α : 类型} (s : 有限集 α) (n : 自然数)
  证明: by simp
-/
lemma card_piFinset_const {α : Type*} (s : Finset α) (n : Nat) :
    #(piFinset fun _ : Fin n => s) = #s ^ n := by simp

/--
lemma `card_pi` / 引理 `card_pi`

English:
lemma card_pi
  given: [forall i, Fintype (α i)]
  statement: card (forall i, α i) = ∏ i, card (α i)
  proof: card_piFinset _

中文:
引理 card_pi
  条件: [对任意 i, 有限类型 (α i)]
  结论: card (对任意 i, α i) = ∏ i, card (α i)
  证明: card_piFinset _
-/
@[simp] lemma card_pi [forall i, Fintype (α i)] : card (forall i, α i) = ∏ i, card (α i) :=
  card_piFinset _

/--
lemma `card_pi_const` / 引理 `card_pi_const`

English:
lemma card_pi_const
  given: (α : Type*) [Fintype α] (n : Nat)
  statement: card (Fin n -> α) = card α ^ n
  proof: card_piFinset_const _ _

中文:
引理 card_pi_const
  条件: (α : 类型) [有限类型 α] (n : 自然数)
  结论: card (有限集 n -> α) = card α ^ n
  证明: card_piFinset_const _ _

Depends on / 依赖: card_piFinset_const
-/
lemma card_pi_const (α : Type*) [Fintype α] (n : Nat) : card (Fin n -> α) = card α ^ n :=
  card_piFinset_const _ _

/-- Product over a sigma type equals the repeated product.

This is a version of `Finset.prod_sigma` specialized to the case
of multiplication over `Finset.univ`. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum.

This is a version of `Finset.sum_sigma` specialized to the case of summation over `Finset.univ`. -/]
/--
theorem `prod_sigma` / 定理 `prod_sigma`

English:
theorem prod_sigma
  statement: {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintype (α i)] [CommMonoid M]
  proof: Finset.prod_sigma ..

中文:
定理 prod_sigma
  结论: {ι} {α : ι -> 类型} {M : 类型} [有限类型 ι] [对任意 i, 有限类型 (α i)] [交换幺半群 M]
  证明: Finset.prod_sigma ..

Depends on / 依赖: Finset, Finset.prod_sigma, prod_sigma
-/
theorem prod_sigma {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintype (α i)] [CommMonoid M]
    (f : Sigma α -> M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩ :=
  Finset.prod_sigma ..

/-- Product over a sigma type equals the repeated product, curried version.
This version is useful to rewrite from right to left. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum, curried version.
This version is useful to rewrite from right to left. -/]
/--
theorem `prod_sigma'` / 定理 `prod_sigma'`

English:
theorem prod_sigma'
  statement: {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintype (α i)] [CommMonoid M]
  proof: prod_sigma ..

@[simp] nonrec lemma card_sigma {ι} {α : ι -> Type*} [Fintype ι] [forall i, Fintype (α i)] :
    card (Sigma α) = ∑ i, card (α i) := card_sigma _ _

中文:
定理 prod_sigma'
  结论: {ι} {α : ι -> 类型} {M : 类型} [有限类型 ι] [对任意 i, 有限类型 (α i)] [交换幺半群 M]
  证明: prod_sigma ..

@[simp] nonrec lemma card_sigma {ι} {α : ι -> Type*} [Fintype ι] [forall i, Fintype (α i)] :
    card (Sigma α) = ∑ i, card (α i) := card_sigma _ _

Depends on / 依赖: prod_sigma
-/
theorem prod_sigma' {ι} {α : ι -> Type*} {M : Type*} [Fintype ι] [forall i, Fintype (α i)] [CommMonoid M]
    (f : (i : ι) -> α i -> M) : ∏ x : Sigma α, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  prod_sigma ..

@[simp] nonrec lemma card_sigma {ι} {α : ι -> Type*} [Fintype ι] [forall i, Fintype (α i)] :
    card (Sigma α) = ∑ i, card (α i) := card_sigma _ _

/--
lemma `card_filter_piFinset_eq_of_mem` / 引理 `card_filter_piFinset_eq_of_mem`

English:
lemma card_filter_piFinset_eq_of_mem
  statement: [forall i, DecidableEq (α i)]
  proof: by
  calc
    _ = ∏ j, #(Function.update s i {a} j) := by
      rw [← piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha]; rw [Fintype.card_piFinset]
    _ = ∏ j, Function.update (fun j => #(s j)) i 1 j :=
      Fintype.prod_congr _ _ fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    _ = _ := by simp [prod_update_of_mem, erase_eq]

中文:
引理 card_filter_piFinset_eq_of_mem
  结论: [对任意 i, DecidableEq (α i)]
  证明: by
  calc
    _ = ∏ j, #(Function.update s i {a} j) := by
      rw [← piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha]; rw [Fintype.card_piFinset]
    _ = ∏ j, Function.update (fun j => #(s j)) i 1 j :=
      Fintype.prod_congr _ _ fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    _ = _ := by simp [prod_update_of_mem, erase_eq]

Depends on / 依赖: Fintype, Fintype.card_piFinset, Fintype.prod_congr, Function, Function.update, card_piFinset, eq_or_ne, erase_eq, piFinset_update_singleton_eq_filter_piFinset_eq, prod_congr, prod_update_of_mem, update
-/
lemma card_filter_piFinset_eq_of_mem [forall i, DecidableEq (α i)]
    (s : forall i, Finset (α i)) (i : ι) {a : α i} (ha : a in s i) :
    #{f in piFinset s | f i = a} = ∏ j in univ.erase i, #(s j) := by
  calc
    _ = ∏ j, #(Function.update s i {a} j) := by
      rw [← piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha]; rw [Fintype.card_piFinset]
    _ = ∏ j, Function.update (fun j => #(s j)) i 1 j :=
      Fintype.prod_congr _ _ fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    _ = _ := by simp [prod_update_of_mem, erase_eq]

/--
lemma `card_filter_piFinset_const_eq_of_mem` / 引理 `card_filter_piFinset_const_eq_of_mem`

English:
lemma card_filter_piFinset_const_eq_of_mem
  given: (s : Finset κ) (i : ι) {x : κ} (hx : x in s)
  proof: (card_filter_piFinset_eq_of_mem _ _ hx).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

中文:
引理 card_filter_piFinset_const_eq_of_mem
  条件: (s : 有限集 κ) (i : ι) {x : κ} (hx : x in s)
  证明: (card_filter_piFinset_eq_of_mem _ _ hx).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

Depends on / 依赖: card_erase_of_mem, card_filter_piFinset_eq_of_mem, card_univ, mem_univ, prod_const
-/
lemma card_filter_piFinset_const_eq_of_mem (s : Finset κ) (i : ι) {x : κ} (hx : x in s) :
    #{f in piFinset fun _ => s | f i = x} = #s ^ (card ι - 1) :=
(card_filter_piFinset_eq_of_mem _ _ hx).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

/--
lemma `card_filter_piFinset_eq` / 引理 `card_filter_piFinset_eq`

English:
lemma card_filter_piFinset_eq
  given: [forall i, DecidableEq (α i)] (s : forall i, Finset (α i)) (i : ι) (a : α i)
  proof: by
  split_ifs with h
  · rw [card_filter_piFinset_eq_of_mem _ _ h]
  · rw [filter_piFinset_of_notMem _ _ _ h, Finset.card_empty]

中文:
引理 card_filter_piFinset_eq
  条件: [对任意 i, DecidableEq (α i)] (s : 对任意 i, 有限集 (α i)) (i : ι) (a : α i)
  证明: by
  split_ifs with h
  · rw [card_filter_piFinset_eq_of_mem _ _ h]
  · rw [filter_piFinset_of_notMem _ _ _ h, Finset.card_empty]

Depends on / 依赖: Finset, Finset.card_empty, card_empty, card_filter_piFinset_eq_of_mem, filter_piFinset_of_notMem, split_ifs
-/
lemma card_filter_piFinset_eq [forall i, DecidableEq (α i)] (s : forall i, Finset (α i)) (i : ι) (a : α i) :
    #{f in piFinset s | f i = a} = if a in s i then ∏ b in univ.erase i, #(s b) else 0 := by
  split_ifs with h
  · rw [card_filter_piFinset_eq_of_mem _ _ h]
  · rw [filter_piFinset_of_notMem _ _ _ h, Finset.card_empty]

/--
lemma `card_filter_piFinset_const` / 引理 `card_filter_piFinset_const`

English:
lemma card_filter_piFinset_const
  given: (s : Finset κ) (i : ι) (j : κ)
  proof: (card_filter_piFinset_eq _ _ _).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

中文:
引理 card_filter_piFinset_const
  条件: (s : 有限集 κ) (i : ι) (j : κ)
  证明: (card_filter_piFinset_eq _ _ _).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

Depends on / 依赖: card_erase_of_mem, card_filter_piFinset_eq, card_univ, mem_univ, prod_const
-/
lemma card_filter_piFinset_const (s : Finset κ) (i : ι) (j : κ) :
    #{f in piFinset fun _ => s | f i = j} = if j in s then #s ^ (card ι - 1) else 0 :=
(card_filter_piFinset_eq _ _ _).trans by
    rw [prod_const #s]; rw [card_erase_of_mem (mem_univ _)]; rw [card_univ]

end Fintype
end Pi

-- TODO: this is a basic theorem about `Fintype.card`,
-- and ideally could be moved to `Mathlib/Data/Fintype/Card.lean`.
/--
theorem `Fintype.card_fun` / 定理 `Fintype.card_fun`

English:
theorem Fintype.card_fun
  given: [DecidableEq α] [Fintype α] [Fintype β]
  proof: by
  simp

@[simp]

中文:
定理 有限类型.card_fun
  条件: [DecidableEq α] [有限类型 α] [有限类型 β]
  证明: by
  simp

@[simp]
-/
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α -> β) = Fintype.card β ^ Fintype.card α := by
  simp

@[simp]
/--
theorem `card_vector` / 定理 `card_vector`

English:
theorem card_vector
  given: [Fintype α] (n : Nat)
  proof: by
  rw [Fintype.ofEquiv_card]; simp

中文:
定理 card_vector
  条件: [有限类型 α] (n : 自然数)
  证明: by
  rw [Fintype.ofEquiv_card]; simp

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, ofEquiv_card
-/
theorem card_vector [Fintype α] (n : Nat) :
    Fintype.card (List.Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card]; simp

/--
lemma `Finset.card_filter_length_eq_le` / 引理 `Finset.card_filter_length_eq_le`

English:
lemma Finset.card_filter_length_eq_le
  given: [Fintype α] {T : Finset (List α)} {s : Nat}
  proof: by
  classical
  calc
    _ <= (Finset.univ.image List.ofFn).card := by
          apply Finset.card_le_card
          intro a ha
          let hlen := Finset.mem_filter.mp ha
          exact Finset.mem_image.mpr ⟨
              (fun j : Fin s => a.get ⟨j.val, by simp [hlen]⟩),
              by simp,
              List.ext_get (by simp [hlen]) (by simp)⟩
    _ = Fintype.card α ^ s := by
          simp [card_image_of_injective univ List.ofFn_injective]

中文:
引理 有限集.card_filter_length_eq_le
  条件: [有限类型 α] {T : 有限集 (列表 α)} {s : 自然数}
  证明: by
  classical
  calc
    _ <= (Finset.univ.image List.ofFn).card := by
          apply Finset.card_le_card
          intro a ha
          let hlen := Finset.mem_filter.mp ha
          exact Finset.mem_image.mpr ⟨
              (fun j : Fin s => a.get ⟨j.val, by simp [hlen]⟩),
              by simp,
              List.ext_get (by simp [hlen]) (by simp)⟩
    _ = Fintype.card α ^ s := by
          simp [card_image_of_injective univ List.ofFn_injective]

Depends on / 依赖: Finset, Finset.card_le_card, Finset.mem_filter.mp, Finset.mem_image.mpr, Finset.univ.image, Fintype, Fintype.card, List.ext_get, List.ofFn, List.ofFn_injective, a.get, card_image_of_injective, card_le_card, classical, ext_get, j.val, mem_filter, mem_image, ofFn_injective
-/
lemma Finset.card_filter_length_eq_le [Fintype α] {T : Finset (List α)} {s : Nat} :
    (T.filter (fun x => x.length = s)).card <= (Fintype.card α) ^ s := by
  classical
  calc
    _ <= (Finset.univ.image List.ofFn).card := by
          apply Finset.card_le_card
          intro a ha
          let hlen := Finset.mem_filter.mp ha
          exact Finset.mem_image.mpr ⟨
              (fun j : Fin s => a.get ⟨j.val, by simp [hlen]⟩),
              by simp,
              List.ext_get (by simp [hlen]) (by simp)⟩
    _ = Fintype.card α ^ s := by
          simp [card_image_of_injective univ List.ofFn_injective]

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive /-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/]
/--
theorem `Fin.prod_univ_eq_prod_range` / 定理 `Fin.prod_univ_eq_prod_range`

English:
theorem Fin.prod_univ_eq_prod_range
  given: [CommMonoid α] (f : Nat -> α) (n : Nat)
  proof: calc
    ∏ i : Fin n, f i = ∏ i : { x // x in range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]

@[to_additive]

中文:
定理 有限集.prod_univ_eq_prod_range
  条件: [交换幺半群 α] (f : 自然数 -> α) (n : 自然数)
  证明: calc
    ∏ i : Fin n, f i = ∏ i : { x // x in range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]

@[to_additive]

Depends on / 依赖: Equiv.subtypeEquivRight, Fin.equivSubtype.trans, Fintype, Fintype.prod_equiv, attach_eq_univ, equivSubtype, prod_attach, prod_equiv, subtypeEquivRight
-/
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : Nat -> α) (n : Nat) :
    ∏ i : Fin n, f i = ∏ i in range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x in range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]

@[to_additive]
/--
theorem `Finset.prod_fin_eq_prod_range` / 定理 `Finset.prod_fin_eq_prod_range`

English:
theorem Finset.prod_fin_eq_prod_range
  given: [CommMonoid β] {n : Nat} (c : Fin n -> β)
  proof: by
  rw [← Fin.prod_univ_eq_prod_range]; rw [Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]

@[to_additive]

中文:
定理 有限集.prod_fin_eq_prod_range
  条件: [交换幺半群 β] {n : 自然数} (c : 有限集 n -> β)
  证明: by
  rw [← Fin.prod_univ_eq_prod_range]; rw [Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]

@[to_additive]

Depends on / 依赖: Fin.prod_univ_eq_prod_range, Finset, Finset.prod_congr, dif_pos, prod_congr, prod_univ_eq_prod_range
-/
theorem Finset.prod_fin_eq_prod_range [CommMonoid β] {n : Nat} (c : Fin n -> β) :
    ∏ i, c i = ∏ i in Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range]; rw [Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]

@[to_additive]
/--
theorem `Finset.prod_toFinset_eq_subtype` / 定理 `Finset.prod_toFinset_eq_subtype`

English:
theorem Finset.prod_toFinset_eq_subtype
  statement: {M : Type*} [CommMonoid M] [Fintype α] (p : α -> Prop)
  proof: by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl

nonrec theorem Fintype.prod_dite [Fintype α] {p : α -> Prop} [DecidablePred p] [CommMonoid β]
    (f : forall a, p a -> β) (g : forall a, ¬p a -> β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

中文:
定理 有限集.prod_toFinset_eq_subtype
  结论: {M : 类型} [交换幺半群 M] [有限类型 α] (p : α -> 命题)
  证明: by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl

nonrec theorem Fintype.prod_dite [Fintype α] {p : α -> Prop} [DecidablePred p] [CommMonoid β]
    (f : forall a, p a -> β) (g : forall a, ¬p a -> β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

Depends on / 依赖: Finset, Finset.prod_subtype, Set.mem_toFinset, mem_toFinset, prod_subtype, simp_rw
-/
theorem Finset.prod_toFinset_eq_subtype {M : Type*} [CommMonoid M] [Fintype α] (p : α -> Prop)
    [DecidablePred p] (f : α -> M) : ∏ a in { x | p x }.toFinset, f a = ∏ a : Subtype p, f a := by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl

nonrec theorem Fintype.prod_dite [Fintype α] {p : α -> Prop} [DecidablePred p] [CommMonoid β]
    (f : forall a, p a -> β) (g : forall a, ¬p a -> β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

section

variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
/--
theorem `Fintype.prod_sumElim` / 定理 `Fintype.prod_sumElim`

English:
theorem Fintype.prod_sumElim
  given: (f : α₁ -> M) (g : α₂ -> M)
  proof: prod_disjSum _ _ _

@[to_additive (attr := simp)]

中文:
定理 有限类型.prod_sumElim
  条件: (f : α₁ -> M) (g : α₂ -> M)
  证明: prod_disjSum _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: prod_disjSum
-/
theorem Fintype.prod_sumElim (f : α₁ -> M) (g : α₂ -> M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disjSum _ _ _

@[to_additive (attr := simp)]
/--
theorem `Fintype.prod_sum_type` / 定理 `Fintype.prod_sum_type`

English:
theorem Fintype.prod_sum_type
  given: (f : α₁ oplus α₂ -> M)
  proof: prod_disjSum _ _ _

中文:
定理 有限类型.prod_sum_type
  条件: (f : α₁ oplus α₂ -> M)
  证明: prod_disjSum _ _ _

Depends on / 依赖: prod_disjSum
-/
theorem Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disjSum _ _ _

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type'`. -/
@[to_additive Fintype.sum_prod_type /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type'`. -/]
/--
theorem `Fintype.prod_prod_type` / 定理 `Fintype.prod_prod_type`

English:
theorem Fintype.prod_prod_type
  given: [CommMonoid γ] (f : α₁ × α₂ -> γ)
  proof: Finset.prod_product ..

中文:
定理 有限类型.prod_prod_type
  条件: [交换幺半群 γ] (f : α₁ × α₂ -> γ)
  证明: Finset.prod_product ..

Depends on / 依赖: Finset, Finset.prod_product, prod_product
-/
theorem Fintype.prod_prod_type [CommMonoid γ] (f : α₁ × α₂ -> γ) :
    ∏ x, f x = ∏ x, ∏ y, f (x, y) :=
  Finset.prod_product ..

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type`. -/
@[to_additive Fintype.sum_prod_type' /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type`. -/]
/--
theorem `Fintype.prod_prod_type'` / 定理 `Fintype.prod_prod_type'`

English:
theorem Fintype.prod_prod_type'
  given: [CommMonoid γ] (f : α₁ -> α₂ -> γ)
  proof: Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]

中文:
定理 有限类型.prod_prod_type'
  条件: [交换幺半群 γ] (f : α₁ -> α₂ -> γ)
  证明: Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]

Depends on / 依赖: Finset, Finset.prod_product, prod_product
-/
theorem Fintype.prod_prod_type' [CommMonoid γ] (f : α₁ -> α₂ -> γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]
/--
theorem `Fintype.prod_prod_type_right` / 定理 `Fintype.prod_prod_type_right`

English:
theorem Fintype.prod_prod_type_right
  given: [CommMonoid γ] (f : α₁ × α₂ -> γ)
  proof: Finset.prod_product_right ..

中文:
定理 有限类型.prod_prod_type_right
  条件: [交换幺半群 γ] (f : α₁ × α₂ -> γ)
  证明: Finset.prod_product_right ..

Depends on / 依赖: Finset, Finset.prod_product_right, prod_product_right
-/
theorem Fintype.prod_prod_type_right [CommMonoid γ] (f : α₁ × α₂ -> γ) :
    ∏ x, f x = ∏ y, ∏ x, f (x, y) :=
  Finset.prod_product_right ..

/-- An uncurried version of `Finset.prod_prod_type_right`. -/
@[to_additive Fintype.sum_prod_type_right'
/-- An uncurried version of `Finset.sum_prod_type_right` -/]
/--
theorem `Fintype.prod_prod_type_right'` / 定理 `Fintype.prod_prod_type_right'`

English:
theorem Fintype.prod_prod_type_right'
  given: [CommMonoid γ] (f : α₁ -> α₂ -> γ)
  proof: Finset.prod_product_right' ..

中文:
定理 有限类型.prod_prod_type_right'
  条件: [交换幺半群 γ] (f : α₁ -> α₂ -> γ)
  证明: Finset.prod_product_right' ..

Depends on / 依赖: Finset, Finset.prod_product_right, prod_product_right
-/
theorem Fintype.prod_prod_type_right' [CommMonoid γ] (f : α₁ -> α₂ -> γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y :=
  Finset.prod_product_right' ..

end
