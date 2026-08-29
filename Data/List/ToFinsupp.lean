/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.GetD

/-!

# Lists as finsupp

## Main definitions

- `List.toFinsupp`: Interpret a list as a finitely supported function, where the indexing type is
  `ℕ`, and the values are either the elements of the list (accessing by indexing) or `0` outside of
  the list.

## Main theorems

- `List.toFinsupp_eq_sum_map_enum_single`: A `l : List M` over `M` an `AddMonoid`, when interpreted
  as a finitely supported function, is equal to the sum of `Finsupp.single` produced by mapping over
  `List.enum l`.

## Implementation details

The functions defined here rely on a decidability predicate that each element in the list
can be decidably determined to be not equal to zero or that one can decide one is out of the
bounds of a list. For concretely defined lists that are made up of elements of decidable terms,
this holds. More work will be needed to support lists over non-dec-eq types like `ℝ`, where the
elements are beyond the dec-eq terms of casted values from `ℕ, ℤ, ℚ`.
-/

@[expose] public section

namespace List

variable {M : Type*} [Zero M] (l : List M) [DecidablePred (getD l · 0 != 0)] (n : Nat)

/--
Definition of `toFinsupp` / `toFinsupp` 的定义

English:
definition toFinsupp
  signature: : Nat ->₀ M where
  body: getD l i 0
  support := {i in Finset.range l.length | getD l i 0 != 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _

@[norm_cast]

中文:
定义 toFinsupp
  签名: : 自然数 ->₀ M where
  定义体: getD l i 0
  support := {i in Finset.range l.length | getD l i 0 != 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _

@[norm_cast]
-/
def toFinsupp : Nat ->₀ M where
  toFun i := getD l i 0
  support := {i in Finset.range l.length | getD l i 0 != 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _

@[norm_cast]
/--
theorem `coe_toFinsupp` / 定理 `coe_toFinsupp`

English:
theorem coe_toFinsupp
  statement: (l.toFinsupp : Nat -> M) = (l.getD · 0)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_toFinsupp
  结论: (l.toFinsupp : 自然数 -> M) = (l.getD · 0)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_toFinsupp : (l.toFinsupp : Nat -> M) = (l.getD · 0) :=
  rfl

@[simp, norm_cast]
/--
theorem `toFinsupp_apply` / 定理 `toFinsupp_apply`

English:
theorem toFinsupp_apply
  given: (i : Nat)
  statement: (l.toFinsupp : Nat -> M) i = l.getD i 0
  proof: rfl

中文:
定理 toFinsupp_apply
  条件: (i : 自然数)
  结论: (l.toFinsupp : 自然数 -> M) i = l.getD i 0
  证明: rfl
-/
theorem toFinsupp_apply (i : Nat) : (l.toFinsupp : Nat -> M) i = l.getD i 0 :=
  rfl

/--
theorem `toFinsupp_support` / 定理 `toFinsupp_support`

English:
theorem toFinsupp_support
  proof: rfl

中文:
定理 toFinsupp_support
  证明: rfl
-/
theorem toFinsupp_support :
    l.toFinsupp.support = {i in Finset.range l.length | getD l i 0 != 0} :=
  rfl

/--
lemma `toFinsupp_support_subset` / 引理 `toFinsupp_support_subset`

English:
lemma toFinsupp_support_subset
  proof: by
  simp [List.toFinsupp_support]

中文:
引理 toFinsupp_support_subset
  证明: by
  simp [List.toFinsupp_support]

Depends on / 依赖: List.toFinsupp_support, toFinsupp_support
-/
lemma toFinsupp_support_subset :
    l.toFinsupp.support subseteq Finset.range l.length := by
  simp [List.toFinsupp_support]

/--
theorem `toFinsupp_apply_lt` / 定理 `toFinsupp_apply_lt`

English:
theorem toFinsupp_apply_lt
  given: (hn : n < l.length)
  statement: l.toFinsupp n = l[n]
  proof: getD_eq_getElem _ _ hn

中文:
定理 toFinsupp_apply_lt
  条件: (hn : n < l.length)
  结论: l.toFinsupp n = l[n]
  证明: getD_eq_getElem _ _ hn

Depends on / 依赖: getD_eq_getElem
-/
theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ hn

/--
theorem `toFinsupp_apply_fin` / 定理 `toFinsupp_apply_fin`

English:
theorem toFinsupp_apply_fin
  given: (n : Fin l.length)
  statement: l.toFinsupp n = l[n]
  proof: getD_eq_getElem _ _ n.isLt

中文:
定理 toFinsupp_apply_fin
  条件: (n : 有限集 l.length)
  结论: l.toFinsupp n = l[n]
  证明: getD_eq_getElem _ _ n.isLt

Depends on / 依赖: getD_eq_getElem, n.isLt
-/
theorem toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ n.isLt

/--
theorem `toFinsupp_apply_le` / 定理 `toFinsupp_apply_le`

English:
theorem toFinsupp_apply_le
  given: (hn : l.length <= n)
  statement: l.toFinsupp n = 0
  proof: getD_eq_default _ _ hn

@[simp]

中文:
定理 toFinsupp_apply_le
  条件: (hn : l.length <= n)
  结论: l.toFinsupp n = 0
  证明: getD_eq_default _ _ hn

@[simp]

Depends on / 依赖: getD_eq_default
-/
theorem toFinsupp_apply_le (hn : l.length <= n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn

@[simp]
/--
theorem `toFinsupp_nil` / 定理 `toFinsupp_nil`

English:
theorem toFinsupp_nil
  given: [DecidablePred fun i => getD ([] : List M) i 0 != 0]
  proof: by
  ext
  simp

中文:
定理 toFinsupp_nil
  条件: [DecidablePred fun i => getD ([] : 列表 M) i 0 != 0]
  证明: by
  ext
  simp
-/
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 != 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp

/--
theorem `toFinsupp_singleton` / 定理 `toFinsupp_singleton`

English:
theorem toFinsupp_singleton
  given: (x : M) [DecidablePred (getD [x] · 0 != 0)]
  proof: by
  ext ⟨_ | i⟩ <;> simp

中文:
定理 toFinsupp_singleton
  条件: (x : M) [DecidablePred (getD [x] · 0 != 0)]
  证明: by
  ext ⟨_ | i⟩ <;> simp
-/
theorem toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 != 0)] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp

/--
theorem `toFinsupp_append` / 定理 `toFinsupp_append`

English:
theorem toFinsupp_append
  statement: {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
  proof: by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_ge n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h]; rw [Finsupp.embDomain_of_notMem_range]; rw [add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    lia
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h]; rw [Nat.add_sub_cancel_left]; rw [getD_eq_default _ _ h]; rw [zero_add]
    exact Eq.symm (Finsupp.embDomain_apply_self _ _ _)

中文:
定理 toFinsupp_append
  结论: {R : 类型} [加法零类 R] (l₁ l₂ : 列表 R)
  证明: by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_ge n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h]; rw [Finsupp.embDomain_of_notMem_range]; rw [add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    lia
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h]; rw [Nat.add_sub_cancel_left]; rw [getD_eq_default _ _ h]; rw [zero_add]
    exact Eq.symm (Finsupp.embDomain_apply_self _ _ _)

Depends on / 依赖: Eq.symm, Finsupp, Finsupp.add_apply, Finsupp.embDomain_apply_self, Finsupp.embDomain_of_notMem_range, Nat.add_sub_cancel_left, Nat.exists_eq_add_of_le, add_apply, add_sub_cancel_left, add_zero, embDomain_apply_self, embDomain_of_notMem_range, exists_eq_add_of_le, getD_append, getD_append_right, getD_eq_default, length, lt_or_ge, toFinsupp_apply, zero_add
-/
theorem toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
    [DecidablePred (getD (l₁ ++ l₂) · 0 != 0)] [DecidablePred (getD l₁ · 0 != 0)]
    [DecidablePred (getD l₂ · 0 != 0)] :
    toFinsupp (l₁ ++ l₂) =
      toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length) := by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_ge n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h]; rw [Finsupp.embDomain_of_notMem_range]; rw [add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    lia
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h]; rw [Nat.add_sub_cancel_left]; rw [getD_eq_default _ _ h]; rw [zero_add]
    exact Eq.symm (Finsupp.embDomain_apply_self _ _ _)

/--
theorem `toFinsupp_cons_eq_single_add_embDomain` / 定理 `toFinsupp_cons_eq_single_add_embDomain`

English:
theorem toFinsupp_cons_eq_single_add_embDomain
  statement: {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
  proof: by
  classical
    convert! toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1

中文:
定理 toFinsupp_cons_eq_single_add_embDomain
  结论: {R : 类型} [加法零类 R] (x : R) (xs : 列表 R)
  证明: by
  classical
    convert! toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1

Depends on / 依赖: add_comm, classical, convert, toFinsupp_append, toFinsupp_singleton
-/
theorem toFinsupp_cons_eq_single_add_embDomain {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred (getD (x::xs) · 0 != 0)] [DecidablePred (getD xs · 0 != 0)] :
    toFinsupp (x::xs) =
      Finsupp.single 0 x + (toFinsupp xs).embDomain (addRightEmbedding 1) := by
  classical
    convert! toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1

/--
theorem `toFinsupp_concat_eq_toFinsupp_add_single` / 定理 `toFinsupp_concat_eq_toFinsupp_add_single`

English:
theorem toFinsupp_concat_eq_toFinsupp_add_single
  statement: {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
  proof: by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]

中文:
定理 toFinsupp_concat_eq_toFinsupp_add_single
  结论: {R : 类型} [加法零类 R] (x : R) (xs : 列表 R)
  证明: by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]

Depends on / 依赖: Finsupp, Finsupp.embDomain_single, addLeftEmbedding_apply, add_zero, classical, embDomain_single, toFinsupp_append, toFinsupp_singleton
-/
theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 != 0] [DecidablePred fun i => getD xs i 0 != 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x := by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]


/--
theorem `toFinsupp_eq_sum_mapIdx_single` / 定理 `toFinsupp_eq_sum_mapIdx_single`

English:
theorem toFinsupp_eq_sum_mapIdx_single
  statement: {R : Type*} [AddMonoid R] (l : List R)
  proof: by
  /- Porting note: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, sum_append, ih]

中文:
定理 toFinsupp_eq_sum_mapIdx_single
  结论: {R : 类型} [加法幺半群 R] (l : 列表 R)
  证明: by
  /- Porting note: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, sum_append, ih]
-/
theorem toFinsupp_eq_sum_mapIdx_single {R : Type*} [AddMonoid R] (l : List R)
    [DecidablePred (getD l · 0 != 0)] :
    toFinsupp l = (l.mapIdx fun n r => Finsupp.single n r).sum := by
  /- Porting note: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, sum_append, ih]

end List
