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

variable {M : Type*} [Zero M] (l : List M) [DecidablePred (getD l · 0 ≠ 0)] (n : ℕ)

/-- Indexing into a `l : List M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. Indices beyond the end of the list are sent to 0.

This is a computable version of the `Finsupp.onFinset` construction.
-/
/-
**List.toFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：toFinsupp : Nat ->₀ M where toFun i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indexing into a `l : List M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. Indices beyond the end of the list are sent to 0
.

This is a computable version of the `Finsupp.onFinset` construction.
-/
def toFinsupp : ℕ →₀ M where
  toFun i := getD l i 0
  support := {i ∈ Finset.range l.length | getD l i 0 ≠ 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _

@[norm_cast]
/-
**List.coe_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：coe_toFinsupp : (l.toFinsupp : Nat -> M) = (l.getD · 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toFinsupp : (l.toFinsupp : ℕ → M) = (l.getD · 0) :=
  rfl

@[simp, norm_cast]
/-
**List.toFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_apply (i : Nat) : (l.toFinsupp : Nat -> M) i = l.getD i 0
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_apply (i : ℕ) : (l.toFinsupp : ℕ → M) i = l.getD i 0 :=
  rfl
/-
**List.toFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_support : l.toFinsupp.support = {i in Finset.range l.length | ge
tD l i 0 != 0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_support :
    l.toFinsupp.support = {i ∈ Finset.range l.length | getD l i 0 ≠ 0} :=
  rfl
/-
**List.toFinsupp_support_subset** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：toFinsupp_support_subset : l.toFinsupp.support subseteq Finset.range l.len
gth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma toFinsupp_support_subset :
    l.toFinsupp.support ⊆ Finset.range l.length := by
  simp [List.toFinsupp_support]
/-
**List.toFinsupp_apply_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l[n]
参数：hn : n < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
-/
theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ hn
/-
**List.toFinsupp_apply_fin** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l[n]
参数：n : Fin l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ n.isLt
/-
**List.toFinsupp_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_apply_le (hn : l.length <= n) : l.toFinsupp n = 0
参数：hn : l.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_default`：getD_eq_default {n : Nat} (hn : l.length <= n) : l
.getD n d = d
-/
theorem toFinsupp_apply_le (hn : l.length ≤ n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn

@[simp]
/-
**List.toFinsupp_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 != 0] : toFin
supp ([] : List M) = 0
参数：[] : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 ≠ 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp
/-
**List.toFinsupp_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 != 0)] : toFinsup
p [x] = Finsupp.single 0 x
参数：x : M；getD [x] · 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
-/
theorem toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 ≠ 0)] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp
/-
**List.toFinsupp_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R) [DecidableP
red (getD (l₁ ++ l₂) · 0 != 0)] [DecidablePred (getD l₁ · 0 != 0)] [DecidablePre
d (getD l₂ · 0 != 0)] : toFinsupp (l₁ ++ l₂) = toFinsupp l₁ + (toFinsupp l₂).emb
Domain (addLeftEmbedding l₁.length)
参数：l₁ l₂ : List R；getD (l₁ ++ l₂) · 0 != 0；getD l₁ · 0 != 0；getD l₂ · 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_append`：getD_append (l l' : List α) (d : α) (n : Nat) (h : n <
 l.length) : (l ++ l').getD n d = l.getD n d
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `List.getD_append_right`：getD_append_right (l l' : List α) (d : α) (n : N
at) (h : l.length <= n) : (l ++ l').getD n d = l'.getD (n - l.length) d
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `List.getD_eq_default`：getD_eq_default {n : Nat} (hn : l.length <= n) : l
.getD n d = d
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
-/
theorem toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
    [DecidablePred (getD (l₁ ++ l₂) · 0 ≠ 0)] [DecidablePred (getD l₁ · 0 ≠ 0)]
    [DecidablePred (getD l₂ · 0 ≠ 0)] :
    toFinsupp (l₁ ++ l₂) =
      toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length) := by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_ge n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h, Finsupp.embDomain_of_notMem_range, add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    lia
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h, Nat.add_sub_cancel_left, getD_eq_default _ _ h, zero_add]
    exact Eq.symm (Finsupp.embDomain_apply_self _ _ _)
/-
**List.toFinsupp_cons_eq_single_add_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_cons_eq_single_add_embDomain {R : Type*} [AddZeroClass R] (x : R
) (xs : List R) [DecidablePred (getD (x::xs) · 0 != 0)] [DecidablePred (getD xs 
· 0 != 0)] : toFinsupp (x::xs) = Finsupp.single 0 x + (toFinsupp xs).embDomain (
addRightEmbedding 1)
参数：x : R；xs : List R；getD (x::xs) · 0 != 0；getD xs · 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `List.toFinsupp_singleton`：toFinsupp_singleton (x : M) [DecidablePred (ge
tD [x] · 0 != 0)] : toFinsupp [x] = Finsupp.single 0 x
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `List.toFinsupp_append`：toFinsupp_append {R : Type*} [AddZeroClass R] (l₁
 l₂ : List R) [DecidablePred (getD (l₁ ++ l₂) · 0 != 0)] [DecidablePred (getD l₁
 · 0 != 0)]…
-/
theorem toFinsupp_cons_eq_single_add_embDomain {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] [DecidablePred (getD xs · 0 ≠ 0)] :
    toFinsupp (x::xs) =
      Finsupp.single 0 x + (toFinsupp xs).embDomain (addRightEmbedding 1) := by
  classical
    convert! toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1
/-
**List.toFinsupp_concat_eq_toFinsupp_add_single** 是 Mathlib 中的一个定理，位于命名空间 `List`
。
形式化陈述：toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x :
 R) (xs : List R) [DecidablePred fun i => getD (xs ++ [x]) i 0 != 0] [DecidableP
red fun i => getD xs i 0 != 0] : toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.
single xs.length x
参数：x : R；xs : List R；xs ++ [x]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toFinsupp_append`：toFinsupp_append {R : Type*} [AddZeroClass R] (l₁
 l₂ : List R) [DecidablePred (getD (l₁ ++ l₂) · 0 != 0)] [DecidablePred (getD l₁
 · 0 != 0)]…
· 使用定理 `List.toFinsupp_singleton`：toFinsupp_singleton (x : M) [DecidablePred (ge
tD [x] · 0 != 0)] : toFinsupp [x] = Finsupp.single 0 x
· 使用定理 `Finsupp.embDomain_single`：embDomain_single (f : α ↪ β) (a : α) (m : M) :
 embDomain f (single a m) = single (f a) m
· 使用定理 `addLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeft
CancelAdd G] (g h : G), (addLeftEmbedding g) h = g + h
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x := by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]
/-
**List.toFinsupp_eq_sum_mapIdx_single** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinsupp_eq_sum_mapIdx_single {R : Type*} [AddMonoid R] (l : List R) [Dec
idablePred (getD l · 0 != 0)] : toFinsupp l = (l.mapIdx fun n r => Finsupp.singl
e n r).sum
参数：l : List R；getD l · 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.toFinsupp_nil`：toFinsupp_nil [DecidablePred fun i => getD ([] : Lis
t M) i 0 != 0] : toFinsupp ([] : List M) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toFinsupp_concat_eq_toFinsupp_add_single`：toFinsupp_concat_eq_toFin
supp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R) [DecidablePre
d fun i => getD (xs ++ [x]) i 0 != …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.mapIdx_concat`：∀ {α : Type u_1} {α_1 : Type u_2} {f : ℕ → α → α_1} 
{l : List α} {e : α},   List.mapIdx f (l ++ [e]) = List.mapIdx f l ++ [f l.lengt
h e]
· 使用定理 `List.sum_append`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 + x2) 0]   [Std.Associative fun x1 x2 => x1 
+ x2]…
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `AddSemigroup.to_isLawfulIdentity`：∀ {M : Type u_4} [inst : AddZeroClass 
M], Std.LawfulIdentity (fun x1 x2 => x1 + x2) 0
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toFinsupp_eq_sum_mapIdx_single {R : Type*} [AddMonoid R] (l : List R)
    [DecidablePred (getD l · 0 ≠ 0)] :
    toFinsupp l = (l.mapIdx fun n r => Finsupp.single n r).sum := by
  /- Porting note: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, sum_append, ih]

end List

