/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Big operators and `Fin`

Some results about products and sums over the type `Fin`.

The most important results are the induction formulas `Fin.prod_univ_castSucc`
and `Fin.prod_univ_succ`, and the formula `Fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `finFunctionFinEquiv`: An explicit equivalence between `Fin n → Fin m` and `Fin (m ^ n)`.
-/

@[expose] public section

assert_not_exists Field

open Finset

variable {ι M : Type*}

namespace Finset

@[to_additive]
/-
**Finset.prod_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range [CommMonoid M] {n : Nat} (f : Nat -> M) : ∏ i in Finset.range n
, f i = ∏ i : Fin n, f i
参数：f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.prod_univ_eq_prod_range`：Fin.prod_univ_eq_prod_range [CommMonoid α] 
(f : Nat -> α) (n : Nat) : ∏ i : Fin n, f i = ∏ i in range n, f i
-/
theorem prod_range [CommMonoid M] {n : ℕ} (f : ℕ → M) :
    ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i :=
  (Fin.prod_univ_eq_prod_range _ _).symm

end Finset

namespace Fin

section CommMonoid

variable [CommMonoid M] {n : ℕ}

@[to_additive]
/-
**Fin.prod_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_ofFn (f : Fin n -> M) : (List.ofFn f).prod = ∏ i, f i
参数：f : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_ofFn (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]

@[to_additive]
/-
**Fin.prod_univ_def** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_def (f : Fin n -> M) : ∏ i, f i = ((List.finRange n).map f).prod
参数：f : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `Fin.prod_ofFn`：prod_ofFn (f : Fin n -> M) : (List.ofFn f).prod = ∏ i, f 
i
-/
theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

/-- A product of a function `f : Fin 0 → M` is `1` because `Fin 0` is empty -/
@[to_additive /-- A sum of a function `f : Fin 0 → M` is `0` because `Fin 0` is empty -/]
/-
**Fin.prod_univ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_zero (f : Fin 0 -> M) : ∏ i, f i = 1
参数：f : Fin 0 -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of a function `f : Fin 0 → M` is `1` because `Fin 0` is empty
-/
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i, f i = 1 :=
  rfl

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining sum -/]
/-
**Fin.prod_univ_succAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_succAbove (f : Fin (n + 1) -> M) (x : Fin (n + 1)) : ∏ i, f i = 
f x * ∏ i : Fin n, f (x.succAbove i)
参数：f : Fin (n + 1) -> M；x : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_succAbove`：Fin.univ_succAbove (n : Nat) (p : Fin (n + 1)) : (un
iv : Finset (Fin (n + 1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by 
simp)
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.coe_succAboveEmb`：∀ {n : ℕ} (p : Fin (n + 1)), ⇑p.succAboveEmb = p.s
uccAbove
-/
theorem prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove n x, prod_cons, Finset.prod_map, coe_succAboveEmb]

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f 0` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining sum -/]
/-
**Fin.prod_univ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f 0 * ∏ i : Fin n, f i.
succ
参数：f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` times the remaining product -/
@[to_additive /-- A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum -/]
/-
**Fin.prod_univ_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i, f i = (∏ i : Fin n, f (Fi
n.castSucc i)) * f (last n)
参数：f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
-/
theorem prod_univ_castSucc (f : Fin (n + 1) → M) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)

@[to_additive (attr := simp)]
/-
**Fin.prod_univ_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.ofFn_getElem`：∀ {α : Type u_1} {xs : List α}, (List.ofFn fun i => x
s[↑i]) = xs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
/-
**Fin.prod_univ_fun_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_fun_getElem (l : List ι) (f : ι -> M) : ∏ i : Fin l.length, f l[
i.1] = (l.map f).prod
参数：l : List ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.ofFn_getElem_eq_map`：ofFn_getElem_eq_map {β : Type*} (l : List α) (
f : α -> β) : ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_univ_fun_getElem (l : List ι) (f : ι → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
/-
**Fin.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_cons (x : M) (f : Fin n -> M) : (∏ i : Fin n.succ, (cons x f : Fin n.
succ -> M) i) = x * ∏ i : Fin n, f i
参数：x : M；f : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_cons (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → M) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive (attr := simp)]
/-
**Fin.prod_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_snoc (x : M) (f : Fin n -> M) : (∏ i : Fin n.succ, (snoc f x : Fin n.
succ -> M) i) = (∏ i : Fin n, f i) * x
参数：x : M；f : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_snoc (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → M) i) = (∏ i : Fin n, f i) * x := by
  simp [prod_univ_castSucc]

@[to_additive sum_univ_one]
/-
**Fin.prod_univ_one** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_one (f : Fin 1 -> M) : ∏ i, f i = f 0
参数：f : Fin 1 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_univ_one (f : Fin 1 → M) : ∏ i, f i = f 0 := by simp

@[to_additive (attr := simp)]
/-
**Fin.prod_univ_two** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
参数：f : Fin 2 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_univ_two (f : Fin 2 → M) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]

@[to_additive]
/-
**Fin.prod_univ_two'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_two' (f : ι -> M) (a b : ι) : ∏ i, f (![a, b] i) = f a * f b
参数：f : ι -> M；a b : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
-/
theorem prod_univ_two' (f : ι → M) (a b : ι) : ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[to_additive]
/-
**Fin.prod_univ_three** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_three (f : Fin 3 -> M) : ∏ i, f i = f 0 * f 1 * f 2
参数：f : Fin 3 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
-/
theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl

@[to_additive]
/-
**Fin.prod_univ_four** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_four (f : Fin 4 -> M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3
参数：f : Fin 4 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_three`：prod_univ_three (f : Fin 3 -> M) : ∏ i, f i = f 0 *
 f 1 * f 2
-/
theorem prod_univ_four (f : Fin 4 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl

@[to_additive]
/-
**Fin.prod_univ_five** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_five (f : Fin 5 -> M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4
参数：f : Fin 5 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_four`：prod_univ_four (f : Fin 4 -> M) : ∏ i, f i = f 0 * f
 1 * f 2 * f 3
-/
theorem prod_univ_five (f : Fin 5 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl

@[to_additive]
/-
**Fin.prod_univ_six** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_six (f : Fin 6 -> M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * 
f 5
参数：f : Fin 6 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_five`：prod_univ_five (f : Fin 5 -> M) : ∏ i, f i = f 0 * f
 1 * f 2 * f 3 * f 4
-/
theorem prod_univ_six (f : Fin 6 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl

@[to_additive]
/-
**Fin.prod_univ_seven** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_seven (f : Fin 7 -> M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 
* f 5 * f 6
参数：f : Fin 7 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_six`：prod_univ_six (f : Fin 6 -> M) : ∏ i, f i = f 0 * f 1
 * f 2 * f 3 * f 4 * f 5
-/
theorem prod_univ_seven (f : Fin 7 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl

@[to_additive]
/-
**Fin.prod_univ_eight** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_eight (f : Fin 8 -> M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 
* f 5 * f 6 * f 7
参数：f : Fin 8 -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Fin.prod_univ_seven`：prod_univ_seven (f : Fin 7 -> M) : ∏ i, f i = f 0 *
 f 1 * f 2 * f 3 * f 4 * f 5 * f 6
-/
theorem prod_univ_eight (f : Fin 8 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl

@[to_additive]
/-
**Fin.prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_const (n : Nat) (x : M) : ∏ _i : Fin n, x = x ^ n
参数：n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_const (n : ℕ) (x : M) : ∏ _i : Fin n, x = x ^ n := by simp

@[to_additive]
/-
**Fin.prod_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_congr' {a b : Nat} (f : Fin b -> M) (h : a = b) : (∏ i : Fin a, f (i.
cast h)) = ∏ i : Fin b, f i
参数：f : Fin b -> M；h : a = b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_congr' {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (i.cast h)) = ∏ i : Fin b, f i := by
  subst h
  congr

@[to_additive]
/-
**Fin.prod_univ_add** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_univ_add {a b : Nat} (f : Fin (a + b) -> M) : (∏ i : Fin (a + b), f i
) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i)
参数：f : Fin (a + b) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.prod_sum_type`：Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) : ∏ 
x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂)
-/
theorem prod_univ_add {a b : ℕ} (f : Fin (a + b) → M) :
    (∏ i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) := by
  rw [Fintype.prod_equiv finSumFinEquiv.symm f fun i => f (finSumFinEquiv.toFun i)]
  · apply Fintype.prod_sum_type
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

@[to_additive]
/-
**Fin.prod_trunc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_trunc {a b : Nat} (f : Fin (a + b) -> M) (hf : forall j : Fin b, f (n
atAdd a j) = 1) : (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castAdd b i)
参数：f : Fin (a + b) -> M；hf : forall j : Fin b, f (natAdd a j) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_add`：prod_univ_add {a b : Nat} (f : Fin (a + b) -> M) : (∏
 i : Fin (a + b), f i) = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd
 a i)
· 使用定理 `Fintype.prod_eq_one`：prod_eq_one (f : α -> M) (h : forall a, f a = 1) : 
∏ a, f a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_trunc {a b : ℕ} (f : Fin (a + b) → M) (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (castAdd b i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]

@[to_additive]
/-
**Fin.prod_insertNth_go** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_insertNth_go :
    ∀ n i (h : i < n + 1) x (p : Fin n → M), ∏ j, insertNth ⟨i, h⟩ x p j = x * ∏ j, p j
  | n, 0, h, x, p => by simp
  | 0, i, h, x, p => by simp [fin_one_eq_zero ⟨i, h⟩]
  | n + 1, i + 1, h, x, p => by
    obtain ⟨hd, tl, rfl⟩ := exists_cons p
    have i_lt := Nat.lt_of_succ_lt_succ h
    let i_fin : Fin (n + 1) := ⟨i, i_lt⟩
    rw [show ⟨i + 1, h⟩ = i_fin.succ from rfl]
    simp only [insertNth_succ_cons, prod_cons]
    rw [prod_insertNth_go n i i_lt x tl, mul_left_comm]

@[to_additive (attr := simp)]
/-
**Fin.prod_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_insertNth i x (p : Fin n -> M) : ∏ j, insertNth i x p j = x * ∏ j, p 
j
参数：p : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.BigOperators.Fin.0.Fin.prod_insertNth_go`：∀ {M 
: Type u_2} [inst : CommMonoid M] (n i : ℕ) (h : i < n + 1) (x : M) (p : Fin n →
 M),   ∏ j, ⟨i, h⟩.insertNth x p j = x * ∏ j, p j
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem prod_insertNth i x (p : Fin n → M) : ∏ j, insertNth i x p j = x * ∏ j, p j :=
  prod_insertNth_go n i.val i.isLt x p

@[to_additive (attr := simp)]
/-
**Fin.mul_prod_removeNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：mul_prod_removeNth i (f : Fin (n + 1) -> M) : f i * ∏ j, removeNth i f j =
 ∏ j, f j
参数：f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.prod_insertNth`：prod_insertNth i x (p : Fin n -> M) : ∏ j, insertNth
 i x p j = x * ∏ j, p j
· 使用引理 `Fin.insertNth_self_removeNth`：insertNth_self_removeNth (p : Fin (n + 1))
 (f : forall j, α j) : insertNth p (f p) (removeNth p f) = f
-/
theorem mul_prod_removeNth i (f : Fin (n + 1) → M) : f i * ∏ j, removeNth i f j = ∏ j, f j := by
  rw [← prod_insertNth, insertNth_self_removeNth]

/-!
### Products over intervals: `Fin.cast`
-/

section cast

variable {m : ℕ}

@[to_additive]
/-
**Fin.prod_Icc_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Icc_cast (h : n = m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Icc (a.c
ast h) (b.cast h), f i = ∏ i in Icc a b, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Icc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.cast h) (b.cast h), f i = ∏ i ∈ Icc a b, f (i.cast h) := by
  simp [← map_finCongr_Icc]

@[to_additive]
/-
**Fin.prod_Ico_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ico_cast (h : n = m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ico (a.c
ast h) (b.cast h), f i = ∏ i in Ico a b, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.cast h) (b.cast h), f i = ∏ i ∈ Ico a b, f (i.cast h) := by
  simp [← map_finCongr_Ico]

@[to_additive]
/-
**Fin.prod_Ioc_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioc_cast (h : n = m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ioc (a.c
ast h) (b.cast h), f i = ∏ i in Ioc a b, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.cast h) (b.cast h), f i = ∏ i ∈ Ioc a b, f (i.cast h) := by
  simp [← map_finCongr_Ioc]

@[to_additive]
/-
**Fin.prod_Ioo_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioo_cast (h : n = m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ioo (a.c
ast h) (b.cast h), f i = ∏ i in Ioo a b, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioo_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.cast h) (b.cast h), f i = ∏ i ∈ Ioo a b, f (i.cast h) := by
  simp [← map_finCongr_Ioo]

@[to_additive]
/-
**Fin.prod_uIcc_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_uIcc_cast (h : n = m) (f : Fin m -> M) (a b : Fin n) : ∏ i in uIcc (a
.cast h) (b.cast h), f i = ∏ i in uIcc a b, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_uIcc_cast (h : n = m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.cast h) (b.cast h), f i = ∏ i ∈ uIcc a b, f (i.cast h) := by
  simp [← map_finCongr_uIcc]

@[to_additive]
/-
**Fin.prod_Ici_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ici_cast (h : n = m) (f : Fin m -> M) (a : Fin n) : ∏ i >= a.cast h, 
f i = ∏ i >= a, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ici_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≥ a.cast h, f i = ∏ i ≥ a, f (i.cast h) := by
  simp [← map_finCongr_Ici]

@[to_additive]
/-
**Fin.prod_Ioi_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioi_cast (h : n = m) (f : Fin m -> M) (a : Fin n) : ∏ i > a.cast h, f
 i = ∏ i > a, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioi_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i > a.cast h, f i = ∏ i > a, f (i.cast h) := by
  simp [← map_finCongr_Ioi]

@[to_additive]
/-
**Fin.prod_Iic_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iic_cast (h : n = m) (f : Fin m -> M) (a : Fin n) : ∏ i <= a.cast h, 
f i = ∏ i <= a, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iic_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≤ a.cast h, f i = ∏ i ≤ a, f (i.cast h) := by
  simp [← map_finCongr_Iic]

@[to_additive]
/-
**Fin.prod_Iio_cast** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iio_cast (h : n = m) (f : Fin m -> M) (a : Fin n) : ∏ i < a.cast h, f
 i = ∏ i < a, f (i.cast h)
参数：h : n = m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iio_cast (h : n = m) (f : Fin m → M) (a : Fin n) :
    ∏ i < a.cast h, f i = ∏ i < a, f (i.cast h) := by
  simp [← map_finCongr_Iio]

end cast

/-!
### Products over intervals: `Fin.castLE`
-/

section castLE

variable {m : ℕ}

@[to_additive]
/-
**Fin.prod_Icc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Icc_castLE (h : n <= m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Icc (
a.castLE h) (b.castLE h), f i = ∏ i in Icc a b, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Icc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.castLE h) (b.castLE h), f i = ∏ i ∈ Icc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Icc]

@[to_additive]
/-
**Fin.prod_Ico_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ico_castLE (h : n <= m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ico (
a.castLE h) (b.castLE h), f i = ∏ i in Ico a b, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ico a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ico]

@[to_additive]
/-
**Fin.prod_Ioc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioc_castLE (h : n <= m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ioc (
a.castLE h) (b.castLE h), f i = ∏ i in Ioc a b, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ioc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ioc]

@[to_additive]
/-
**Fin.prod_Ioo_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioo_castLE (h : n <= m) (f : Fin m -> M) (a b : Fin n) : ∏ i in Ioo (
a.castLE h) (b.castLE h), f i = ∏ i in Ioo a b, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioo_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.castLE h) (b.castLE h), f i = ∏ i ∈ Ioo a b, f (i.castLE h) := by
  simp [← map_castLEEmb_Ioo]

@[to_additive]
/-
**Fin.prod_uIcc_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_uIcc_castLE (h : n <= m) (f : Fin m -> M) (a b : Fin n) : ∏ i in uIcc
 (a.castLE h) (b.castLE h), f i = ∏ i in uIcc a b, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_uIcc_castLE (h : n ≤ m) (f : Fin m → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.castLE h) (b.castLE h), f i = ∏ i ∈ uIcc a b, f (i.castLE h) := by
  simp [← map_castLEEmb_uIcc]

@[to_additive]
/-
**Fin.prod_Iic_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iic_castLE (h : n <= m) (f : Fin m -> M) (a : Fin n) : ∏ i <= a.castL
E h, f i = ∏ i <= a, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iic_castLE (h : n ≤ m) (f : Fin m → M) (a : Fin n) :
    ∏ i ≤ a.castLE h, f i = ∏ i ≤ a, f (i.castLE h) := by
  simp [← map_castLEEmb_Iic]

@[to_additive]
/-
**Fin.prod_Iio_castLE** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iio_castLE (h : n <= m) (f : Fin m -> M) (a : Fin n) : ∏ i < a.castLE
 h, f i = ∏ i < a, f (i.castLE h)
参数：h : n <= m；f : Fin m -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.castLEEmb_apply`：∀ {n m : ℕ} (h : n ≤ m) (i : Fin n), (Fin.castLEEmb
 h) i = Fin.castLE h i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iio_castLE (h : n ≤ m) (f : Fin m → M) (a : Fin n) :
    ∏ i < a.castLE h, f i = ∏ i < a, f (i.castLE h) := by
  simp [← map_castLEEmb_Iio]

end castLE

/-!
### Products over intervals: `Fin.castAdd`
-/

section castAdd

@[to_additive]
/-
**Fin.prod_Icc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Icc_castAdd (m : Nat) (f : Fin (n + m) -> M) (a b : Fin n) : ∏ i in I
cc (a.castAdd m) (b.castAdd m), f i = ∏ i in Icc a b, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Icc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Icc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Icc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Icc]

@[to_additive]
/-
**Fin.prod_Ico_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ico_castAdd (m : Nat) (f : Fin (n + m) -> M) (a b : Fin n) : ∏ i in I
co (a.castAdd m) (b.castAdd m), f i = ∏ i in Ico a b, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ico (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ico a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ico]

@[to_additive]
/-
**Fin.prod_Ioc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioc_castAdd (m : Nat) (f : Fin (n + m) -> M) (a b : Fin n) : ∏ i in I
oc (a.castAdd m) (b.castAdd m), f i = ∏ i in Ioc a b, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ioc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ioc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ioc]

@[to_additive]
/-
**Fin.prod_Ioo_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioo_castAdd (m : Nat) (f : Fin (n + m) -> M) (a b : Fin n) : ∏ i in I
oo (a.castAdd m) (b.castAdd m), f i = ∏ i in Ioo a b, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioo_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ Ioo (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ Ioo a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_Ioo]

@[to_additive]
/-
**Fin.prod_uIcc_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_uIcc_castAdd (m : Nat) (f : Fin (n + m) -> M) (a b : Fin n) : ∏ i in 
uIcc (a.castAdd m) (b.castAdd m), f i = ∏ i in uIcc a b, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_uIcc_castAdd (m : ℕ) (f : Fin (n + m) → M) (a b : Fin n) :
    ∏ i ∈ uIcc (a.castAdd m) (b.castAdd m), f i = ∏ i ∈ uIcc a b, f (i.castAdd m) := by
  simp [← map_castAddEmb_uIcc]

@[to_additive]
/-
**Fin.prod_Iic_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iic_castAdd (m : Nat) (f : Fin (n + m) -> M) (a : Fin n) : ∏ i <= a.c
astAdd m, f i = ∏ i <= a, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iic_castAdd (m : ℕ) (f : Fin (n + m) → M) (a : Fin n) :
    ∏ i ≤ a.castAdd m, f i = ∏ i ≤ a, f (i.castAdd m) := by
  simp [← map_castAddEmb_Iic]

@[to_additive]
/-
**Fin.prod_Iio_castAdd** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iio_castAdd (m : Nat) (f : Fin (n + m) -> M) (a : Fin n) : ∏ i < a.ca
stAdd m, f i = ∏ i < a, f (i.castAdd m)
参数：m : Nat；f : Fin (n + m) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iio_castAdd (m : ℕ) (f : Fin (n + m) → M) (a : Fin n) :
    ∏ i < a.castAdd m, f i = ∏ i < a, f (i.castAdd m) := by
  simp [← map_castAddEmb_Iio]

end castAdd

/-!
### Products over intervals: `Fin.castSucc`
-/

section castSucc

@[to_additive]
/-
**Fin.prod_Icc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Icc_castSucc (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Icc a.cast
Succ b.castSucc, f i = ∏ i in Icc a b, f i.castSucc
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Icc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Icc a.castSucc b.castSucc, f i = ∏ i ∈ Icc a b, f i.castSucc := by
  simp [← map_castSuccEmb_Icc]

@[to_additive]
/-
**Fin.prod_Ico_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ico_castSucc (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ico a.cast
Succ b.castSucc, f i = ∏ i in Ico a b, f i.castSucc
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ico a.castSucc b.castSucc, f i = ∏ i ∈ Ico a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ico]

@[to_additive]
/-
**Fin.prod_Ioc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioc_castSucc (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ioc a.cast
Succ b.castSucc, f i = ∏ i in Ioc a b, f i.castSucc
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioc a.castSucc b.castSucc, f i = ∏ i ∈ Ioc a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ioc]

@[to_additive]
/-
**Fin.prod_Ioo_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioo_castSucc (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ioo a.cast
Succ b.castSucc, f i = ∏ i in Ioo a b, f i.castSucc
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioo_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioo a.castSucc b.castSucc, f i = ∏ i ∈ Ioo a b, f i.castSucc := by
  simp [← map_castSuccEmb_Ioo]

@[to_additive]
/-
**Fin.prod_uIcc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_uIcc_castSucc (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in uIcc a.ca
stSucc b.castSucc, f i = ∏ i in uIcc a b, f i.castSucc
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_uIcc_castSucc (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ uIcc a.castSucc b.castSucc, f i = ∏ i ∈ uIcc a b, f i.castSucc := by
  simp [← map_castSuccEmb_uIcc]

@[to_additive]
/-
**Fin.prod_Iic_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iic_castSucc (f : Fin (n + 1) -> M) (a : Fin n) : ∏ i <= a.castSucc, 
f i = ∏ i <= a, f i.castSucc
参数：f : Fin (n + 1) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iic_castSucc (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i ≤ a.castSucc, f i = ∏ i ≤ a, f i.castSucc := by
  simp [← map_castSuccEmb_Iic]

@[to_additive]
/-
**Fin.prod_Iio_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Iio_castSucc (f : Fin (n + 1) -> M) (a : Fin n) : ∏ i < a.castSucc, f
 i = ∏ i < a, f i.castSucc
参数：f : Fin (n + 1) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Iio_castSucc (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i < a.castSucc, f i = ∏ i < a, f i.castSucc := by
  simp [← map_castSuccEmb_Iio]

end castSucc

/-!
### Products over intervals: `Fin.succ`
-/

section succ

@[to_additive]
/-
**Fin.prod_Icc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Icc_succ (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Icc a.succ b.s
ucc, f i = ∏ i in Icc a b, f i.succ
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Icc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Icc a.succ b.succ, f i = ∏ i ∈ Icc a b, f i.succ := by
  simp [← map_succEmb_Icc]

@[to_additive]
/-
**Fin.prod_Ico_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ico_succ (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ico a.succ b.s
ucc, f i = ∏ i in Ico a b, f i.succ
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ico_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ico a.succ b.succ, f i = ∏ i ∈ Ico a b, f i.succ := by
  simp [← map_succEmb_Ico]

@[to_additive]
/-
**Fin.prod_Ioc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioc_succ (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ioc a.succ b.s
ucc, f i = ∏ i in Ioc a b, f i.succ
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioc a.succ b.succ, f i = ∏ i ∈ Ioc a b, f i.succ := by
  simp [← map_succEmb_Ioc]

@[to_additive]
/-
**Fin.prod_Ioo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioo_succ (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in Ioo a.succ b.s
ucc, f i = ∏ i in Ioo a b, f i.succ
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioo_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ Ioo a.succ b.succ, f i = ∏ i ∈ Ioo a b, f i.succ := by
  simp [← map_succEmb_Ioo]

@[to_additive]
/-
**Fin.prod_uIcc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_uIcc_succ (f : Fin (n + 1) -> M) (a b : Fin n) : ∏ i in uIcc a.succ b
.succ, f i = ∏ i in uIcc a b, f i.succ
参数：f : Fin (n + 1) -> M；a b : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_uIcc_succ (f : Fin (n + 1) → M) (a b : Fin n) :
    ∏ i ∈ uIcc a.succ b.succ, f i = ∏ i ∈ uIcc a b, f i.succ := by
  simp [← map_succEmb_uIcc]

@[to_additive]
/-
**Fin.prod_Ici_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ici_succ (f : Fin (n + 1) -> M) (a : Fin n) : ∏ i >= a.succ, f i = ∏ 
i >= a, f i.succ
参数：f : Fin (n + 1) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ici_succ (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i ≥ a.succ, f i = ∏ i ≥ a, f i.succ := by
  simp [← map_succEmb_Ici]

@[to_additive (attr := simp)]
/-
**Fin.prod_Ioi_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioi_succ (f : Fin (n + 1) -> M) (a : Fin n) : ∏ i > a.succ, f i = ∏ i
 > a, f i.succ
参数：f : Fin (n + 1) -> M；a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioi_succ (f : Fin (n + 1) → M) (a : Fin n) :
    ∏ i > a.succ, f i = ∏ i > a, f i.succ := by
  simp [← map_succEmb_Ioi]

@[to_additive]
/-
**Fin.prod_Ioi_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_Ioi_zero (f : Fin (n + 1) -> M) : ∏ i > 0, f i = ∏ j : Fin n, f j.suc
c
参数：f : Fin (n + 1) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.Ioi_zero_eq_map`：Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (
Fin.succEmb _)
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_Ioi_zero (f : Fin (n + 1) → M) :
    ∏ i > 0, f i = ∏ j : Fin n, f j.succ := by
  simp [Ioi_zero_eq_map]

end succ

/-- The product of `g i j` over `i j : Fin (n + 1)`, `i ≠ j`,
is equal to the product of `g i j * g j i` over `i < j`.

The additive version of this lemma is useful for some proofs about differential forms.
In this application, the function has the signature `f : Fin (n + 1) → Fin n → M`,
where `f i j` means `g i (Fin.succAbove i j)` in the informal statements.

Similarly, the product of `g i j * g j i` over `i < j`
is written as `f (Fin.castSucc i) j * f (Fin.succ j) i` over `i j : Fin n`, `j ≥ i`.
-/
@[to_additive /-- The sum of `g i j` over `i j : Fin (n + 1)`, `i ≠ j`,
is equal to the sum of `g i j + g j i` over `i < j`.

This lemma is useful for some proofs about differential forms.
In this application, the function has the signature `f : Fin (n + 1) → Fin n → M`,
where `f i j` means `g i (Fin.succAbove i j)` in the informal statements.

Similarly, the sum of `g i j + g j i` over `i < j`
is written as `f (Fin.castSucc i) j + f (Fin.succ j) i` over `i j : Fin n`, `j ≥ i`.
-/]
/-
**Fin.prod_prod_eq_prod_triangle_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：prod_prod_eq_prod_triangle_mul (f : Fin (n + 1) -> Fin n -> M) : ∏ i, ∏ j,
 f i j = ∏ i : Fin n, ∏ j >= i, (f i.castSucc j * f j.succ i)
参数：f : Fin (n + 1) -> Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not 
(s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f
 : ι -> M) : (∏ x in s with …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_le_eq_Ici`：filter_le_eq_Ici [DecidablePred (a <= ·)] : ({x
 | a <= x} : Finset _) = Ici a
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `Finset.filter_ge_eq_Iic`：filter_ge_eq_Iic [DecidablePred (· <= a)] : ({x
 | x <= a} : Finset _) = Iic a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_comm'`：prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : F
inset α} {s' : α -> Finset γ} (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y
 in t')…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
-/
theorem prod_prod_eq_prod_triangle_mul (f : Fin (n + 1) → Fin n → M) :
    ∏ i, ∏ j, f i j = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := calc
  _ = (∏ i, ∏ j with i ≤ j.castSucc, f i j) * ∏ i, ∏ j with j.castSucc < i, f i j := by
    simp only [← Finset.prod_mul_distrib, ← not_le, Finset.prod_filter_mul_prod_filter_not]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≤ i, f i.succ j := by
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
    simp [Finset.filter_le_eq_Ici, Finset.filter_ge_eq_Iic]
  _ = (∏ i, ∏ j ≥ i, f i.castSucc j) * ∏ i, ∏ j ≥ i, f j.succ i := by
    congr 1
    apply Finset.prod_comm'
    simp
  _ = ∏ i : Fin n, ∏ j ≥ i, (f i.castSucc j * f j.succ i) := by
    simp only [Finset.prod_mul_distrib]

end CommMonoid

/-
**Fin.sum_pow_mul_eq_add_pow** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sum_pow_mul_eq_add_pow {n : Nat} {R : Type*} [CommSemiring R] (a b : R) : 
(∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.sum_pow_mul_eq_add_pow`：∀ {R : Type u_4} [inst : CommSemiring R]
 (ι : Type u_5) [inst_1 : Fintype ι] (a b : R),   ∑ s, a ^ s.card * b ^ (Fintype
.card ι - s.card) = …
-/
theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type*} [CommSemiring R] (a b : R) :
    (∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b
/-
**Fin.sum_neg_one_pow** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：sum_neg_one_pow (R : Type*) [Ring R] (m : Nat) : (∑ n : Fin m, (-1) ^ n.1 
: R) = if Even m then 0 else 1
参数：R : Type*；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
-/
lemma sum_neg_one_pow (R : Type*) [Ring R] (m : ℕ) :
    (∑ n : Fin m, (-1) ^ n.1 : R) = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ n IH =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, IH, Fin.val_last, Nat.even_add_one, ite_not]
    split_ifs with h
    · simp [*]
    · simp [(Nat.not_even_iff_odd.mp h).neg_pow]

section PartialProd

variable [Monoid M] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialProd f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive /-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partialSum f` is
`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`. -/]
/-
**Fin.partialProd** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：partialProd (f : Fin n -> M) (i : Fin (n + 1)) : M
参数：f : Fin n -> M；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def partialProd (f : Fin n → M) (i : Fin (n + 1)) : M :=
  ((List.ofFn f).take i).prod

@[to_additive (attr := simp)]
/-
**Fin.partialProd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：partialProd_zero (f : Fin n -> M) : partialProd f 0 = 1
参数：f : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partialProd_zero (f : Fin n → M) : partialProd f 0 = 1 := by simp [partialProd]

@[to_additive]
/-
**Fin.partialProd_succ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：partialProd_succ (f : Fin n -> M) (j : Fin n) : partialProd f j.succ = par
tialProd f (Fin.castSucc j) * f j
参数：f : Fin n -> M；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_add_one`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.take (i +
 1) l = List.take i l ++ l[i]?.toList
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem partialProd_succ (f : Fin n → M) (j : Fin n) :
    partialProd f j.succ = partialProd f (Fin.castSucc j) * f j := by
  simp [partialProd, List.take_add_one]

@[to_additive]
/-
**Fin.partialProd_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：partialProd_succ' (f : Fin (n + 1) -> M) (j : Fin (n + 1)) : partialProd f
 j.succ = f 0 * partialProd (Fin.tail f) j
参数：f : Fin (n + 1) -> M；j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
-/
theorem partialProd_succ' (f : Fin (n + 1) → M) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by
  simp [partialProd]
  rfl

@[to_additive]
/-
**Fin.partialProd_init** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：partialProd_init {f : Fin (n + 1) -> M} (i : Fin (n + 1)) : partialProd (i
nit f) i = partialProd f i.castSucc
参数：n + 1；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.partialProd_zero`：partialProd_zero (f : Fin n -> M) : partialProd f 
0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.partialProd_succ`：partialProd_succ (f : Fin n -> M) (j : Fin n) : pa
rtialProd f j.succ = partialProd f (Fin.castSucc j) * f j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma partialProd_init {f : Fin (n + 1) → M} (i : Fin (n + 1)) :
    partialProd (init f) i = partialProd f i.castSucc :=
  i.inductionOn (by simp) fun i hi => by simp_all [init, partialProd_succ]

@[to_additive]
/-
**Fin.partialProd_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) -> G) : (f 0 •
 partialProd fun i : Fin n => (f i.castSucc)⁻¹ * f i.succ) = f
参数：f : Fin (n + 1) -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.partialProd_zero`：partialProd_zero (f : Fin n -> M) : partialProd f 
0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.partialProd_succ`：partialProd_succ (f : Fin n -> M) (j : Fin n) : pa
rtialProd f j.succ = partialProd f (Fin.castSucc j) * f j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem partialProd_left_inv {G : Type*} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i.castSucc)⁻¹ * f i.succ) = f :=
  funext fun x => Fin.inductionOn x (by simp) fun x hx => by
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [partialProd_succ, ← mul_assoc, hx, mul_inv_cancel_left]

@[to_additive]
/-
**Fin.partialProd_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：partialProd_right_inv {G : Type*} [Group G] (f : Fin n -> G) (i : Fin n) :
 (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i
参数：f : Fin n -> G；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.partialProd_succ`：partialProd_succ (f : Fin n -> M) (j : Fin n) : pa
rtialProd f j.succ = partialProd f (Fin.castSucc j) * f j
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem partialProd_right_inv {G : Type*} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f (Fin.castSucc i))⁻¹ * partialProd f i.succ = f i := by
  rw [partialProd_succ, inv_mul_cancel_left]

@[to_additive]
/-
**Fin.partialProd_contractNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：partialProd_contractNth {G : Type*} [Monoid G] {n : Nat} (g : Fin (n + 1) 
-> G) (a : Fin (n + 1)) : partialProd (contractNth a (· * ·) g) = partialProd g 
∘ a.succ.succAbove
参数：g : Fin (n + 1) -> G；a : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.partialProd_zero`：partialProd_zero (f : Fin n -> M) : partialProd f 
0 = 1
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.succ_succAbove_succ`：∀ {n : ℕ} (i : Fin (n + 1)) (j : Fin n), i.succ
.succAbove j.succ = (i.succAbove j).succ
· 使用定理 `Fin.partialProd_succ`：partialProd_succ (f : Fin n -> M) (j : Fin n) : pa
rtialProd f j.succ = partialProd f (Fin.castSucc j) * f j
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.contractNth_apply_of_lt`：contractNth_apply_of_lt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) < j) : contr
actNth j op g k =…
· 使用定理 `Fin.contractNth_apply_of_eq`：contractNth_apply_of_eq (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) = j) : contr
actNth j op g k =…
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Fin.castSucc_succ`：∀ {n : ℕ} (i : Fin n), i.succ.castSucc = i.castSucc.s
ucc
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Fin.contractNth_apply_of_gt`：contractNth_apply_of_gt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (j : Nat) < k) : contr
actNth j op g k =…
-/
lemma partialProd_contractNth {G : Type*} [Monoid G] {n : ℕ}
    (g : Fin (n + 1) → G) (a : Fin (n + 1)) :
    partialProd (contractNth a (· * ·) g) = partialProd g ∘ a.succ.succAbove := by
  ext i
  refine inductionOn i ?_ ?_
  · simp
  · intro i hi
    simp only [Function.comp_apply, succ_succAbove_succ] at *
    rw [partialProd_succ, partialProd_succ, hi]
    rcases lt_trichotomy (i : ℕ) a with (h | h | h)
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_lt _ _ _ _ h,
        succAbove_of_castSucc_lt] <;>
      simp only [lt_def, val_castSucc, val_succ] <;>
      lia
    · rw [succAbove_of_castSucc_lt, contractNth_apply_of_eq _ _ _ _ h,
        succAbove_of_le_castSucc, castSucc_succ, partialProd_succ, mul_assoc] <;>
      simp only [castSucc_lt_succ_iff, le_def, val_castSucc] <;>
      lia
    · rw [succAbove_of_le_castSucc, succAbove_of_le_castSucc, contractNth_apply_of_gt _ _ _ _ h,
        castSucc_succ] <;>
      simp only [le_def, val_succ, val_castSucc] <;>
      lia

/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive
      /-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
      Then if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.
      If `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.
      If `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`
      Useful for defining group cohomology. -/]
/-
**Fin.inv_partialProd_mul_eq_contractNth** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：inv_partialProd_mul_eq_contractNth {G : Type*} [Group G] (g : Fin (n + 1) 
-> G) (j : Fin (n + 1)) (k : Fin n) : (partialProd g (j.succ.succAbove (Fin.cast
Succ k)))⁻¹ * partialProd g (j.succAbove k).succ = j.contractNth (· * ·) g k
参数：g : Fin (n + 1) -> G；j : Fin (n + 1)；k : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `Fin.castSucc_lt_iff_succ_le`：∀ {n : ℕ} {i : Fin n} {j : Fin (n + 1)}, i.
castSucc < j ↔ i.succ ≤ j
· 使用定理 `Fin.succ_le_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `Fin.le_iff_val_le_val`：le_iff_val_le_val {a b : Fin n} : a <= b ↔ (a : N
at) <= b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.partialProd_right_inv`：partialProd_right_inv {G : Type*} [Group G] (
f : Fin n -> G) (i : Fin n) : (partialProd f (Fin.castSucc i))⁻¹ * partialProd f
 i.succ = f i
· 使用定理 `Fin.contractNth_apply_of_lt`：contractNth_apply_of_lt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) < j) : contr
actNth j op g k =…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.partialProd_succ`：partialProd_succ (f : Fin n -> M) (j : Fin n) : pa
rtialProd f j.succ = partialProd f (Fin.castSucc j) * f j
· 使用定理 `Fin.castSucc_succ`：∀ {n : ℕ} (i : Fin n), i.succ.castSucc = i.castSucc.s
ucc
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Fin.contractNth_apply_of_eq`：contractNth_apply_of_eq (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (k : Nat) = j) : contr
actNth j op g k =…
· 使用定理 `Fin.val_succ`：∀ {n : ℕ} (j : Fin n), ↑j.succ = ↑j + 1
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Fin.contractNth_apply_of_gt`：contractNth_apply_of_gt (j : Fin (n + 1)) (
op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) (h : (j : Nat) < k) : contr
actNth j op g k =…
-/
theorem inv_partialProd_mul_eq_contractNth {G : Type*} [Group G] (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (k : Fin n) :
    (partialProd g (j.succ.succAbove (Fin.castSucc k)))⁻¹ * partialProd g (j.succAbove k).succ =
      j.contractNth (· * ·) g k := by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [succAbove_of_castSucc_lt, succAbove_of_castSucc_lt, partialProd_right_inv,
    contractNth_apply_of_lt]
    · assumption
    · rw [castSucc_lt_iff_succ_le, succ_le_succ_iff, le_iff_val_le_val]
      exact le_of_lt h
  · rwa [succAbove_of_castSucc_lt, succAbove_of_le_castSucc, partialProd_succ,
    castSucc_succ, ← mul_assoc,
      partialProd_right_inv, contractNth_apply_of_eq]
    · simp [le_iff_val_le_val, ← h]
    · rw [castSucc_lt_iff_succ_le, succ_le_succ_iff, le_iff_val_le_val]
      exact le_of_eq h
  · rwa [succAbove_of_le_castSucc, succAbove_of_le_castSucc, partialProd_succ, partialProd_succ,
      castSucc_succ, partialProd_succ, inv_mul_cancel_left, contractNth_apply_of_gt]
    · exact le_iff_val_le_val.2 (le_of_lt h)
    · rw [le_iff_val_le_val, val_succ]
      exact Nat.succ_le_of_lt h

end PartialProd

end Fin

/-- Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`. -/
@[simps!]
/-
**finFunctionFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finFunctionFinEquiv {m n : Nat} : (Fin n -> Fin m) ≃ Fin (m ^ n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Fin n → Fin m` and `Fin (m ^ n)`.
-/
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * m ^ (i : ℕ), by
      induction n with
      | zero => simp
      | succ n ih =>
        cases m
        · exact isEmptyElim (f <| Fin.last _)
        simp_rw [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _
          (Fin.is_le _)).trans_eq ?_
        rw [← one_add_mul (_ : ℕ), add_comm, pow_succ']⟩)
    (fun a b => ⟨a / m ^ (b : ℕ) % m, by
      rcases n with - | n
      · exact b.elim0
      rcases m with - | m
      · rw [zero_pow n.succ_ne_zero] at a
        exact a.elim0
      · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
      dsimp
      induction n with
      | zero => subsingleton [(finCongr <| pow_zero _).subsingleton]
      | succ n ih =>
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
          mul_one, pow_succ', ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
        rw [ih _ (Nat.div_lt_of_lt_mul (a.is_lt.trans_eq (pow_succ' _ _))), Nat.mod_add_div]
/-
**finFunctionFinEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finFunctionFinEquiv_apply {m n : Nat} (f : Fin n -> Fin m) : (finFunctionF
inEquiv f : Nat) = ∑ i : Fin n, ↑(f i) * m ^ (i : Nat)
参数：f : Fin n -> Fin m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl
/-
**finFunctionFinEquiv_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finFunctionFinEquiv_single {m n : Nat} [NeZero m] (i : Fin n) (j : Fin m) 
: (finFunctionFinEquiv (Pi.single i j) : Nat) = j * m ^ (i : Nat)
参数：i : Fin n；j : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finFunctionFinEquiv_apply`：finFunctionFinEquiv_apply {m n : Nat} (f : Fi
n n -> Fin m) : (finFunctionFinEquiv f : Nat) = ∑ i : Fin n, ↑(f i) * m ^ (i : N
at)
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`. -/
/-
**finPiFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finPiFinEquiv {m : Nat} {n : Fin m -> Nat} : (forall i : Fin m, Fin (n i))
 ≃ Fin (∏ i : Fin m, n i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `∀ i : Fin m, Fin (n i)` and `Fin (∏ i : Fin m, n i)`.
-/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction m with
      | zero => simp
      | succ m ih =>
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      suffices
        ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
          ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
            (∏ i : Fin m, n i) * nn by
        solve_by_elim
      intro n nn f fn
      cases nn
      · exact isEmptyElim fn
      refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _ (Fin.is_le _)).trans_eq ?_
      rw [← one_add_mul (_ : ℕ), mul_comm, add_comm]⟩)
    (fun a b => ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b, by
      cases m
      · exact b.elim0
      rcases h : n b with nb | nb
      · rw [prod_eq_zero (Finset.mem_univ _) h] at a
        exact isEmptyElim a
      exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine Fin.consInduction ?_ ?_ n
      · intro a
        have : Subsingleton (Fin (∏ i : Fin 0, i.elim0)) :=
          (finCongr <| prod_empty).subsingleton
        subsingleton
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (finCongr <| Fin.val_succ i)
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]
        clear this
        simp_rw [Fin.val_zero, Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero,
          Fin.prod_univ_succ, Fin.castLE_zero, Fin.cons_zero, ← Nat.div_div_eq_div_mul,
          mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert! Nat.mod_add_div _ _
        exact ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq (Fin.prod_univ_succ _)))
/-
**finPiFinEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finPiFinEquiv_apply {m : Nat} {n : Fin m -> Nat} (f : forall i : Fin m, Fi
n (n i)) : (finPiFinEquiv f : Nat) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j)
参数：f : forall i : Fin m, Fin (n i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) := rfl
/-
**finPiFinEquiv_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finPiFinEquiv_single {m : Nat} {n : Fin m -> Nat} [forall i, NeZero (n i)]
 (i : Fin m) (j : Fin (n i)) : (finPiFinEquiv (Pi.single i j : forall i : Fin m,
 Fin (n i)) : Nat) = j * ∏ j, n (Fin.castLE i.is_lt.le j)
参数：n i；i : Fin m；j : Fin (n i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finPiFinEquiv_apply`：finPiFinEquiv_apply {m : Nat} {n : Fin m -> Nat} (f
 : forall i : Fin m, Fin (n i)) : (finPiFinEquiv f : Nat) = ∑ i, f i * ∏ j, n (F
in.castLE…
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Fin.val_zero`：∀ (n : ℕ) [inst : NeZero n], ↑0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) := by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, zero_mul]

/-- Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin m, n i)`. -/
/-
**finSigmaFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finSigmaFinEquiv {m : Nat} {n : Fin m -> Nat} : (i : Fin m) × Fin (n i) ≃ 
Fin (∑ i : Fin m, n i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the Sigma type `(i : Fin m) × Fin (n i)` and `Fin (∑ i : Fin
 m, n i)`.
-/
def finSigmaFinEquiv {m : ℕ} {n : Fin m → ℕ} : (i : Fin m) × Fin (n i) ≃ Fin (∑ i : Fin m, n i) :=
  match m with
  | 0 => @Equiv.equivOfIsEmpty _ _ _ (by simpa using Fin.isEmpty')
  | Nat.succ m =>
    calc _ ≃ _ := (@finSumFinEquiv m 1).sigmaCongrLeft.symm
      _ ≃ _ := Equiv.sumSigmaDistrib _
      _ ≃ _ := finSigmaFinEquiv.sumCongr (Equiv.uniqueSigma _)
      _ ≃ _ := finSumFinEquiv
      _ ≃ _ := finCongr (Fin.sum_univ_castSucc n).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**finSigmaFinEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSigmaFinEquiv_apply {m : Nat} {n : Fin m -> Nat} (k : (i : Fin m) × Fin
 (n i)) : (finSigmaFinEquiv k : Nat) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) 
+ k.2
参数：k : (i : Fin m) × Fin (n i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSigmaFinEquiv.eq_2`：∀ (m_2 : ℕ) (n_2 : Fin m_2.succ → ℕ),   finSigmaF
inEquiv =     Trans.trans       (Trans.trans         (Trans.trans           (Tra
ns.trans fi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
· 使用定理 `Nat.sub_lt_right_of_lt_add`：∀ {n k m : ℕ}, n ≤ k → k < m + n → k - n < m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.eq_of_lt_succ_of_not_lt`：∀ {m n : ℕ}, m < n + 1 → ¬m < n → m = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
-/
theorem finSigmaFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (k : (i : Fin m) × Fin (n i)) :
    (finSigmaFinEquiv k : ℕ) = ∑ i : Fin k.1, n (Fin.castLE k.1.2.le i) + k.2 := by
  induction m with
  | zero => exact k.fst.elim0
  | succ m ih =>
  rcases k with ⟨⟨iv, hi⟩, j⟩
  rw [finSigmaFinEquiv]
  unfold finSumFinEquiv
  simp only [Equiv.coe_fn_mk, Equiv.sigmaCongrLeft, Equiv.coe_fn_symm_mk, Equiv.trans_def,
    Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  by_cases him : iv < m
  · conv in Sigma.mk _ _ =>
      equals ⟨Sum.inl ⟨iv, him⟩, j⟩ => simp [Fin.addCases, him]
    simpa using! ih _
  · replace him := Nat.eq_of_lt_succ_of_not_lt hi him
    subst him
    conv in Sigma.mk _ _ =>
      equals ⟨Sum.inr 0, j⟩ => simp [Fin.addCases, Fin.natAdd]
    simp
    rfl

/-- `finSigmaFinEquiv` on `Fin 1 × f` is just `f` -/
/-
**finSigmaFinEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finSigmaFinEquiv_one {n : Fin 1 -> Nat} (ij : (i : Fin 1) × Fin (n i)) : (
finSigmaFinEquiv ij : Nat) = ij.2
参数：ij : (i : Fin 1) × Fin (n i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finSigmaFinEquiv_apply`：finSigmaFinEquiv_apply {m : Nat} {n : Fin m -> N
at} (k : (i : Fin m) × Fin (n i)) : (finSigmaFinEquiv k : Nat) = ∑ i : Fin k.1, 
n (Fin.castL…
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finset.sum_of_isEmpty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst
 : AddCommMonoid M] [IsEmpty ι] (s : Finset ι), ∑ i ∈ s, f i = 0
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0

--- 原说明 ---
`finSigmaFinEquiv` on `Fin 1 × f` is just `f`
-/
theorem finSigmaFinEquiv_one {n : Fin 1 → ℕ} (ij : (i : Fin 1) × Fin (n i)) :
    (finSigmaFinEquiv ij : ℕ) = ij.2 := by
  rw [finSigmaFinEquiv_apply, add_eq_right]
  apply @Finset.sum_of_isEmpty _ _ _ _ (by simpa using Fin.isEmpty')

namespace List

section CommMonoid

variable [CommMonoid M]

@[to_additive]
/-
**List.prod_take_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_take_ofFn {n : Nat} (f : Fin n -> M) (i : Nat) : ((ofFn f).take i).pr
od = ∏ j with j.val < i, f j
参数：f : Fin n -> M；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `List.prod_take_succ`：prod_take_succ (L : List M) (i : Nat) (p : i < L.le
ngth) : (L.take (i + 1)).prod = (L.take i).prod * L[i]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem prod_take_ofFn {n : ℕ} (f : Fin n → M) (i : ℕ) :
    ((ofFn f).take i).prod = ∏ j with j.val < i, f j := by
  induction i with
  | zero =>
    simp
  | succ i IH =>
    by_cases h : i < n
    · have : i < length (ofFn f) := by rwa [length_ofFn]
      rw [prod_take_succ _ _ this]
      have A : ({j | j.val < i + 1} : Finset (Fin n)) =
          insert ⟨i, h⟩ ({j | Fin.val j < i} : Finset (Fin n)) := by grind
      grind
    · have A : (ofFn f).take i = (ofFn f).take i.succ := by
        rw [← length_ofFn (f := f)] at h
        have : length (ofFn f) ≤ i := not_lt.mp h
        rw [take_of_length_le this, take_of_length_le (le_trans this (Nat.le_succ _))]
      have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
        intro j
        have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
        simp [this, lt_trans this (Nat.lt_succ_self _)]
      simp [← A, B, IH]

@[to_additive]
/-
**List.prod_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_ofFn {n : Nat} {f : Fin n -> M} : (ofFn f).prod = ∏ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.prod_ofFn`：prod_ofFn (f : Fin n -> M) : (List.ofFn f).prod = ∏ i, f 
i
-/
theorem prod_ofFn {n : ℕ} {f : Fin n → M} : (ofFn f).prod = ∏ i, f i :=
  Fin.prod_ofFn f

end CommMonoid

@[to_additive]
/-
**List.alternatingProd_eq_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：alternatingProd_eq_finsetProd {G : Type*} [DivisionCommMonoid G] : forall 
(L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : Int) ^ (i : N
at) | [] => by rw [alternatingProd]; rw [Finset.prod_eq_one] rintro ⟨i, ⟨⟩⟩ | g:
:[] => by change g = ∏ i : Fin 1, [g][i] ^ (-1 : Int) ^ (i : Nat) rw [Fin.prod_u
niv_succ]; simp | g::h::L => calc g * h⁻¹ * L.alternatingProd = g * h⁻¹ * ∏ i : 
Fin L.length, L[i] ^ (-1 : Int) ^ (i : Nat)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem alternatingProd_eq_finsetProd {G : Type*} [DivisionCommMonoid G] :
    ∀ (L : List G), alternatingProd L = ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternatingProd, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    change g = ∏ i : Fin 1, [g][i] ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc g * h⁻¹ * L.alternatingProd
      = g * h⁻¹ * ∏ i : Fin L.length, L[i] ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternatingProd_eq_finsetProd _)
    _ = ∏ i : Fin (L.length + 2), (g::h::L)[i] ^ (-1 : ℤ) ^ (i : ℕ) := by
        { rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
          simp [pow_add]}

@[deprecated (since := "2026-04-08")]
alias alternatingSum_eq_finset_sum := alternatingSum_eq_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias alternatingProd_eq_finset_prod := alternatingProd_eq_finsetProd

end List

/-- This is a classic "telescoping sum" lemma. It says:
`r₀ - (r₀ + r₁) + (r₁ + r₂) - (r₂+ r₃) + ⋯ ± (rₙ₋₁ + rₙ) ∓ rₙ = 0`.

The chosen spelling, which gives definitional power over `d`, is influenced by downstream
applications such as `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`. -/
/-
**Fin.sum_neg_one_pow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.sum_neg_one_pow_eq_zero {α : Type*} [AddCommGroup α] {n : Nat} (d : Fi
n (n + 2) -> α) (r : Fin (n + 1) -> α) (h_first : d 0 = r 0) (h_mid : forall i :
 Fin n, d i.succ.castSucc = r i.castSucc + r i.succ) (h_last : d (Fin.last _) = 
r (Fin.last _)) : ∑ i, (-1) ^ i.val • d i = 0
参数：d : Fin (n + 2) -> α；r : Fin (n + 1) -> α；h_first : d 0 = r 0；h_mid : forall 
i : Fin n, d i.succ.castSucc = r i.castSucc + r i.succ；h_last : d (Fin.last _) =
 r (Fin.last _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zsmul_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α) (
n : ℤ), n • (a + b) = n • a + n • b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
This is a classic "telescoping sum" lemma. It says:
`r₀ - (r₀ + r₁) + (r₁ + r₂) - (r₂+ r₃) + ⋯ ± (rₙ₋₁ + rₙ) ∓ rₙ = 0`.

The chosen spelling, which gives definitional power over `d`, is influenced by d
ownstream
applications such as `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`.
-/
lemma Fin.sum_neg_one_pow_eq_zero {α : Type*} [AddCommGroup α]
    {n : ℕ} (d : Fin (n + 2) → α) (r : Fin (n + 1) → α)
    (h_first : d 0 = r 0)
    (h_mid : ∀ i : Fin n, d i.succ.castSucc = r i.castSucc + r i.succ)
    (h_last : d (Fin.last _) = r (Fin.last _)) :
    ∑ i, (-1) ^ i.val • d i = 0 := by
  have h₁ : ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • d i =
      d 0 +
      ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • (d (Fin.castSucc i).succ) +
      (-1 : ℤ) ^ (n + 1) • d (Fin.last (n + 1)) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp [add_assoc]
  have h₂ : ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • (r (Fin.castSucc i) + r (Fin.succ i)) =
      ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • r (Fin.castSucc i) +
      ∑ i : Fin n, (-1 : ℤ) ^ (i.val + 1) • r (Fin.succ i) := by
    simp_rw [zsmul_add, Finset.sum_add_distrib]
  have h₃ := Fin.sum_univ_castSucc fun i ↦ (-1 : ℤ) ^ i.val • r i
  simp_all [Fin.sum_univ_succ, pow_succ']
  grind
