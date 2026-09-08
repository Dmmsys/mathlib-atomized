/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn,
Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Logic.Basic

/-! # getD and getI

This file provides theorems for working with the `getD` and `getI` functions. These are used to
access an element of a list by numerical index, with a default value as a fallback when the index
is out of range.
-/

@[expose] public section

assert_not_imported Mathlib.Algebra.Order.Group.Nat

namespace List

universe u v

variable {α : Type u} {β : Type v} (l : List α) (x : α) (xs : List α) (n : ℕ)

section getD

variable (d : α)

/-
**List.getD_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.getD n d = l[n]
参数：hn : n < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_eq_getElem {n : ℕ} (hn : n < l.length) : l.getD n d = l[n] := by
  grind
/-
**List.getD_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.getD n d = l[n]
参数：hn : n < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_eq_getElem? (i : Fin l.length) : l.getD i d = l[i]?.get (by simp) := by
  simp only [getD_eq_getElem?_getD, Fin.is_lt, getElem?_pos, Option.getD_some, Fin.getElem_fin,
    Option.get_some]
/-
**List.getD_eq_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_eq_get (i : Fin l.length) : l.getD i d = l.get i
参数：i : Fin l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem getD_eq_get (i : Fin l.length) : l.getD i d = l.get i :=
  getD_eq_getElem ..
/-
**List.getD_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_map {n : Nat} (f : α -> β) : (map f l).getD n (f d) = f (l.getD n d)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
· 使用定理 `Option.getD_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : α) (o 
: Option α), (Option.map f o).getD (f x) = f (o.getD x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getD_map {n : ℕ} (f : α → β) : (map f l).getD n (f d) = f (l.getD n d) := by
  simp only [getD_eq_getElem?_getD, getElem?_map, Option.getD_map]
/-
**List.getD_eq_default** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_eq_default {n : Nat} (hn : l.length <= n) : l.getD n d = d
参数：hn : l.length <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getD n d = d := by
  grind
/-
**List.getD_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_reverse {l : List α} (i) (h : i < length l) : getD l.reverse i = getD
 l (l.length - 1 - i)
参数：i；h : i < length l。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_reverse {l : List α} (i) (h : i < length l) :
    getD l.reverse i = getD l (l.length - 1 - i) := by
  grind

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`. -/
@[instance_reducible]
/-
**List.decidableGetDNilNe** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：decidableGetDNilNe (a : α) : DecidablePred fun i : Nat => getD ([] : List 
α) i a != a
参数：a : α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `DecidableEq α`.
-/
def decidableGetDNilNe (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun _ => isFalse fun H => H getD_nil

@[simp]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_getD_singleton_default_eq (n : ℕ) : [d][n]?.getD d = d := by
  grind

@[simp]
/-
**List.getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.
prod
参数：l : List M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem?_getD_replicate_default_eq (r n : ℕ) : (replicate r d)[n]?.getD d = d := by
  grind
/-
**List.getD_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_replicate {y i n} (h : i < n) : getD (replicate n x) i y = x
参数：h : i < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_replicate {y i n} (h : i < n) : getD (replicate n x) i y = x := by
  grind
/-
**List.getD_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_append (l l' : List α) (d : α) (n : Nat) (h : n < l.length) : (l ++ l
').getD n d = l.getD n d
参数：l l' : List α；d : α；n : Nat；h : n < l.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  grind
/-
**List.getD_append_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_append_right (l l' : List α) (d : α) (n : Nat) (h : l.length <= n) : 
(l ++ l').getD n d = l'.getD (n - l.length) d
参数：l l' : List α；d : α；n : Nat；h : l.length <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  grind
/-
**List.getD_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_surjective_iff {l : List α} {d : α} : (l.getD · d).Surjective ↔ (fora
ll x, x = d ∨ x in l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `List.getD_getElem?`：∀ {α : Type u_1} {l : List α} {i : ℕ} {d : α}, l[i]?
.getD d = if p : i < l.length then l[i] else d
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem getD_surjective_iff {l : List α} {d : α} :
    (l.getD · d).Surjective ↔ (∀ x, x = d ∨ x ∈ l) := by
  apply forall_congr'
  have : ∃ x, l.length ≤ x := ⟨_, Nat.le_refl _⟩
  simp only [getD_eq_getElem?_getD, getD_getElem?, dite_eq_iff, Nat.not_lt, exists_prop, exists_or,
    exists_and_right, this, mem_iff_getElem?, getElem?_eq_some_iff]
  grind
/-
**List.getD_surjective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_surjective {l : List α} (h : forall x, x in l) (d : α) : (l.getD · d)
.Surjective
参数：h : forall x, x in l；d : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.getD_surjective_iff`：getD_surjective_iff {l : List α} {d : α} : (l.
getD · d).Surjective ↔ (forall x, x = d ∨ x in l)
-/
theorem getD_surjective {l : List α} (h : ∀ x, x ∈ l) (d : α) : (l.getD · d).Surjective :=
  getD_surjective_iff.mpr fun _ ↦ .inr <| h _

end getD

section getI

variable [Inhabited α]

@[simp]
/-
**List.getI_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_nil : getI ([] : List α) n = default
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getI_nil : getI ([] : List α) n = default :=
  rfl

@[simp]
/-
**List.getI_cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_cons_zero : getI (x :: xs) 0 = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl

@[simp]
/-
**List.getI_cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl
/-
**List.getI_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_eq_getElem {n : Nat} (hn : n < l.length) : l.getI n = l[n]
参数：hn : n < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
-/
theorem getI_eq_getElem {n : ℕ} (hn : n < l.length) : l.getI n = l[n] :=
  getD_eq_getElem l default hn
/-
**List.getI_eq_default** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_eq_default {n : Nat} (hn : l.length <= n) : l.getI n = default
参数：hn : l.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_default`：getD_eq_default {n : Nat} (hn : l.length <= n) : l
.getD n d = d
-/
theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.getI n = default :=
  getD_eq_default _ _ hn
/-
**List.getD_default_eq_getI** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getD_default_eq_getI {n : Nat} : l.getD n default = l.getI n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getD_default_eq_getI {n : ℕ} : l.getD n default = l.getI n :=
  rfl
/-
**List.getI_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_append (l l' : List α) (n : Nat) (h : n < l.length) : (l ++ l').getI 
n = l.getI n
参数：l l' : List α；n : Nat；h : n < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_append`：getD_append (l l' : List α) (d : α) (n : Nat) (h : n <
 l.length) : (l ++ l').getD n d = l.getD n d
-/
theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getI n = l.getI n := getD_append _ _ _ _ h
/-
**List.getI_append_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_append_right (l l' : List α) (n : Nat) (h : l.length <= n) : (l ++ l'
).getI n = l'.getI (n - l.length)
参数：l l' : List α；n : Nat；h : l.length <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_append_right`：getD_append_right (l l' : List α) (d : α) (n : N
at) (h : l.length <= n) : (l ++ l').getD n d = l'.getD (n - l.length) d
-/
theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getI n = l'.getI (n - l.length) :=
  getD_append_right _ _ _ _ h
/-
**List.getI_eq_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_eq_getElem {n : Nat} (hn : n < l.length) : l.getI n = l[n]
参数：hn : n < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
-/
theorem getI_eq_getElem?_getD (n : ℕ) : l.getI n = (l[n]?).getD default := by
  rw [← getD_default_eq_getI, getD_eq_getElem?_getD]

@[deprecated getI_eq_getElem?_getD (since := "2026-01-05")]
/-
**List.getI_eq_iget_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_eq_iget_getElem? (n : Nat) : l.getI n = l[n]?.getD default
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getI_eq_iget_getElem? (n : ℕ) : l.getI n = l[n]?.getD default :=
  getI_eq_getElem?_getD (l := l) n
/-
**List.getI_zero_eq_headI** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getI_zero_eq_headI : l.getI 0 = l.headI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem getI_zero_eq_headI : l.getI 0 = l.headI := by cases l <;> rfl

end getI

end List

