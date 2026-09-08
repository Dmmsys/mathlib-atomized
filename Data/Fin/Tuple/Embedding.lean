/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic

/-! # Constructions of embeddings of `Fin n` into a type

* `Fin.Embedding.cons` : from an embedding `x : Fin n ↪ α` and `a : α` such that
  `a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α` by putting `a` at `0`

* `Fin.Embedding.tail`: the tail of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.snoc` : from an embedding `x : Fin n ↪ α` and `a : α`
  such that `a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α`
  by putting `a` at the end.

* `Fin.Embedding.init`: the init of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.append` : merges two embeddings `Fin m ↪ α` and `Fin n ↪ α`
  into an embedding `Fin (m + n) ↪ α` if they have disjoint ranges

-/

@[expose] public section

open Function.Embedding Fin Set Nat

namespace Fin.Embedding

variable {α : Type*}

/-- Remove the first element from an injective (n + 1)-tuple. -/
/-
**Fin.Embedding.tail** 是 Mathlib 中的一个定义，位于命名空间 `Fin.Embedding`。
形式化陈述：tail {n : Nat} (x : Fin (n + 1) ↪ α) : Fin n ↪ α
参数：x : Fin (n + 1) ↪ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the first element from an injective (n + 1)-tuple.
-/
def tail {n : ℕ} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
  ⟨Fin.tail x, x.injective.comp <| Fin.succ_injective _⟩

@[simp, norm_cast]
/-
**Fin.Embedding.coe_tail** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：coe_tail {n : Nat} (x : Fin (n + 1) ↪ α) : ↑(tail x) = Fin.tail x
参数：x : Fin (n + 1) ↪ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_tail {n : ℕ} (x : Fin (n + 1) ↪ α) : ↑(tail x) = Fin.tail x := rfl

/-- Adding a new element at the beginning of an injective n-tuple, to get an injective n+1-tuple. -/
/-
**Fin.Embedding.cons** 是 Mathlib 中的一个定义，位于命名空间 `Fin.Embedding`。
形式化陈述：cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ 
α
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a new element at the beginning of an injective n-tuple, to get an injecti
ve n+1-tuple.
-/
def cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

@[simp, norm_cast]
/-
**Fin.Embedding.coe_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：coe_cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : ↑(cons x h
a) = Fin.cons a x
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(cons x ha) = Fin.cons a x := rfl
/-
**Fin.Embedding.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：tail_cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : tail (con
s x ha) = x
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    tail (cons x ha) = x := rfl

/-- Remove the last element from an injective (n + 1)-tuple. -/
/-
**Fin.Embedding.init** 是 Mathlib 中的一个定义，位于命名空间 `Fin.Embedding`。
形式化陈述：init {n : Nat} (x : Fin (n + 1) ↪ α) : Fin n ↪ α
参数：x : Fin (n + 1) ↪ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the last element from an injective (n + 1)-tuple.
-/
def init {n : ℕ} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
  ⟨Fin.init x, x.injective.comp <| castSucc_injective _⟩

/-- Adding a new element at the end of an injective n-tuple, to get an injective n+1-tuple. -/
/-
**Fin.Embedding.snoc** 是 Mathlib 中的一个定义，位于命名空间 `Fin.Embedding`。
形式化陈述：snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ 
α
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adding a new element at the end of an injective n-tuple, to get an injective n+1
-tuple.
-/
def snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    Fin (n + 1) ↪ α :=
  ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

@[simp, norm_cast]
/-
**Fin.Embedding.coe_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：coe_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : ↑(snoc x h
a) = Fin.snoc x a
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(snoc x ha) = Fin.snoc x a := rfl
/-
**Fin.Embedding.init_snoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：init_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : init (sno
c x ha) = x
参数：x : Fin n ↪ α；ha : a ∉ range x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Fin.init_snoc`：init_snoc : init (snoc p x) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem init_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    init (snoc x ha) = x := by
  simp [snoc, init]
/-
**Fin.Embedding.snoc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：snoc_castSucc {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} {i : Fi
n n} : snoc x ha i.castSucc = x i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.Embedding.coe_snoc`：coe_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha :
 a ∉ range x) : ↑(snoc x ha) = Fin.snoc x a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
-/
theorem snoc_castSucc {n : ℕ} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} {i : Fin n} :
    snoc x ha i.castSucc = x i := by
  rw [coe_snoc, Fin.snoc_castSucc]
/-
**Fin.Embedding.snoc_last** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：snoc_last {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} : snoc x ha
 (last n) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.Embedding.coe_snoc`：coe_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha :
 a ∉ range x) : ↑(snoc x ha) = Fin.snoc x a
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
-/
theorem snoc_last {n : ℕ} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} :
    snoc x ha (last n) = a := by
  rw [coe_snoc, Fin.snoc_last]

/-- Append a `Fin n ↪ α` at the end of a `Fin m ↪ α` if their ranges are disjoint. -/
/-
**Fin.Embedding.append** 是 Mathlib 中的一个定义，位于命名空间 `Fin.Embedding`。
形式化陈述：append {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x)
 (range y)) : Fin (m + n) ↪ α
参数：h : Disjoint (range x) (range y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a `Fin n ↪ α` at the end of a `Fin m ↪ α` if their ranges are disjoint.
-/
def append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y)) :
    Fin (m + n) ↪ α :=
  ⟨Fin.append x y,
    Fin.append_injective_iff.mpr ⟨x.inj', y.inj', disjoint_range_iff.mp h⟩⟩

@[simp, norm_cast]
/-
**Fin.Embedding.coe_append** 是 Mathlib 中的一个定理，位于命名空间 `Fin.Embedding`。
形式化陈述：coe_append {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (rang
e x) (range y)) : append h = Fin.append x y
参数：h : Disjoint (range x) (range y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y)) :
    append h = Fin.append x y := rfl

end Fin.Embedding

namespace Function.Embedding

variable {α : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- The natural equivalence of `Fin 2 ↪ α` with pairs `(a, b)` of distinct elements of `α`. -/
/-
**Function.Embedding.twoEmbeddingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embed
ding`。
形式化陈述：twoEmbeddingEquiv : (Fin 2 ↪ α) ≃ {(a, b) : α × α | a != b} where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence of `Fin 2 ↪ α` with pairs `(a, b)` of distinct elements 
of `α`.
-/
def twoEmbeddingEquiv : (Fin 2 ↪ α) ≃ {(a, b) : α × α | a ≠ b} where
  toFun e := ⟨(e 0, e 1), by
    simp only [ne_eq, Fin.isValue, mem_ofPred_eq, EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff,
      succ_ne_self, not_false_eq_true]⟩
  invFun := fun ⟨⟨a, b⟩, h⟩ ↦ {
    toFun i := if i = 0 then a else b
    inj' i j hij := by
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · simp [hi, hj]
        · simp only [if_pos hi, eq_one_of_ne_zero j hj,
          if_neg (Ne.symm Fin.zero_ne_one)] at hij
          apply (h hij).elim
      · rw [eq_one_of_ne_zero i hi] at hij ⊢
        by_cases hj : j = 0
        · simp [hj] at hij; exact False.elim (h hij.symm)
        · rw [eq_one_of_ne_zero j hj] }
  left_inv e := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [Fin.eq_one_of_ne_zero i hi]

/-- Two distinct elements of `α` give an embedding `Fin 2 ↪ α`. -/
/-
**Function.Embedding.embFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding`。
形式化陈述：embFinTwo {a b : α} (h : a != b) : Fin 2 ↪ α
参数：h : a != b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two distinct elements of `α` give an embedding `Fin 2 ↪ α`.
-/
def embFinTwo {a b : α} (h : a ≠ b) : Fin 2 ↪ α :=
  twoEmbeddingEquiv.invFun ⟨(a, b), h⟩
/-
**Function.Embedding.embFinTwo_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Em
bedding`。
形式化陈述：embFinTwo_apply_zero {a b : α} (h : a != b) : embFinTwo h 0 = a
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem embFinTwo_apply_zero {a b : α} (h : a ≠ b) :
    embFinTwo h 0 = a := rfl
/-
**Function.Embedding.embFinTwo_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：embFinTwo_apply_one {a b : α} (h : a != b) : embFinTwo h 1 = b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem embFinTwo_apply_one {a b : α} (h : a ≠ b) :
    embFinTwo h 1 = b := rfl

end Function.Embedding

