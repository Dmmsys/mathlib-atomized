/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.Data.Fin.VecNotation

/-! # Function types of a given heterogeneous arity

This provides `Function.FromTypes`, such that `FromTypes ![α, β] τ = α → β → τ`.
Note that it is often preferable to use `((i : Fin n) → p i) → τ` in place of `FromTypes p τ`.

## Main definitions

* `Function.FromTypes p τ`: `n`-ary function `p 0 → p 1 → ... → p (n - 1) → β`.
-/

@[expose] public section

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The type of `n`-ary functions `p 0 → p 1 → ... → p (n - 1) → τ`. -/
/-
**Function.FromTypes** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{n : ℕ} → (Fin n → Type u) → Type u → Type u
参数：Fin n → Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `n`-ary functions `p 0 → p 1 → ... → p (n - 1) → τ`.
-/
def FromTypes : {n : ℕ} → (Fin n → Type u) → Type u → Type u
  | 0    , _, τ => τ
  | n + 1, p, τ => vecHead p → @FromTypes n (vecTail p) τ
/-
**Function.fromTypes_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fromTypes_zero (p : Fin 0 -> Type u) (τ : Type u) : FromTypes p τ = τ
参数：p : Fin 0 -> Type u；τ : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromTypes_zero (p : Fin 0 → Type u) (τ : Type u) : FromTypes p τ = τ := rfl
/-
**Function.fromTypes_nil** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ
参数：τ : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.fromTypes_zero`：fromTypes_zero (p : Fin 0 -> Type u) (τ : Type 
u) : FromTypes p τ = τ
-/
theorem fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ := fromTypes_zero ![] τ

-- prefer `fromTypes_cons` when it (syntactically) applies
/-
**Function.fromTypes_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fromTypes_succ {n} (p : Fin (n + 1) -> Type u) (τ : Type u) : FromTypes p 
τ = (vecHead p -> FromTypes (vecTail p) τ)
参数：p : Fin (n + 1) -> Type u；τ : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromTypes_succ {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ = (vecHead p → FromTypes (vecTail p) τ) := rfl
/-
**Function.fromTypes_cons** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：fromTypes_cons {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u) : FromT
ypes (vecCons α p) τ = (α -> FromTypes p τ)
参数：α : Type u；p : Fin n -> Type u；τ : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.fromTypes_succ`：fromTypes_succ {n} (p : Fin (n + 1) -> Type u) 
(τ : Type u) : FromTypes p τ = (vecHead p -> FromTypes (vecTail p) τ)
-/
theorem fromTypes_cons {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ = (α → FromTypes p τ) := fromTypes_succ _ τ

/-- The definitional equality between `0`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
/-
**Function.fromTypes_zero_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：fromTypes_zero_equiv (p : Fin 0 -> Type u) (τ : Type u) : FromTypes p τ ≃ 
τ
参数：p : Fin 0 -> Type u；τ : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The definitional equality between `0`-ary heterogeneous functions into `τ` and `
τ`.
-/
def fromTypes_zero_equiv (p : Fin 0 → Type u) (τ : Type u) :
    FromTypes p τ ≃ τ := Equiv.refl _

/-- The definitional equality between `![]`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
/-
**Function.fromTypes_nil_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：fromTypes_nil_equiv (τ : Type u) : FromTypes ![] τ ≃ τ
参数：τ : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definitional equality between `![]`-ary heterogeneous functions into `τ` and
 `τ`.
-/
def fromTypes_nil_equiv (τ : Type u) : FromTypes ![] τ ≃ τ :=
  fromTypes_zero_equiv ![] τ

/-- The definitional equality between `p`-ary heterogeneous functions into `τ`
  and function from `vecHead p` to `(vecTail p)`-ary heterogeneous functions into `τ`. -/
@[simps!]
/-
**Function.fromTypes_succ_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：fromTypes_succ_equiv {n} (p : Fin (n + 1) -> Type u) (τ : Type u) : FromTy
pes p τ ≃ (vecHead p -> FromTypes (vecTail p) τ)
参数：p : Fin (n + 1) -> Type u；τ : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The definitional equality between `p`-ary heterogeneous functions into `τ`
  and function from `vecHead p` to `(vecTail p)`-ary heterogeneous functions int
o `τ`.
-/
def fromTypes_succ_equiv {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ ≃ (vecHead p → FromTypes (vecTail p) τ) := Equiv.refl _

/-- The definitional equality between `(vecCons α p)`-ary heterogeneous functions into `τ`
  and function from `α` to `p`-ary heterogeneous functions into `τ`. -/
@[simps!]
/-
**Function.fromTypes_cons_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：fromTypes_cons_equiv {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u) :
 FromTypes (vecCons α p) τ ≃ (α -> FromTypes p τ)
参数：α : Type u；p : Fin n -> Type u；τ : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definitional equality between `(vecCons α p)`-ary heterogeneous functions in
to `τ`
  and function from `α` to `p`-ary heterogeneous functions into `τ`.
-/
def fromTypes_cons_equiv {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ ≃ (α → FromTypes p τ) := fromTypes_succ_equiv _ _

namespace FromTypes

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Constant `n`-ary function with value `t`. -/
/-
**Function.FromTypes.const** 是 Mathlib 中的一个定义，位于命名空间 `Function.FromTypes`。
形式化陈述：{n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → τ → Function.FromTypes p τ
参数：p : Fin n → Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant `n`-ary function with value `t`.
-/
def const : {n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → (t : τ) → FromTypes p τ
  | 0,     _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

@[simp]
/-
**Function.FromTypes.const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTypes`。
形式化陈述：const_zero (p : Fin 0 -> Type u) {τ : Type u} (t : τ) : const p t = t
参数：p : Fin 0 -> Type u；t : τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_zero (p : Fin 0 → Type u) {τ : Type u} (t : τ) : const p t = t :=
  rfl

@[simp]
/-
**Function.FromTypes.const_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTypes`。
形式化陈述：const_succ {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ) : const p 
t = fun _ => const (vecTail p) t
参数：p : Fin (n + 1) -> Type u；t : τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_succ {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ) :
    const p t = fun _ => const (vecTail p) t := rfl
/-
**Function.FromTypes.const_succ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTy
pes`。
形式化陈述：const_succ_apply {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ) (x :
 p 0) : const p t x = const (vecTail p) t
参数：p : Fin (n + 1) -> Type u；t : τ；x : p 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem const_succ_apply {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ)
    (x : p 0) : const p t x = const (vecTail p) t := rfl
/-
**Function.FromTypes.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Function.FromTypes`。
形式化陈述：inhabited {n} {p : Fin n -> Type u} {τ} [Inhabited τ] : Inhabited (FromTyp
es p τ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited {n} {p : Fin n → Type u} {τ} [Inhabited τ] :
    Inhabited (FromTypes p τ) := ⟨const p default⟩

end FromTypes

end Function

