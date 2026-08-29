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
/--
Definition of `FromTypes` / `FromTypes` 的定义

English:
definition FromTypes
  signature: : {n : Nat} -> (Fin n -> Type u) -> Type u -> Type u

中文:
定义 FromTypes
  签名: : {n : 自然数} -> (有限集 n -> 类型u) -> 类型u -> 类型u
-/
def FromTypes : {n : Nat} -> (Fin n -> Type u) -> Type u -> Type u
  | 0 , _, τ => τ
  | n + 1, p, τ => vecHead p -> @FromTypes n (vecTail p) τ

/--
theorem `fromTypes_zero` / 定理 `fromTypes_zero`

English:
theorem fromTypes_zero
  given: (p : Fin 0 -> Type u) (τ : Type u)
  statement: FromTypes p τ = τ
  proof: rfl

中文:
定理 fromTypes_zero
  条件: (p : 有限集 0 -> 类型u) (τ : 类型u)
  结论: FromTypes p τ = τ
  证明: rfl
-/
theorem fromTypes_zero (p : Fin 0 -> Type u) (τ : Type u) : FromTypes p τ = τ := rfl

/--
theorem `fromTypes_nil` / 定理 `fromTypes_nil`

English:
theorem fromTypes_nil
  given: (τ : Type u)
  statement: FromTypes ![] τ = τ
  proof: fromTypes_zero ![] τ

中文:
定理 fromTypes_nil
  条件: (τ : 类型u)
  结论: FromTypes ![] τ = τ
  证明: fromTypes_zero ![] τ

Depends on / 依赖: fromTypes_zero
-/
theorem fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ := fromTypes_zero ![] τ

-- prefer `fromTypes_cons` when it (syntactically) applies
/--
theorem `fromTypes_succ` / 定理 `fromTypes_succ`

English:
theorem fromTypes_succ
  given: {n} (p : Fin (n + 1) -> Type u) (τ : Type u)
  proof: rfl

中文:
定理 fromTypes_succ
  条件: {n} (p : 有限集 (n + 1) -> 类型u) (τ : 类型u)
  证明: rfl
-/
theorem fromTypes_succ {n} (p : Fin (n + 1) -> Type u) (τ : Type u) :
    FromTypes p τ = (vecHead p -> FromTypes (vecTail p) τ) := rfl

/--
theorem `fromTypes_cons` / 定理 `fromTypes_cons`

English:
theorem fromTypes_cons
  given: {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u)
  proof: fromTypes_succ _ τ

中文:
定理 fromTypes_cons
  条件: {n} (α : 类型u) (p : 有限集 n -> 类型u) (τ : 类型u)
  证明: fromTypes_succ _ τ

Depends on / 依赖: fromTypes_succ
-/
theorem fromTypes_cons {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ = (α -> FromTypes p τ) := fromTypes_succ _ τ

/-- The definitional equality between `0`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
/--
Definition of `fromTypes_zero_equiv` / `fromTypes_zero_equiv` 的定义

English:
definition fromTypes_zero_equiv
  signature: (p : Fin 0 -> Type u) (τ : Type u)
  body: Equiv.refl _

中文:
定义 fromTypes_zero_equiv
  签名: (p : 有限集 0 -> 类型u) (τ : 类型u)
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def fromTypes_zero_equiv (p : Fin 0 -> Type u) (τ : Type u) :
    FromTypes p τ ≃ τ := Equiv.refl _

/-- The definitional equality between `![]`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
/--
Definition of `fromTypes_nil_equiv` / `fromTypes_nil_equiv` 的定义

English:
definition fromTypes_nil_equiv
  signature: (τ : Type u)
  body: fromTypes_zero_equiv ![] τ

中文:
定义 fromTypes_nil_equiv
  签名: (τ : 类型u)
  定义体: fromTypes_zero_equiv ![] τ

Depends on / 依赖: fromTypes_zero_equiv
-/
def fromTypes_nil_equiv (τ : Type u) : FromTypes ![] τ ≃ τ :=
  fromTypes_zero_equiv ![] τ

/-- The definitional equality between `p`-ary heterogeneous functions into `τ`
  and function from `vecHead p` to `(vecTail p)`-ary heterogeneous functions into `τ`. -/
@[simps!]
/--
Definition of `fromTypes_succ_equiv` / `fromTypes_succ_equiv` 的定义

English:
definition fromTypes_succ_equiv
  signature: {n} (p : Fin (n + 1) -> Type u) (τ : Type u)
  body: Equiv.refl _

中文:
定义 fromTypes_succ_equiv
  签名: {n} (p : 有限集 (n + 1) -> 类型u) (τ : 类型u)
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def fromTypes_succ_equiv {n} (p : Fin (n + 1) -> Type u) (τ : Type u) :
    FromTypes p τ ≃ (vecHead p -> FromTypes (vecTail p) τ) := Equiv.refl _

/-- The definitional equality between `(vecCons α p)`-ary heterogeneous functions into `τ`
  and function from `α` to `p`-ary heterogeneous functions into `τ`. -/
@[simps!]
/--
Definition of `fromTypes_cons_equiv` / `fromTypes_cons_equiv` 的定义

English:
definition fromTypes_cons_equiv
  signature: {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u)
  body: fromTypes_succ_equiv _ _

中文:
定义 fromTypes_cons_equiv
  签名: {n} (α : 类型u) (p : 有限集 n -> 类型u) (τ : 类型u)
  定义体: fromTypes_succ_equiv _ _

Depends on / 依赖: fromTypes_succ_equiv
-/
def fromTypes_cons_equiv {n} (α : Type u) (p : Fin n -> Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ ≃ (α -> FromTypes p τ) := fromTypes_succ_equiv _ _

namespace FromTypes

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : {n : Nat} -> (p : Fin n -> Type u) -> {τ : Type u} -> (t : τ) -> FromTypes p τ

中文:
定义 const
  签名: : {n : 自然数} -> (p : 有限集 n -> 类型u) -> {τ : 类型u} -> (t : τ) -> FromTypes p τ
-/
def const : {n : Nat} -> (p : Fin n -> Type u) -> {τ : Type u} -> (t : τ) -> FromTypes p τ
  | 0, _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

@[simp]
/--
theorem `const_zero` / 定理 `const_zero`

English:
theorem const_zero
  given: (p : Fin 0 -> Type u) {τ : Type u} (t : τ)
  statement: const p t = t
  proof: rfl

@[simp]

中文:
定理 const_zero
  条件: (p : 有限集 0 -> 类型u) {τ : 类型u} (t : τ)
  结论: const p t = t
  证明: rfl

@[simp]
-/
theorem const_zero (p : Fin 0 -> Type u) {τ : Type u} (t : τ) : const p t = t :=
  rfl

@[simp]
/--
theorem `const_succ` / 定理 `const_succ`

English:
theorem const_succ
  given: {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ)
  proof: rfl

中文:
定理 const_succ
  条件: {n} (p : 有限集 (n + 1) -> 类型u) {τ : 类型u} (t : τ)
  证明: rfl
-/
theorem const_succ {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ) :
    const p t = fun _ => const (vecTail p) t := rfl

/--
theorem `const_succ_apply` / 定理 `const_succ_apply`

English:
theorem const_succ_apply
  statement: {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ)
  proof: rfl

中文:
定理 const_succ_apply
  结论: {n} (p : 有限集 (n + 1) -> 类型u) {τ : 类型u} (t : τ)
  证明: rfl
-/
theorem const_succ_apply {n} (p : Fin (n + 1) -> Type u) {τ : Type u} (t : τ)
    (x : p 0) : const p t x = const (vecTail p) t := rfl

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: {n} {p : Fin n -> Type u} {τ} [Inhabited τ]
  body: ⟨const p default⟩

中文:
实例 inhabited
  签名: {n} {p : 有限集 n -> 类型u} {τ} [可居 τ]
  定义体: ⟨const p default⟩
-/
instance inhabited {n} {p : Fin n -> Type u} {τ} [Inhabited τ] :
    Inhabited (FromTypes p τ) := ⟨const p default⟩

end FromTypes

end Function
