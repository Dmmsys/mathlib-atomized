/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Nat.Notation

/-!
# Definition of the `Finite` typeclass

This file defines a typeclass `Finite` saying that `α : Sort*` is finite. A type is `Finite` if it
is equivalent to `Fin n` for some `n`. We also define `Infinite α` as a typeclass equivalent to
`¬Finite α`.

The `Finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite.  While the `Finite` class also
represents finiteness of a type, a key difference is that a `Fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `Finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `Fintype` instances.

Every `Fintype` instance automatically gives a `Finite` instance, see `Fintype.finite`, but not vice
versa. Every `Fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `Fintype` instance, one should prefer writing a `Finite` instance
instead.

## Main definitions

* `Finite α` denotes that `α` is a finite type.
* `Infinite α` denotes that `α` is an infinite type.
* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.

## Implementation notes

This file defines both the type-level `Finite` class and the set-level `Set.Finite` definition.

The definition of `Finite α` is not just `Nonempty (Fintype α)` since `Fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `Finite.prop`.

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite, fintype, finite sets
-/

@[expose] public section

assert_not_exists Finset MonoidWithZero IsOrderedRing

universe u v

open Function

variable {α β : Sort*}

/-- A type is `Finite` if it is in bijective correspondence to some `Fin n`.

This is similar to `Fintype`, but `Finite` is a proposition rather than data.
A particular benefit to this is that `Finite` instances are definitionally equal to one another
(due to proof irrelevance) rather than being merely propositionally equal,
and, furthermore, `Finite` instances generally avoid the need for `Decidable` instances.
One other notable difference is that `Finite` allows there to be `Finite p` instances
for all `p : Prop`, which is not allowed by `Fintype` due to universe constraints.
An application of this is that `Finite (x ∈ s → β x)` follows from the general instance for pi
types, assuming `[∀ x, Finite (β x)]`.
Implementation note: this is a reason `Finite α` is not defined as `Nonempty (Fintype α)`.

Every `Fintype` instance provides a `Finite` instance via `Finite.of_fintype`.
Conversely, one can noncomputably create a `Fintype` instance from a `Finite` instance
via `Fintype.ofFinite`. In a proof one might write
```lean
  have := Fintype.ofFinite α
```
to obtain such an instance.

Do not write noncomputable `Fintype` instances; instead write `Finite` instances
and use this `Fintype.ofFinite` interface.
The `Fintype` instances should be relied upon to be computable for evaluation purposes.

Theorems should use `Finite` instead of `Fintype`, unless definitions in the theorem statement
require `Fintype`.
Definitions should prefer `Finite` as well, unless it is important that the definitions
are meant to be computable in the reduction or `#eval` sense.
-/
/-
**inductive** 是 Mathlib 中的一个类，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type is `Finite` if it is in bijective correspondence to some `Fin n`.

This is similar to `Fintype`, but `Finite` is a proposition rather than data.
A particular benefit to this is that `Finite` instances are definitionally equal
 to one another
(due to proof irrelevance) rather than being merely propositionally equal,
and, furthermore, `Finite` instances generally avoid the need for `Decidable` in
stances.
One other notable difference is that `Finite` allows there to be `Finite p` inst
ances
for all `p : Prop`, which is not allowed by `Fintype` due to universe constraint
s.
An application of this is that `Finite (x ∈ s → β x)` follows from the general i
nstance for pi
types, assuming `[∀ x, Finite (β x)]`.
Implementation note: this is a reason `Finite α` is not defined as `Nonempty (Fi
ntype α)`.

Every `Fintype` instance provides a `Finite` instance via `Finite.of_fintype`.
Conversely, one can noncomputably create a `Fintype` instance from a `Finite` in
stance
via `Fintype.ofFinite`. In a proof one might write
```lean
  have := Fintype.ofFinite α
```
to obtain such an instance.

Do not write noncomputable `Fintype` instances; instead write `Finite` instances
and use this `Fintype.ofFinite` interface.
The `Fintype` instances should be relied upon to be computable for evaluation pu
rposes.

Theorems should use `Finite` instead of `Fintype`, unless definitions in the the
orem statement
require `Fintype`.
Definitions should prefer `Finite` as well, unless it is important that the defi
nitions
are meant to be computable in the reduction or `#eval` sense.
-/
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _
/-
**finite_iff_exists_equiv_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ exists n, Nonempty (α
 ≃ Fin n)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩
/-
**Finite.exists_equiv_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : exists n : Nat, Nonem
pty (α ≃ Fin n)
参数：α : Sort*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finite_iff_exists_equiv_fin`：finite_iff_exists_equiv_fin {α : Sort*} : F
inite α ↔ exists n, Nonempty (α ≃ Fin n)
-/
theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h
/-
**Finite.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β
参数：α : Sort*；f : α ≃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β :=
  let ⟨e⟩ := h; ⟨f.symm.trans e⟩
/-
**Equiv.finite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
参数：f : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩
/-
**Function.Bijective.finite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Bijective.finite_iff {f : α -> β} (h : Bijective f) : Finite α ↔ 
Finite β
参数：h : Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
-/
theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff
/-
**Finite.ofBijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.ofBijective [Finite α] {f : α -> β} (h : Bijective f) : Finite β
参数：h : Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Bijective.finite_iff`：Function.Bijective.finite_iff {f : α -> β
} (h : Bijective f) : Finite α ↔ Finite β
-/
theorem Finite.ofBijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›

variable (α) in
/-
**Finite.nonempty_decidableEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.nonempty_decidableEq [Finite α] : Nonempty (DecidableEq α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
-/
theorem Finite.nonempty_decidableEq [Finite α] : Nonempty (DecidableEq α) :=
  let ⟨_n, ⟨e⟩⟩ := Finite.exists_equiv_fin α; ⟨e.decidableEq⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm

/-- A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to
`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`. -/
/-
**Infinite** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u_3 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type is said to be infinite if it is not finite. Note that `Infinite α` is equ
ivalent to
`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`.
-/
class Infinite (α : Sort*) : Prop where
  /-- assertion that `α` is `¬Finite` -/
  not_finite : ¬Finite α

@[simp, push]
/-
**not_finite_iff_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_finite_iff_infinite : ¬Finite α ↔ Infinite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.not_finite`：∀ {α : Sort u_3} [self : Infinite α], ¬Finite α
-/
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩

@[simp, push]
/-
**not_infinite_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_infinite_iff_finite : ¬Infinite α ↔ Finite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
-/
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm
/-
**Equiv.infinite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β
参数：e : α ≃ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
-/
theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
  not_finite_iff_infinite.symm.trans <| e.finite_iff.not.trans not_finite_iff_infinite
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›
/-
**finite_or_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α
参数：α : Sort*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
-/
theorem finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 not_finite_iff_infinite.1

/-- `Infinite α` is not `Finite` -/
/-
**not_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_finite (α : Sort*) [Infinite α] [Finite α] : False
参数：α : Sort*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.not_finite`：∀ {α : Sort u_3} [self : Infinite α], ¬Finite α

--- 原说明 ---
`Infinite α` is not `Finite`
-/
theorem not_finite (α : Sort*) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›
/-
**Finite.false** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：∀ {α : Sort u_1} [Infinite α], Finite α → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
-/
protected theorem Finite.false [Infinite α] (_ : Finite α) : False :=
  not_finite α
/-
**Infinite.false** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：∀ {α : Sort u_1} [Finite α], Infinite α → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.not_finite`：∀ {α : Sort u_3} [self : Infinite α], ¬Finite α
-/
protected theorem Infinite.false [Finite α] (_ : Infinite α) : False :=
  @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite
/-
**Bool.instFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instFinite : Finite Bool
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Bool.instFinite : Finite Bool := .intro finTwoEquiv.symm
/-
**Prop.instFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instFinite : Finite Prop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Prop.instFinite : Finite Prop := .of_equiv _ Equiv.propEquivBool.symm

section Set

/-!
### Finite sets
-/

variable {α : Type u} {β : Type v}

namespace Set

/-- A set is finite if the corresponding `Subtype` is finite,
i.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`. -/
/-
**Set.Finite** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u} → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is finite if the corresponding `Subtype` is finite,
i.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`.
-/
protected def Finite (s : Set α) : Prop := Finite s

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

/-
**Set.finite_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := .rfl

/-- Constructor for `Set.Finite` using a `Finite` instance. -/
/-
**Set.toFinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinite (s : Set α) [Finite s] : s.Finite
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Set.Finite` using a `Finite` instance.
-/
theorem toFinite (s : Set α) [Finite s] : s.Finite := ‹_›

/-- Projection of `Set.Finite` to its `Finite` instance.
This is intended to be used with dot notation.
See also `Set.Finite.Fintype` and `Set.Finite.nonempty_fintype`. -/
/-
**Set.Finite.to_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection of `Set.Finite` to its `Finite` instance.
This is intended to be used with dot notation.
See also `Set.Finite.Fintype` and `Set.Finite.nonempty_fintype`.
-/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s := h

/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `Infinite`. -/
/-
**Set.Infinite** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u} → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is infinite if it is not finite.

This is protected so that it does not conflict with global `Infinite`.
-/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite

@[simp, push]
/-
**Set.not_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_finite {s : Set α} : ¬s.Finite ↔ s.Infinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_finite {s : Set α} : ¬s.Finite ↔ s.Infinite := .rfl

@[simp, push]
/-
**Set.not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not

alias ⟨_, Finite.not_infinite⟩ := not_infinite
/-
**Set.Infinite.not_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → ¬s.Finite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Infinite.not_finite {s : Set α} (hs : s.Infinite) : ¬ s.Finite := hs

attribute [simp] Finite.not_infinite

/-- See also `finite_or_infinite`, `fintypeOrInfinite`. -/
/-
**Set.finite_or_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p

--- 原说明 ---
See also `finite_or_infinite`, `fintypeOrInfinite`.
-/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _
/-
**Set.infinite_or_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
-/
protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _

end Set

/-
**Equiv.set_finite_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.
Finite
参数：hst : s ≃ t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.Finite := by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]

namespace Set

/-! ### Infinite sets -/

variable {s t : Set α}

/-
**Set.infinite_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
-/
theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.not

alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

end Set

end Set

