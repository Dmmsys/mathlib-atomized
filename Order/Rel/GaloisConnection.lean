/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
module

public import Mathlib.Data.Rel

/-!
# The Galois Connection Induced by a Relation

In this file, we show that an arbitrary relation `R` between a pair of types `α` and `β` defines
a pair `toDual ∘ R.leftDual` and `R.rightDual ∘ ofDual` of adjoint order-preserving maps between the
corresponding posets `Set α` and `(Set β)ᵒᵈ`.
We define `R.leftFixedPoints` (resp. `R.rightFixedPoints`) as the set of fixed points `J`
(resp. `I`) of `Set α` (resp. `Set β`) such that `rightDual (leftDual J) = J`
(resp. `leftDual (rightDual I) = I`).

## Main Results

⋆ `Rel.gc_leftDual_rightDual`: we prove that the maps `toDual ∘ R.leftDual` and
  `R.rightDual ∘ ofDual` form a Galois connection.
⋆ `Rel.equivFixedPoints`: we prove that the maps `R.leftDual` and `R.rightDual` induce inverse
  bijections between the sets of fixed points.

## References

⋆ Engendrement de topologies, démontrabilité et opérations sur les sous-topos, Olivia Caramello and
  Laurent Lafforgue (in preparation)

## Tags

relation, Galois connection, induced bijection, fixed points
-/

@[expose] public section

variable {α β : Type*} (R : SetRel α β)

namespace SetRel

/-! ### Pairs of adjoint maps defined by relations -/

open OrderDual

/-- `leftDual` maps any set `J` of elements of type `α` to the set `{b : β | ∀ a ∈ J, a ~[R] b}` of
elements `b` of type `β` such that `a ~[R] b` for every element `a` of `J`. -/
/-
**SetRel.leftDual** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：leftDual (J : Set α) : Set β
参数：J : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`leftDual` maps any set `J` of elements of type `α` to the set `{b : β | ∀ a ∈ J
, a ~[R] b}` of
elements `b` of type `β` such that `a ~[R] b` for every element `a` of `J`.
-/
def leftDual (J : Set α) : Set β := {b : β | ∀ ⦃a⦄, a ∈ J → a ~[R] b}

/-- `rightDual` maps any set `I` of elements of type `β` to the set `{a : α | ∀ b ∈ I, a ~[R] b}`
of elements `a` of type `α` such that `a ~[R] b` for every element `b` of `I`. -/
/-
**SetRel.rightDual** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：rightDual (I : Set β) : Set α
参数：I : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rightDual` maps any set `I` of elements of type `β` to the set `{a : α | ∀ b ∈ 
I, a ~[R] b}`
of elements `a` of type `α` such that `a ~[R] b` for every element `b` of `I`.
-/
def rightDual (I : Set β) : Set α := {a : α | ∀ ⦃b⦄, b ∈ I → a ~[R] b}

/-- The pair of functions `toDual ∘ leftDual` and `rightDual ∘ ofDual` forms a Galois connection. -/
/-
**SetRel.gc_leftDual_rightDual** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：gc_leftDual_rightDual : GaloisConnection (toDual ∘ R.leftDual) (R.rightDua
l ∘ ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pair of functions `toDual ∘ leftDual` and `rightDual ∘ ofDual` forms a Galoi
s connection.
-/
theorem gc_leftDual_rightDual : GaloisConnection (toDual ∘ R.leftDual) (R.rightDual ∘ ofDual) :=
  fun _ _ ↦ ⟨fun h _ ha _ hb ↦ h (by simpa) ha, fun h _ hb _ ha ↦ h (by simpa) hb⟩

/-! ### Induced equivalences between fixed points -/

/-- `leftFixedPoints` is the set of elements `J : Set α` satisfying `rightDual (leftDual J) = J`. -/
/-
**SetRel.leftFixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：leftFixedPoints
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`leftFixedPoints` is the set of elements `J : Set α` satisfying `rightDual (left
Dual J) = J`.
-/
def leftFixedPoints := {J : Set α | R.rightDual (R.leftDual J) = J}

/-- `rightFixedPoints` is the set of elements `I : Set β` satisfying `leftDual (rightDual I) = I`.
-/
/-
**SetRel.rightFixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：rightFixedPoints
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rightFixedPoints` is the set of elements `I : Set β` satisfying `leftDual (righ
tDual I) = I`.
-/
def rightFixedPoints := {I : Set β | R.leftDual (R.rightDual I) = I}

open GaloisConnection

/-- `leftDual` maps every element `J` to `rightFixedPoints`. -/
/-
**SetRel.leftDual_mem_rightFixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：leftDual_mem_rightFixedPoint (J : Set α) : R.leftDual J in R.rightFixedPoi
nts
参数：J : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `SetRel.gc_leftDual_rightDual`：gc_leftDual_rightDual : GaloisConnection (
toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…

--- 原说明 ---
`leftDual` maps every element `J` to `rightFixedPoints`.
-/
theorem leftDual_mem_rightFixedPoint (J : Set α) : R.leftDual J ∈ R.rightFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_l; exact R.gc_leftDual_rightDual.le_u_l J
  · exact R.gc_leftDual_rightDual.l_u_le (R.leftDual J)

/-- `rightDual` maps every element `I` to `leftFixedPoints`. -/
/-
**SetRel.rightDual_mem_leftFixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：rightDual_mem_leftFixedPoint (I : Set β) : R.rightDual I in R.leftFixedPoi
nts
参数：I : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `SetRel.gc_leftDual_rightDual`：gc_leftDual_rightDual : GaloisConnection (
toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)

--- 原说明 ---
`rightDual` maps every element `I` to `leftFixedPoints`.
-/
theorem rightDual_mem_leftFixedPoint (I : Set β) : R.rightDual I ∈ R.leftFixedPoints := by
  apply le_antisymm
  · apply R.gc_leftDual_rightDual.monotone_u; exact R.gc_leftDual_rightDual.l_u_le I
  · exact R.gc_leftDual_rightDual.le_u_l (R.rightDual I)

/-- The maps `leftDual` and `rightDual` induce inverse bijections between the sets of fixed points.
-/
/-
**SetRel.equivFixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：equivFixedPoints : R.leftFixedPoints ≃ R.rightFixedPoints where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.leftDual_mem_rightFixedPoint`：leftDual_mem_rightFixedPoint (J : S
et α) : R.leftDual J in R.rightFixedPoints
· 使用定理 `SetRel.rightDual_mem_leftFixedPoint`：rightDual_mem_leftFixedPoint (I : S
et β) : R.rightDual I in R.leftFixedPoints

--- 原说明 ---
The maps `leftDual` and `rightDual` induce inverse bijections between the sets o
f fixed points.
-/
def equivFixedPoints : R.leftFixedPoints ≃ R.rightFixedPoints where
  toFun := fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rightFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_leftFixedPoint I⟩
  left_inv J := by obtain ⟨J, hJ⟩ := J; rw [Subtype.mk.injEq, hJ]
  right_inv I := by obtain ⟨I, hI⟩ := I; rw [Subtype.mk.injEq, hI]
/-
**SetRel.rightDual_leftDual_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：rightDual_leftDual_le_of_le {J J' : Set α} (h : J' in R.leftFixedPoints) (
h₁ : J <= J') : R.rightDual (R.leftDual J) <= J'
参数：h : J' in R.leftFixedPoints；h₁ : J <= J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `SetRel.gc_leftDual_rightDual`：gc_leftDual_rightDual : GaloisConnection (
toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
-/
theorem rightDual_leftDual_le_of_le {J J' : Set α} (h : J' ∈ R.leftFixedPoints) (h₁ : J ≤ J') :
    R.rightDual (R.leftDual J) ≤ J' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_u
  apply R.gc_leftDual_rightDual.monotone_l
  exact h₁
/-
**SetRel.leftDual_rightDual_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：leftDual_rightDual_le_of_le {I I' : Set β} (h : I' in R.rightFixedPoints) 
(h₁ : I <= I') : R.leftDual (R.rightDual I) <= I'
参数：h : I' in R.rightFixedPoints；h₁ : I <= I'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `SetRel.gc_leftDual_rightDual`：gc_leftDual_rightDual : GaloisConnection (
toDual ∘ R.leftDual) (R.rightDual ∘ ofDual)
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
-/
theorem leftDual_rightDual_le_of_le {I I' : Set β} (h : I' ∈ R.rightFixedPoints) (h₁ : I ≤ I') :
    R.leftDual (R.rightDual I) ≤ I' := by
  rw [← h]
  apply R.gc_leftDual_rightDual.monotone_l
  apply R.gc_leftDual_rightDual.monotone_u
  exact h₁

end SetRel

