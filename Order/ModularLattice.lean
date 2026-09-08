/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Cover
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Modular Lattices

This file defines (semi)modular lattices, a kind of lattice useful in algebra.
For examples, look to the subobject lattices of abelian groups, submodules, and ideals, or consider
any distributive lattice.

## Typeclasses

We define (semi)modularity typeclasses as Prop-valued mixins.

* `IsWeakUpperModularLattice`: Weakly upper modular lattices. Lattice where `a ⊔ b` covers `a`
  and `b` if `a` and `b` both cover `a ⊓ b`.
* `IsWeakLowerModularLattice`: Weakly lower modular lattices. Lattice where `a` and `b` cover
  `a ⊓ b` if `a ⊔ b` covers both `a` and `b`
* `IsUpperModularLattice`: Upper modular lattices. Lattices where `a ⊔ b` covers `a` if `b`
  covers `a ⊓ b`.
* `IsLowerModularLattice`: Lower modular lattices. Lattices where `a` covers `a ⊓ b` if `a ⊔ b`
  covers `b`.
- `IsModularLattice`: Modular lattices. Lattices where `a ≤ c → (a ⊔ b) ⊓ c = a ⊔ (b ⊓ c)`. We
  only require an inequality because the other direction holds in all lattices.

## Main Definitions

- `infIccOrderIsoIccSup` gives an order isomorphism between the intervals
  `[a ⊓ b, a]` and `[b, a ⊔ b]`.
  This corresponds to the diamond (or second) isomorphism theorems of algebra.

## Main Results

- `isModularLattice_iff_inf_sup_inf_assoc`:
  Modularity is equivalent to the `inf_sup_inf_assoc`: `(x ⊓ z) ⊔ (y ⊓ z) = ((x ⊓ z) ⊔ y) ⊓ z`
- `DistribLattice.isModularLattice`: Distributive lattices are modular.

## References

* [Manfred Stern, *Semimodular lattices. Theory and applications*][stern2009]
* [Wikipedia, Modular Lattice](https://en.wikipedia.org/wiki/Modular_lattice)

## TODO

- Relate atoms and coatoms in modular lattices
-/

@[expose] public section


open Set

variable {α : Type*}

/-- A weakly upper modular lattice is a lattice where `a ⊔ b` covers `a` and `b` if `a` and `b` both
cover `a ⊓ b`. -/
/-
**IsWeakUpperModularLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weakly upper modular lattice is a lattice where `a ⊔ b` covers `a` and `b` if 
`a` and `b` both
cover `a ⊓ b`.
-/
class IsWeakUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if `a` and `b` both cover `a ⊓ b`. -/
  covBy_sup_of_inf_covBy_covBy {a b : α} : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b

/-- A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers
both `a` and `b`. -/
@[to_dual existing]
/-
**IsWeakLowerModularLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weakly lower modular lattice is a lattice where `a` and `b` cover `a ⊓ b` if `
a ⊔ b` covers
both `a` and `b`.
-/
class IsWeakLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` cover `a ⊓ b` if `a ⊔ b` covers both `a` and `b` -/
  inf_covBy_of_covBy_covBy_sup {a b : α} : a ⋖ a ⊔ b → b ⋖ a ⊔ b → a ⊓ b ⋖ a

/-- An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` covers `a` and `b`
if either `a` or `b` covers `a ⊓ b`. -/
/-
**IsUpperModularLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upper modular lattice, aka semimodular lattice, is a lattice where `a ⊔ b` co
vers `a` and `b`
if either `a` or `b` covers `a ⊓ b`.
-/
class IsUpperModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a ⊔ b` covers `a` and `b` if either `a` or `b` covers `a ⊓ b` -/
  covBy_sup_of_inf_covBy {a b : α} : a ⊓ b ⋖ a → b ⋖ a ⊔ b

/-- A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers
either `a` or `b`. -/
@[to_dual existing]
/-
**IsLowerModularLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lower modular lattice is a lattice where `a` and `b` both cover `a ⊓ b` if `a 
⊔ b` covers
either `a` or `b`.
-/
class IsLowerModularLattice (α : Type*) [Lattice α] : Prop where
/-- `a` and `b` both cover `a ⊓ b` if `a ⊔ b` covers either `a` or `b` -/
  inf_covBy_of_covBy_sup {a b : α} : a ⋖ a ⊔ b → a ⊓ b ⋖ b

/-- A modular lattice is one with a limited associativity between `⊓` and `⊔`. -/
/-
**IsModularLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modular lattice is one with a limited associativity between `⊓` and `⊔`.
-/
class IsModularLattice (α : Type*) [Lattice α] : Prop where
/-- Whenever `x ≤ z`, then for any `y`, `(x ⊔ y) ⊓ z ≤ x ⊔ (y ⊓ z)` -/
  sup_inf_le_assoc_of_le : ∀ {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z

section WeakUpperModular

variable [Lattice α] [IsWeakUpperModularLattice α] {a b : α}

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_left]
/-
**covBy_sup_of_inf_covBy_of_inf_covBy_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_sup_of_inf_covBy_of_inf_covBy_left : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a
 ⊔ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy`：∀ {α : Type u_2}
 {inst : Lattice α} [self : IsWeakUpperModularLattice α] {a b : α}, a ⊓ b ⋖ a → 
a ⊓ b ⋖ b → a ⋖ a ⊔ b
-/
theorem covBy_sup_of_inf_covBy_of_inf_covBy_left : a ⊓ b ⋖ a → a ⊓ b ⋖ b → a ⋖ a ⊔ b :=
  IsWeakUpperModularLattice.covBy_sup_of_inf_covBy_covBy

@[to_dual inf_covBy_of_covBy_sup_of_covBy_sup_right]
/-
**covBy_sup_of_inf_covBy_of_inf_covBy_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_sup_of_inf_covBy_of_inf_covBy_right : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> b ⋖ 
a ⊔ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `covBy_sup_of_inf_covBy_of_inf_covBy_left`：covBy_sup_of_inf_covBy_of_inf_
covBy_left : a ⊓ b ⋖ a -> a ⊓ b ⋖ b -> a ⋖ a ⊔ b
-/
theorem covBy_sup_of_inf_covBy_of_inf_covBy_right : a ⊓ b ⋖ a → a ⊓ b ⋖ b → b ⋖ a ⊔ b := by
  rw [inf_comm, sup_comm]
  exact fun ha hb => covBy_sup_of_inf_covBy_of_inf_covBy_left hb ha

@[to_dual]
alias CovBy.sup_of_inf_of_inf_left := covBy_sup_of_inf_covBy_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_of_inf_right := covBy_sup_of_inf_covBy_of_inf_covBy_right

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsWeakLowerModularLattice (OrderDual α) :=
  ⟨fun ha hb => (ha.ofDual.sup_of_inf_of_inf_left hb.ofDual).toDual⟩

end WeakUpperModular

section UpperModular

variable [Lattice α] [IsUpperModularLattice α] {a b : α}

@[to_dual inf_covBy_of_covBy_sup_left]
/-
**covBy_sup_of_inf_covBy_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_sup_of_inf_covBy_left : a ⊓ b ⋖ a -> b ⋖ a ⊔ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperModularLattice.covBy_sup_of_inf_covBy`：∀ {α : Type u_2} {inst : L
attice α} [self : IsUpperModularLattice α] {a b : α}, a ⊓ b ⋖ a → b ⋖ a ⊔ b
-/
theorem covBy_sup_of_inf_covBy_left : a ⊓ b ⋖ a → b ⋖ a ⊔ b :=
  IsUpperModularLattice.covBy_sup_of_inf_covBy

@[to_dual inf_covBy_of_covBy_sup_right]
/-
**covBy_sup_of_inf_covBy_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_sup_of_inf_covBy_right : a ⊓ b ⋖ b -> a ⋖ a ⊔ b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `covBy_sup_of_inf_covBy_left`：covBy_sup_of_inf_covBy_left : a ⊓ b ⋖ a -> 
b ⋖ a ⊔ b
-/
theorem covBy_sup_of_inf_covBy_right : a ⊓ b ⋖ b → a ⋖ a ⊔ b := by
  rw [sup_comm, inf_comm]
  exact covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_left := covBy_sup_of_inf_covBy_left

@[to_dual]
alias CovBy.sup_of_inf_right := covBy_sup_of_inf_covBy_right

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsUpperModularLattice.to_isWeakUpperModularLattice :
    IsWeakUpperModularLattice α :=
  ⟨fun _ => CovBy.sup_of_inf_right⟩

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLowerModularLattice (OrderDual α) :=
  ⟨fun h => h.ofDual.sup_of_inf_left.toDual⟩

end UpperModular

section IsModularLattice

variable [Lattice α] [IsModularLattice α]

/-
**sup_inf_le_assoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_le_assoc_of_le {x z : α} (y : α) : x <= z -> (x ⊔ y) ⊓ z <= x ⊔ y 
⊓ z
参数：y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModularLattice.sup_inf_le_assoc_of_le`：∀ {α : Type u_2} {inst : Lattic
e α} [self : IsModularLattice α] {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ 
x ⊔ y ⊓ z
-/
theorem sup_inf_le_assoc_of_le {x z : α} (y : α) : x ≤ z → (x ⊔ y) ⊓ z ≤ x ⊔ y ⊓ z :=
  IsModularLattice.sup_inf_le_assoc_of_le y

@[to_dual existing]
/-
**inf_sup_le_assoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_le_assoc_of_le {x z : α} (y : α) : z <= x -> x ⊓ (y ⊔ z) <= x ⊓ y 
⊔ z
参数：y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_le_assoc_of_le`：sup_inf_le_assoc_of_le {x z : α} (y : α) : x <= 
z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z
-/
theorem inf_sup_le_assoc_of_le {x z : α} (y : α) : z ≤ x → x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ z := by
  simp_rw [inf_comm x, sup_comm _ z]
  exact sup_inf_le_assoc_of_le y

@[to_dual]
/-
**sup_inf_assoc_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x <= z) : (x ⊔ y) ⊓ z = x
 ⊔ y ⊓ z
参数：y : α；h : x <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_inf_le_assoc_of_le`：sup_inf_le_assoc_of_le {x z : α} (y : α) : x <= 
z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x ≤ z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z :=
  le_antisymm (sup_inf_le_assoc_of_le y h)
    (le_inf (sup_le_sup_left inf_le_left _) (sup_le h inf_le_right))

@[to_dual]
/-
**IsModularLattice.inf_sup_inf_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ 
y) ⊓ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_assoc_of_le`：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x 
<= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem IsModularLattice.inf_sup_inf_assoc {x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le y inf_le_right).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModularLattice αᵒᵈ :=
  ⟨fun y z xz =>
    le_of_eq
      (by
        rw [inf_comm, sup_comm, eq_comm, inf_comm, sup_comm]
        exact @sup_inf_assoc_of_le α _ _ _ y _ xz)⟩

variable {x y z : α}

@[to_dual]
/-
**eq_of_le_of_inf_le_of_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_le_of_inf_le_of_le_sup (hxy : x <= y) (hinf : y ⊓ z <= x) (hsup : y 
<= x ⊔ z) : x = y
参数：hxy : x <= y；hinf : y ⊓ z <= x；hsup : y <= x ⊔ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_assoc_of_le`：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x 
<= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem eq_of_le_of_inf_le_of_le_sup (hxy : x ≤ y) (hinf : y ⊓ z ≤ x) (hsup : y ≤ x ⊔ z) :
    x = y := by
  refine hxy.antisymm ?_
  rw [← inf_eq_right, sup_inf_assoc_of_le _ hxy] at hsup
  rwa [← hsup, sup_le_iff, and_iff_right rfl.le, inf_comm]

@[to_dual]
/-
**eq_of_le_of_inf_le_of_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_le_of_inf_le_of_sup_le (hxy : x <= y) (hinf : y ⊓ z <= x ⊓ z) (hsup 
: y ⊔ z <= x ⊔ z) : x = y
参数：hxy : x <= y；hinf : y ⊓ z <= x ⊓ z；hsup : y ⊔ z <= x ⊔ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_inf_le_of_le_sup`：eq_of_le_of_inf_le_of_le_sup (hxy : x <= y
) (hinf : y ⊓ z <= x) (hsup : y <= x ⊔ z) : x = y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem eq_of_le_of_inf_le_of_sup_le (hxy : x ≤ y) (hinf : y ⊓ z ≤ x ⊓ z) (hsup : y ⊔ z ≤ x ⊔ z) :
    x = y :=
  eq_of_le_of_inf_le_of_le_sup hxy (hinf.trans inf_le_left) (le_sup_left.trans hsup)

@[to_dual]
/-
**sup_lt_sup_of_lt_of_inf_le_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_lt_sup_of_lt_of_inf_le_inf (hxy : y < x) (hinf : x ⊓ z <= y ⊓ z) : y ⊔
 z < x ⊔ z
参数：hxy : y < x；hinf : x ⊓ z <= y ⊓ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `eq_of_le_of_inf_le_of_sup_le`：eq_of_le_of_inf_le_of_sup_le (hxy : x <= y
) (hinf : y ⊓ z <= x ⊓ z) (hsup : y ⊔ z <= x ⊔ z) : x = y
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sup_lt_sup_of_lt_of_inf_le_inf (hxy : y < x) (hinf : x ⊓ z ≤ y ⊓ z) : y ⊔ z < x ⊔ z :=
  lt_of_le_of_ne (sup_le_sup_right (le_of_lt hxy) _) fun hsup =>
    ne_of_lt hxy <| eq_of_le_of_inf_le_of_sup_le (le_of_lt hxy) hinf (le_of_eq hsup.symm)
/-
**strictMono_inf_prod_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_inf_prod_sup : StrictMono fun x => (x ⊓ z, x ⊔ z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `sup_lt_sup_of_lt_of_inf_le_inf`：sup_lt_sup_of_lt_of_inf_le_inf (hxy : y 
< x) (hinf : x ⊓ z <= y ⊓ z) : y ⊔ z < x ⊔ z
-/
theorem strictMono_inf_prod_sup : StrictMono fun x ↦ (x ⊓ z, x ⊔ z) := fun _x _y hxy ↦
  ⟨⟨inf_le_inf_right _ hxy.le, sup_le_sup_right hxy.le _⟩,
    fun ⟨inf_le, sup_le⟩ ↦ (sup_lt_sup_of_lt_of_inf_le_inf hxy inf_le).not_ge sup_le⟩

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian. -/
/-
**wellFounded_lt_exact_sequence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_lt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ] [h₁ 
: WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : α) (f₁ : β -> α) (f₂ : α -> β) (g
₁ : γ -> α) (g₂ : α -> γ) (gci : GaloisCoinsertion f₁ f₂) (gi : GaloisInsertion 
g₂ g₁) (hf : forall a, f₁ (f₂ a) = a ⊓ K) (hg : forall a, g₁ (g₂ a) = a ⊔ K) : W
ellFoundedLT α
参数：K : α；f₁ : β -> α；f₂ : α -> β；g₁ : γ -> α；g₂ : α -> γ；gci : GaloisCoinsertion
 f₁ f₂；gi : GaloisInsertion g₂ g₁；hf : forall a, f₁ (f₂ a) = a ⊓ K；hg : forall a
, g₁ (g₂ a) = a ⊔ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.wellFoundedLT`：StrictMono.wellFoundedLT [WellFoundedLT β] (hf
 : StrictMono f) : WellFoundedLT α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
· 使用定理 `strictMono_inf_prod_sup`：strictMono_inf_prod_sup : StrictMono fun x => (
x ⊓ z, x ⊔ z)

--- 原说明 ---
A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Artinian, then `M` is Artinian.
-/
theorem wellFounded_lt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [h₁ : WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedLT α :=
  StrictMono.wellFoundedLT (f := fun A ↦ (f₂ A, g₂ A)) fun A B hAB ↦ by
    simp only [Prod.le_def, lt_iff_le_not_ge, ← gci.l_le_l_iff, ← gi.u_le_u_iff, hf, hg]
    exact strictMono_inf_prod_sup hAB

/-- A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian. -/
/-
**wellFounded_gt_exact_sequence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_gt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ] [Wel
lFoundedGT β] [WellFoundedGT γ] (K : α) (f₁ : β -> α) (f₂ : α -> β) (g₁ : γ -> α
) (g₂ : α -> γ) (gci : GaloisCoinsertion f₁ f₂) (gi : GaloisInsertion g₂ g₁) (hf
 : forall a, f₁ (f₂ a) = a ⊓ K) (hg : forall a, g₁ (g₂ a) = a ⊔ K) : WellFounded
GT α
参数：K : α；f₁ : β -> α；f₂ : α -> β；g₁ : γ -> α；g₂ : α -> γ；gci : GaloisCoinsertion
 f₁ f₂；gi : GaloisInsertion g₂ g₁；hf : forall a, f₁ (f₂ a) = a ⊓ K；hg : forall a
, g₁ (g₂ a) = a ⊔ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wellFounded_lt_exact_sequence`：wellFounded_lt_exact_sequence {β γ : Type
*} [Preorder β] [Preorder γ] [h₁ : WellFoundedLT β] [h₂ : WellFoundedLT γ] (K : 
α) (f₁ : β -> α) (f…
· 使用定理 `instIsModularLatticeOrderDual`：∀ {α : Type u_1} [inst : Lattice α] [IsMo
dularLattice α], IsModularLattice αᵒᵈ
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ

--- 原说明 ---
A generalization of the theorem that if `N` is a submodule of `M` and
  `N` and `M / N` are both Noetherian, then `M` is Noetherian.
-/
theorem wellFounded_gt_exact_sequence {β γ : Type*} [Preorder β] [Preorder γ]
    [WellFoundedGT β] [WellFoundedGT γ] (K : α)
    (f₁ : β → α) (f₂ : α → β) (g₁ : γ → α) (g₂ : α → γ) (gci : GaloisCoinsertion f₁ f₂)
    (gi : GaloisInsertion g₂ g₁) (hf : ∀ a, f₁ (f₂ a) = a ⊓ K) (hg : ∀ a, g₁ (g₂ a) = a ⊔ K) :
    WellFoundedGT α :=
  wellFounded_lt_exact_sequence (α := αᵒᵈ) (β := γᵒᵈ) (γ := βᵒᵈ)
    K g₁ g₂ f₁ f₂ gi.dual gci.dual hg hf

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the closed intervals `[a ⊓ b, a]` and `[b, a ⊔ b]` -/
@[simps]
/-
**infIccOrderIsoIccSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：infIccOrderIsoIccSup (a b : α) : Icc (a ⊓ b) a ≃o Icc b (a ⊔ b) where toFu
n x
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diamond isomorphism between the closed intervals `[a ⊓ b, a]` and `[b, a ⊔ b
]`
-/
def infIccOrderIsoIccSup (a b : α) : Icc (a ⊓ b) a ≃o Icc b (a ⊔ b) where
  toFun x := ⟨x ⊔ b, ⟨le_sup_right, sup_le_sup_right x.prop.2 b⟩⟩
  invFun x := ⟨a ⊓ x, ⟨inf_le_inf_left a x.prop.1, inf_le_left⟩⟩
  left_inv x :=
    Subtype.ext
      (by
        change a ⊓ (↑x ⊔ b) = ↑x
        rw [sup_comm, ← inf_sup_assoc_of_le _ x.prop.2, sup_eq_right.2 x.prop.1])
  right_inv x :=
    Subtype.ext
      (by
        change a ⊓ ↑x ⊔ b = ↑x
        rw [inf_comm, inf_sup_assoc_of_le _ x.prop.1, inf_eq_left.2 x.prop.2])
  map_rel_iff' {x y} := by
    simp only [Subtype.mk_le_mk, Equiv.coe_fn_mk]
    rw [← Subtype.coe_le_coe]
    refine ⟨fun h => ?_, fun h => sup_le_sup_right h _⟩
    rw [← sup_eq_right.2 x.prop.1, inf_sup_assoc_of_le _ x.prop.2, sup_comm, ←
      sup_eq_right.2 y.prop.1, inf_sup_assoc_of_le _ y.prop.2, sup_comm b]
    exact inf_le_inf_left _ h

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the closed intervals `[a ⊓ b, b]` and `[a, a ⊔ b]` -/
@[simps!]
/-
**infIccOrderIsoIccSup'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：infIccOrderIsoIccSup' (a b : α) : Icc (a ⊓ b) b ≃o Icc a (a ⊔ b)
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diamond isomorphism between the closed intervals `[a ⊓ b, b]` and `[a, a ⊔ b
]`
-/
def infIccOrderIsoIccSup' (a b : α) : Icc (a ⊓ b) b ≃o Icc a (a ⊔ b) :=
  (OrderIso.setCongr _ _ (by rw [inf_comm])).trans <| (infIccOrderIsoIccSup b a).trans <|
    OrderIso.setCongr _ _ (by rw [sup_comm])
/-
**inf_strictMonoOn_Icc_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b 
(a ⊔ b))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.of_domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Preor
der α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMono (s.domRestric
t f) → StrictMo…
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem inf_strictMonoOn_Icc_sup {a b : α} : StrictMonoOn (fun c => a ⊓ c) (Icc b (a ⊔ b)) :=
  StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).symm.strictMono
/-
**sup_strictMonoOn_Icc_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a
 ⊓ b) a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.of_domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Preor
der α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMono (s.domRestric
t f) → StrictMo…
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem sup_strictMonoOn_Icc_inf {a b : α} : StrictMonoOn (fun c => c ⊔ b) (Icc (a ⊓ b) a) :=
  StrictMono.of_domRestrict (infIccOrderIsoIccSup a b).strictMono

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the open intervals `(a ⊓ b, a)` and `(b, a ⊔ b)`. -/
@[simps]
/-
**infIooOrderIsoIooSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：infIooOrderIsoIooSup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b) where toFu
n c
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diamond isomorphism between the open intervals `(a ⊓ b, a)` and `(b, a ⊔ b)`
.
-/
def infIooOrderIsoIooSup (a b : α) : Ioo (a ⊓ b) a ≃o Ioo b (a ⊔ b) where
  toFun c :=
    ⟨c ⊔ b,
      le_sup_right.trans_lt <|
        sup_strictMonoOn_Icc_inf (left_mem_Icc.2 inf_le_left) (Ioo_subset_Icc_self c.2) c.2.1,
      sup_strictMonoOn_Icc_inf (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 inf_le_left) c.2.2⟩
  invFun c :=
    ⟨a ⊓ c,
      inf_strictMonoOn_Icc_sup (left_mem_Icc.2 le_sup_right) (Ioo_subset_Icc_self c.2) c.2.1,
      inf_le_left.trans_lt' <|
        inf_strictMonoOn_Icc_sup (Ioo_subset_Icc_self c.2) (right_mem_Icc.2 le_sup_right) c.2.2⟩
  left_inv c :=
    Subtype.ext <| by
      dsimp
      rw [sup_comm, ← inf_sup_assoc_of_le _ c.prop.2.le, sup_eq_right.2 c.prop.1.le]
  right_inv c :=
    Subtype.ext <| by
      dsimp
      rw [inf_comm, inf_sup_assoc_of_le _ c.prop.1.le, inf_eq_left.2 c.prop.2.le]
  map_rel_iff' := @fun c d =>
    @OrderIso.le_iff_le _ _ _ _ (infIccOrderIsoIccSup _ _) ⟨c.1, Ioo_subset_Icc_self c.2⟩
      ⟨d.1, Ioo_subset_Icc_self d.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The diamond isomorphism between the open intervals `(a ⊓ b, b)` and `(a, a ⊔ b)`. -/
@[simps!]
/-
**infIooOrderIsoIooSup'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：infIooOrderIsoIooSup' (a b : α) : Ioo (a ⊓ b) b ≃o Ioo a (a ⊔ b)
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diamond isomorphism between the open intervals `(a ⊓ b, b)` and `(a, a ⊔ b)`
.
-/
def infIooOrderIsoIooSup' (a b : α) : Ioo (a ⊓ b) b ≃o Ioo a (a ⊔ b) :=
  (OrderIso.setCongr _ _ (by rw [inf_comm])).trans <| (infIooOrderIsoIooSup b a).trans <|
    OrderIso.setCongr _ _ (by rw [sup_comm])

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsModularLattice.to_isLowerModularLattice : IsLowerModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, sup_comm a, inf_comm a, ← isEmpty_coe_sort, right_lt_sup,
      inf_lt_left, (infIooOrderIsoIooSup b a).symm.toEquiv.isEmpty_congr]
    exact id⟩

-- See note [lower instance priority]
@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsModularLattice.to_isUpperModularLattice : IsUpperModularLattice α :=
  ⟨fun {a b} => by
    simp_rw [covBy_iff_Ioo_eq, ← isEmpty_coe_sort, right_lt_sup, inf_lt_left,
      (infIooOrderIsoIooSup a b).toEquiv.isEmpty_congr]
    exact id⟩

end IsModularLattice

namespace IsCompl

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

/-- The diamond isomorphism between the intervals `Set.Iic a` and `Set.Ici b`. -/
/-
**IsCompl.IicOrderIsoIci** 是 Mathlib 中的一个定义，位于命名空间 `IsCompl`。
形式化陈述：IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b
参数：h : IsCompl a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diamond isomorphism between the intervals `Set.Iic a` and `Set.Ici b`.
-/
def IicOrderIsoIci {a b : α} (h : IsCompl a b) : Set.Iic a ≃o Set.Ici b :=
  (OrderIso.setCongr (Set.Iic a) (Set.Icc (a ⊓ b) a)
        (h.inf_eq_bot.symm ▸ Set.Icc_bot.symm)).trans <|
    (infIccOrderIsoIccSup a b).trans
      (OrderIso.setCongr (Set.Icc b (a ⊔ b)) (Set.Ici b) (h.sup_eq_top.symm ▸ Set.Icc_top))

end IsCompl

/-
**le_iff_eq_of_codisjoint_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_eq_of_codisjoint_of_disjoint [Lattice α] [BoundedOrder α] [IsModula
rLattice α] {a b c : α} (h₀ : Codisjoint a b) (h₁ : Disjoint b c) : a <= c ↔ a =
 c
参数：h₀ : Codisjoint a b；h₁ : Disjoint b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `sup_inf_le_assoc_of_le`：sup_inf_le_assoc_of_le {x z : α} (y : α) : x <= 
z -> (x ⊔ y) ⊓ z <= x ⊔ y ⊓ z
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma le_iff_eq_of_codisjoint_of_disjoint [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {a b c : α} (h₀ : Codisjoint a b) (h₁ : Disjoint b c) :
    a ≤ c ↔ a = c :=
  ⟨fun h₂ ↦ le_antisymm h₂ <| by simpa [h₀.eq_top, h₁.eq_bot] using sup_inf_le_assoc_of_le b h₂,
   le_of_eq⟩
/-
**isModularLattice_iff_inf_sup_inf_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isModularLattice_iff_inf_sup_inf_assoc [Lattice α] : IsModularLattice α ↔ 
forall x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModularLattice.inf_sup_inf_assoc`：IsModularLattice.inf_sup_inf_assoc {
x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem isModularLattice_iff_inf_sup_inf_assoc [Lattice α] :
    IsModularLattice α ↔ ∀ x y z : α, x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z :=
  ⟨fun h => @IsModularLattice.inf_sup_inf_assoc _ _ h, fun h =>
    ⟨fun y z xz => by rw [← inf_eq_left.2 xz, h]⟩⟩

namespace DistribLattice

/-
**DistribLattice.** 是 Mathlib 中的一个实例，位于命名空间 `DistribLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [DistribLattice α] : IsModularLattice α :=
  ⟨fun y z xz => by rw [inf_sup_right, inf_eq_left.2 xz]⟩

end DistribLattice

namespace Disjoint

variable {a b c : α}

@[to_dual]
/-
**Disjoint.disjoint_sup_right_of_disjoint_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Di
sjoint`。
形式化陈述：disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α] [IsModula
rLattice α] (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) : Disjoint a (b ⊔ c)
参数：h : Disjoint a b；hsup : Disjoint (a ⊔ b) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `IsModularLattice.sup_inf_sup_assoc`：∀ {α : Type u_1} [inst : Lattice α] 
[IsModularLattice α] {x y z : α}, (x ⊔ z) ⊓ (y ⊔ z) = (x ⊔ z) ⊓ y ⊔ z
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem disjoint_sup_right_of_disjoint_sup_left [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint a b) (hsup : Disjoint (a ⊔ b) c) :
    Disjoint a (b ⊔ c) := by
  rw [disjoint_iff_inf_le, ← h.eq_bot, sup_comm]
  apply le_inf inf_le_left
  apply (inf_le_inf_right (c ⊔ b) le_sup_right).trans
  rw [sup_comm, IsModularLattice.sup_inf_sup_assoc, hsup.eq_bot, bot_sup_eq]

@[to_dual]
/-
**Disjoint.disjoint_sup_left_of_disjoint_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Di
sjoint`。
形式化陈述：disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α] [IsModula
rLattice α] (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) : Disjoint (a ⊔ b) c
参数：h : Disjoint b c；hsup : Disjoint a (b ⊔ c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Disjoint.disjoint_sup_right_of_disjoint_sup_left`：disjoint_sup_right_of_
disjoint_sup_left [Lattice α] [OrderBot α] [IsModularLattice α] (h : Disjoint a 
b) (hsup : Disjoint (a ⊔ b) c) : Disjo…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem disjoint_sup_left_of_disjoint_sup_right [Lattice α] [OrderBot α]
    [IsModularLattice α] (h : Disjoint b c) (hsup : Disjoint a (b ⊔ c)) :
    Disjoint (a ⊔ b) c := by
  rw [disjoint_comm, sup_comm]
  apply Disjoint.disjoint_sup_right_of_disjoint_sup_left h.symm
  rwa [sup_comm, disjoint_comm] at hsup

@[to_dual]
/-
**Disjoint._root_.disjoint_sup_right_of_disjoint_sup_right** 是 Mathlib 中的一个引理，位于
命名空间 `Disjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.disjoint_sup_right_of_disjoint_sup_right [Lattice α] [OrderBot α] [IsModularLattice α]
    (h₁ : Disjoint a (b ⊔ c)) (h₂ : Disjoint b (c ⊔ a)) :
    Disjoint c (a ⊔ b) := by
  rw [sup_comm] at h₂ ⊢
  rw [disjoint_comm]
  exact (h₁.mono_right le_sup_right).disjoint_sup_left_of_disjoint_sup_right h₂

@[to_dual]
/-
**Disjoint.isCompl_sup_right_of_isCompl_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Disj
oint`。
形式化陈述：isCompl_sup_right_of_isCompl_sup_left [Lattice α] [BoundedOrder α] [IsModu
larLattice α] (h : Disjoint a b) (hcomp : IsCompl (a ⊔ b) c) : IsCompl a (b ⊔ c)
参数：h : Disjoint a b；hcomp : IsCompl (a ⊔ b) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.disjoint_sup_right_of_disjoint_sup_left`：disjoint_sup_right_of_
disjoint_sup_left [Lattice α] [OrderBot α] [IsModularLattice α] (h : Disjoint a 
b) (hsup : Disjoint (a ⊔ b) c) : Disjo…
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `codisjoint_assoc`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : O
rderTop α] {a b c : α},   Codisjoint (a ⊔ b) c ↔ Codisjoint a (b ⊔ c)
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem isCompl_sup_right_of_isCompl_sup_left [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint a b) (hcomp : IsCompl (a ⊔ b) c) :
    IsCompl a (b ⊔ c) :=
  ⟨h.disjoint_sup_right_of_disjoint_sup_left hcomp.disjoint, codisjoint_assoc.mp hcomp.codisjoint⟩

@[to_dual]
/-
**Disjoint.isCompl_sup_left_of_isCompl_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Disj
oint`。
形式化陈述：isCompl_sup_left_of_isCompl_sup_right [Lattice α] [BoundedOrder α] [IsModu
larLattice α] (h : Disjoint b c) (hcomp : IsCompl a (b ⊔ c)) : IsCompl (a ⊔ b) c
参数：h : Disjoint b c；hcomp : IsCompl a (b ⊔ c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.disjoint_sup_left_of_disjoint_sup_right`：disjoint_sup_left_of_d
isjoint_sup_right [Lattice α] [OrderBot α] [IsModularLattice α] (h : Disjoint b 
c) (hsup : Disjoint a (b ⊔ c)) : Disjo…
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_assoc`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : O
rderTop α] {a b c : α},   Codisjoint (a ⊔ b) c ↔ Codisjoint a (b ⊔ c)
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem isCompl_sup_left_of_isCompl_sup_right [Lattice α] [BoundedOrder α] [IsModularLattice α]
    (h : Disjoint b c) (hcomp : IsCompl a (b ⊔ c)) :
    IsCompl (a ⊔ b) c :=
  ⟨h.disjoint_sup_left_of_disjoint_sup_right hcomp.disjoint, codisjoint_assoc.mpr hcomp.codisjoint⟩

end Disjoint

/-
**Set.Iic.isCompl_inf_inf_of_isCompl_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Iic.isCompl_inf_inf_of_isCompl_of_le [Lattice α] [BoundedOrder α] [IsM
odularLattice α] {a b c : α} (h₁ : IsCompl b c) (h₂ : b <= a) : IsCompl (⟨a ⊓ b,
 inf_le_left⟩ : Iic a) (⟨a ⊓ c, inf_le_left⟩ : Iic a)
参数：h₁ : IsCompl b c；h₂ : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsModularLattice.inf_sup_inf_assoc`：IsModularLattice.inf_sup_inf_assoc {
x y z : α} : x ⊓ z ⊔ y ⊓ z = (x ⊓ z ⊔ y) ⊓ z
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
-/
lemma Set.Iic.isCompl_inf_inf_of_isCompl_of_le [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {a b c : α} (h₁ : IsCompl b c) (h₂ : b ≤ a) :
    IsCompl (⟨a ⊓ b, inf_le_left⟩ : Iic a) (⟨a ⊓ c, inf_le_left⟩ : Iic a) := by
  constructor
  · simp [disjoint_iff, Subtype.ext_iff, inf_comm a c, inf_assoc a, ← inf_assoc b, h₁.inf_eq_bot]
  · simp only [Iic.codisjoint_iff, inf_comm a, IsModularLattice.inf_sup_inf_assoc]
    simp [inf_of_le_left h₂, h₁.sup_eq_top]

namespace IsModularLattice

variable [Lattice α] [IsModularLattice α] {a b c : α}

/-
**IsModularLattice.isModularLattice_Iic** 是 Mathlib 中的一个实例，位于命名空间 `IsModularLatt
ice`。
形式化陈述：isModularLattice_Iic : IsModularLattice (Set.Iic a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModularLattice.sup_inf_le_assoc_of_le`：∀ {α : Type u_2} {inst : Lattic
e α} [self : IsModularLattice α] {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ 
x ⊔ y ⊓ z
-/
instance isModularLattice_Iic : IsModularLattice (Set.Iic a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩
/-
**IsModularLattice.isModularLattice_Ici** 是 Mathlib 中的一个实例，位于命名空间 `IsModularLatt
ice`。
形式化陈述：isModularLattice_Ici : IsModularLattice (Set.Ici a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModularLattice.sup_inf_le_assoc_of_le`：∀ {α : Type u_2} {inst : Lattic
e α} [self : IsModularLattice α] {x : α} (y : α) {z : α}, x ≤ z → (x ⊔ y) ⊓ z ≤ 
x ⊔ y ⊓ z
-/
instance isModularLattice_Ici : IsModularLattice (Set.Ici a) :=
  ⟨@fun x y z xz => (sup_inf_le_assoc_of_le (y : α) xz : (↑x ⊔ ↑y) ⊓ ↑z ≤ ↑x ⊔ ↑y ⊓ ↑z)⟩

section ComplementedLattice

variable [BoundedOrder α] [ComplementedLattice α]

/-
**IsModularLattice.exists_inf_eq_and_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsModular
Lattice`。
形式化陈述：exists_inf_eq_and_sup_eq (hb : a <= b) (hc : b <= c) : exists b', b ⊓ b' =
 a ∧ b ⊔ b' = c
参数：hb : a <= b；hc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplementedLattice.exists_isCompl`：∀ {α : Type u_2} {inst : Lattice α} 
{inst_1 : BoundedOrder α} [self : ComplementedLattice α] (a : α), ∃ b, IsCompl a
 b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_sup_assoc_of_le`：∀ {α : Type u_1} [inst : Lattice α] [IsModularLatti
ce α] {x : α} (y : α) {z : α}, z ≤ x → x ⊓ y ⊔ z = x ⊓ (y ⊔ z)
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sup_inf_assoc_of_le`：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x 
<= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_inf_eq_and_sup_eq (hb : a ≤ b) (hc : b ≤ c) : ∃ b', b ⊓ b' = a ∧ b ⊔ b' = c := by
  obtain ⟨d, hdisjoint, hcodisjoint⟩ := exists_isCompl b
  refine ⟨(d ⊔ a) ⊓ c, ?_, ?_⟩
  · simpa [← inf_assoc, ← inf_sup_assoc_of_le _ hb, hdisjoint.eq_bot] using hb.trans hc
  · simp [← sup_inf_assoc_of_le _ hc, ← sup_assoc, hcodisjoint.eq_top]
/-
**IsModularLattice.exists_disjoint_and_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsModul
arLattice`。
形式化陈述：exists_disjoint_and_sup_eq (h : a <= b) : exists a', Disjoint a a' ∧ a ⊔ a
' = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsModularLattice.exists_inf_eq_and_sup_eq`：exists_inf_eq_and_sup_eq (hb 
: a <= b) (hc : b <= c) : exists b', b ⊓ b' = a ∧ b ⊔ b' = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem exists_disjoint_and_sup_eq (h : a ≤ b) : ∃ a', Disjoint a a' ∧ a ⊔ a' = b := by
  simp_rw [disjoint_iff]
  apply exists_inf_eq_and_sup_eq (by simp) h
/-
**IsModularLattice.exists_inf_eq_and_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsMod
ularLattice`。
形式化陈述：exists_inf_eq_and_codisjoint (h : a <= b) : exists b', b ⊓ b' = a ∧ Codisj
oint b b'
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsModularLattice.exists_inf_eq_and_sup_eq`：exists_inf_eq_and_sup_eq (hb 
: a <= b) (hc : b <= c) : exists b', b ⊓ b' = a ∧ b ⊔ b' = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem exists_inf_eq_and_codisjoint (h : a ≤ b) : ∃ b', b ⊓ b' = a ∧ Codisjoint b b' := by
  simp_rw [codisjoint_iff]
  apply exists_inf_eq_and_sup_eq h (by simp)
/-
**IsModularLattice.complementedLattice_Icc** 是 Mathlib 中的一个实例，位于命名空间 `IsModularL
attice`。
形式化陈述：complementedLattice_Icc [Fact (a <= b)] : ComplementedLattice (Set.Icc a b
) where exists_isCompl
参数：a <= b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsModularLattice.exists_inf_eq_and_sup_eq`：exists_inf_eq_and_sup_eq (hb 
: a <= b) (hc : b <= c) : exists b', b ⊓ b' = a ∧ b ⊔ b' = c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
instance complementedLattice_Icc [Fact (a ≤ b)] : ComplementedLattice (Set.Icc a b) where
  exists_isCompl := fun ⟨x, ha, hb⟩ => by
    simp_rw [Set.Icc.isCompl_iff]
    obtain ⟨y, rfl, rfl⟩ := exists_inf_eq_and_sup_eq ha hb
    exact ⟨⟨y, inf_le_right, le_sup_right⟩, rfl, rfl⟩
/-
**IsModularLattice.complementedLattice_Iic** 是 Mathlib 中的一个实例，位于命名空间 `IsModularL
attice`。
形式化陈述：complementedLattice_Iic : ComplementedLattice (Set.Iic a) where exists_isC
ompl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsModularLattice.exists_disjoint_and_sup_eq`：exists_disjoint_and_sup_eq 
(h : a <= b) : exists a', Disjoint a a' ∧ a ⊔ a' = b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
instance complementedLattice_Iic : ComplementedLattice (Set.Iic a) where
  exists_isCompl := fun ⟨x, hx⟩ => by
    simp_rw [Set.Iic.isCompl_iff]
    obtain ⟨y, hdisjoint, rfl⟩ := exists_disjoint_and_sup_eq hx
    exact ⟨⟨y, le_sup_right⟩, hdisjoint, rfl⟩
/-
**IsModularLattice.complementedLattice_Ici** 是 Mathlib 中的一个实例，位于命名空间 `IsModularL
attice`。
形式化陈述：complementedLattice_Ici : ComplementedLattice (Set.Ici a) where exists_isC
ompl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsModularLattice.exists_inf_eq_and_codisjoint`：exists_inf_eq_and_codisjo
int (h : a <= b) : exists b', b ⊓ b' = a ∧ Codisjoint b b'
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
instance complementedLattice_Ici : ComplementedLattice (Set.Ici a) where
  exists_isCompl := fun ⟨x, hx⟩ => by
    simp_rw [Set.Ici.isCompl_iff]
    obtain ⟨y, rfl, hcodisjoint⟩ := exists_inf_eq_and_codisjoint hx
    exact ⟨⟨y, inf_le_right⟩, rfl, hcodisjoint⟩

/-- A disjoint element can be enlarged to a complementary element. -/
@[to_dual /-- A codisjoint element can be shrunk to a complementary element. -/]
/-
**IsModularLattice._root_.Disjoint.exists_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `IsM
odularLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A disjoint element can be enlarged to a complementary element.
-/
theorem _root_.Disjoint.exists_isCompl {a b : α} (hab : Disjoint a b) :
    ∃ a' : α, a ≤ a' ∧ IsCompl a' b := by
  obtain ⟨u, hu⟩ := ComplementedLattice.exists_isCompl (a ⊔ b)
  exact ⟨u ⊔ a, le_sup_right, hab.isCompl_sup_left_of_isCompl_sup_right hu.symm⟩

end ComplementedLattice

end IsModularLattice

