/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Non-zero divisors and smul-divisors

In this file we define the submonoid `nonZeroDivisors` and `nonZeroSMulDivisors` of a
`MonoidWithZero`. We also define `nonZeroDivisorsLeft` and `nonZeroDivisorsRight` for
non-commutative monoids.

## Notation

This file declares the notations:
- `M₀⁰` for the submonoid of non-zero-divisors of `M₀`, in the scope `nonZeroDivisors`.
- `M₀⁰[M]` for the submonoid of non-zero smul-divisors of `M₀` with respect to `M`, in the locale
  `nonZeroSMulDivisors`

Use the statement `open scoped nonZeroDivisors nonZeroSMulDivisors` to access this notation in
your own code.

-/

@[expose] public section

assert_not_exists Ring

open Function

/-
**Irreducible.coe_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.coe_ne_zero {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀] 
[SubmonoidClass S M₀] {s : S} {x : s} (hx : Irreducible x) : (x : M₀) != 0
参数：hx : Irreducible x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Irreducible.coe_ne_zero {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀]
    [SubmonoidClass S M₀] {s : S} {x : s} (hx : Irreducible x) : (x : M₀) ≠ 0 :=
  fun h ↦ hx.1 <| by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])

section
variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

/-- The collection of elements of a `MonoidWithZero` that are not left zero divisors form a
`Submonoid`. -/
/-
**nonZeroDivisorsLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonZeroDivisorsLeft : Submonoid M₀ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of elements of a `MonoidWithZero` that are not left zero divisors
 form a
`Submonoid`.
-/
def nonZeroDivisorsLeft : Submonoid M₀ where
  carrier := {x | ∀ y, x * y = 0 → y = 0}
  one_mem' := by simp
  mul_mem' {x y} hx hy := fun z hz ↦ hy _ <| hx _ (mul_assoc x y z ▸ hz)

@[simp]
/-
**mem_nonZeroDivisorsLeft_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisorsLeft_iff : x in nonZeroDivisorsLeft M₀ ↔ forall y, x * 
y = 0 -> y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonZeroDivisorsLeft_iff : x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, x * y = 0 → y = 0 := .rfl
/-
**notMem_nonZeroDivisorsLeft_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisorsLeft_iff : x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y =
 0 ∧ y != 0}.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
-/
lemma notMem_nonZeroDivisorsLeft_iff :
    x ∉ nonZeroDivisorsLeft M₀ ↔ {y | x * y = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsLeft_iff] using! Set.nonempty_def.symm

/-- The collection of elements of a `MonoidWithZero` that are not right zero divisors form a
`Submonoid`. -/
/-
**nonZeroDivisorsRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonZeroDivisorsRight : Submonoid M₀ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of elements of a `MonoidWithZero` that are not right zero divisor
s form a
`Submonoid`.
-/
def nonZeroDivisorsRight : Submonoid M₀ where
  carrier := {x | ∀ y, y * x = 0 → y = 0}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy z hz ↦ hx _ (hy _ ((mul_assoc z x y).symm ▸ hz))

@[simp]
/-
**mem_nonZeroDivisorsRight_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisorsRight_iff : x in nonZeroDivisorsRight M₀ ↔ forall y, y 
* x = 0 -> y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonZeroDivisorsRight_iff : x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, y * x = 0 → y = 0 := .rfl
/-
**notMem_nonZeroDivisorsRight_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisorsRight_iff : x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x
 = 0 ∧ y != 0}.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
-/
lemma notMem_nonZeroDivisorsRight_iff :
    x ∉ nonZeroDivisorsRight M₀ ↔ {y | y * x = 0 ∧ y ≠ 0}.Nonempty := by
  simpa [mem_nonZeroDivisorsRight_iff] using! Set.nonempty_def.symm
/-
**nonZeroDivisorsLeft_eq_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] : nonZer
oDivisorsLeft M₀ = nonZeroDivisorsRight M₀
参数：M₀ : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]
/-
**coe_nonZeroDivisorsLeft_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M₀ : Type u_1) [inst : MonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivi
al M₀],   ↑(nonZeroDivisorsLeft M₀) = {x | x ≠ 0}
参数：M₀ : Type u_1；nonZeroDivisorsLeft M₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_nonZeroDivisorsLeft_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsLeft M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsLeft_iff, mul_eq_zero, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun hx y hx' ↦ by simp_all⟩
  contrapose! h
  exact ⟨1, Or.inl h, one_ne_zero⟩
/-
**coe_nonZeroDivisorsRight_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (M₀ : Type u_1) [inst : MonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivi
al M₀],   ↑(nonZeroDivisorsRight M₀) = {x | x ≠ 0}
参数：M₀ : Type u_1；nonZeroDivisorsRight M₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
@[simp] lemma coe_nonZeroDivisorsRight_eq [NoZeroDivisors M₀] [Nontrivial M₀] :
    nonZeroDivisorsRight M₀ = {x : M₀ | x ≠ 0} := by
  ext x
  simp only [SetLike.mem_coe, mem_nonZeroDivisorsRight_iff, mul_eq_zero, forall_eq_or_imp, true_and,
    Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun hx y hx' ↦ by contradiction⟩
  contrapose! h
  exact ⟨1, h, one_ne_zero⟩

end

/-- The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`. -/
/-
**nonZeroDivisors** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀
参数：M₀ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`.
-/
def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ :=
  nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀

/-- The notation for the submonoid of non-zero divisors. -/
scoped[nonZeroDivisors] notation:9000 M₀ "⁰" => nonZeroDivisors M₀

/-- Let `M₀` be a monoid with zero and `M` an additive monoid with an `M₀`-action, then the
collection of non-zero smul-divisors forms a submonoid.

These elements are also called `M`-regular. -/
/-
**nonZeroSMulDivisors** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonZeroSMulDivisors (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] 
[MulAction M₀ M] : Submonoid M₀ where carrier
参数：M₀ : Type*；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M₀` be a monoid with zero and `M` an additive monoid with an `M₀`-action, t
hen the
collection of non-zero smul-divisors forms a submonoid.

These elements are also called `M`-regular.
-/
def nonZeroSMulDivisors (M₀ : Type*) [MonoidWithZero M₀] (M : Type*) [Zero M] [MulAction M₀ M] :
    Submonoid M₀ where
  carrier := { r | ∀ m : M, r • m = 0 → m = 0}
  one_mem' m h := (one_smul M₀ m) ▸ h
  mul_mem' {r₁ r₂} h₁ h₂ m H := h₂ _ <| h₁ _ <| mul_smul r₁ r₂ m ▸ H

/-- The notation for the submonoid of non-zero smul-divisors. -/
scoped[nonZeroSMulDivisors] notation:9000 M₀ "⁰[" M "]" => nonZeroSMulDivisors M₀ M

open nonZeroDivisors

section MonoidWithZero
variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

/-
**nonZeroDivisorsLeft_eq_nonZeroSMulDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonZeroDivisorsLeft_eq_nonZeroSMulDivisors : nonZeroDivisorsLeft M₀ = nonZ
eroSMulDivisors M₀ M₀
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonZeroDivisorsLeft_eq_nonZeroSMulDivisors :
    nonZeroDivisorsLeft M₀ = nonZeroSMulDivisors M₀ M₀ := rfl
/-
**mem_nonZeroDivisors_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_iff : r in M₀⁰ ↔ (forall x, r * x = 0 -> x = 0) ∧ fora
ll x, x * r = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonZeroDivisors_iff :
    r ∈ M₀⁰ ↔ (∀ x, r * x = 0 → x = 0) ∧ ∀ x, x * r = 0 → x = 0 := Iff.rfl
/-
**mem_nonZeroDivisors_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_iff' : r in M₀⁰ ↔ r in nonZeroDivisorsLeft M₀ ∧ r in n
onZeroDivisorsRight M₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonZeroDivisors_iff' :
    r ∈ M₀⁰ ↔ r ∈ nonZeroDivisorsLeft M₀ ∧ r ∈ nonZeroDivisorsRight M₀ := Iff.rfl
/-
**notMem_nonZeroDivisors_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisors_iff : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.Nonempty ∨
 {s | s * r = 0 ∧ s != 0}.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma notMem_nonZeroDivisors_iff :
    r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty ∨ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [-not_and, not_and_or, mem_nonZeroDivisors_iff, Set.nonempty_def]
/-
**mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff (hr : r in nonZeroDivisorsLef
t M₀) : r * x = 0 ↔ x = 0
参数：hr : r in nonZeroDivisorsLeft M₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff (hr : r ∈ nonZeroDivisorsLeft M₀) :
    r * x = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩
/-
**mul_right_mem_nonZeroDivisorsRight_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_mem_nonZeroDivisorsRight_eq_zero_iff (hr : r in nonZeroDivisorsR
ight M₀) : x * r = 0 ↔ x = 0
参数：hr : r in nonZeroDivisorsRight M₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mul_right_mem_nonZeroDivisorsRight_eq_zero_iff (hr : r ∈ nonZeroDivisorsRight M₀) :
    x * r = 0 ↔ x = 0 :=
  ⟨hr _, by simp +contextual⟩
/-
**mul_right_mem_nonZeroDivisors_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x 
= 0
参数：hr : r in M₀⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_mem_nonZeroDivisorsRight_eq_zero_iff`：mul_right_mem_nonZeroDiv
isorsRight_eq_zero_iff (hr : r in nonZeroDivisorsRight M₀) : x * r = 0 ↔ x = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : x * r = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

@[simp]
/-
**mul_right_coe_nonZeroDivisors_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`：mul_right_mem_nonZeroDivisors
_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mul_right_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_nonZeroDivisors_eq_zero_iff c.prop
/-
**IsUnit.mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x in M₀⁰
参数：hx : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_right_eq_zero`：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) :
 a * b = 0 ↔ b = 0
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
-/
lemma IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x ∈ M₀⁰ :=
  ⟨fun _ ↦ hx.mul_right_eq_zero.mp, fun _ ↦ hx.mul_left_eq_zero.mp⟩

variable (M₀) in
/-
**isUnit_le_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_le_nonZeroDivisors : IsUnit.submonoid M₀ <= M₀⁰
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
-/
lemma isUnit_le_nonZeroDivisors : IsUnit.submonoid M₀ ≤ M₀⁰ := fun _ ↦ (·.mem_nonZeroDivisors)

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]
/-
**mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft (hx : x in nonZeroD
ivisorsLeft M₀) (hy : y in nonZeroDivisorsLeft M₀) : x * y in nonZeroDivisorsLef
t M₀
参数：hx : x in nonZeroDivisorsLeft M₀；hy : y in nonZeroDivisorsLeft M₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
lemma mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft (hx : x ∈ nonZeroDivisorsLeft M₀)
    (hy : y ∈ nonZeroDivisorsLeft M₀) :
    x * y ∈ nonZeroDivisorsLeft M₀ := Submonoid.mul_mem _ hx hy

@[deprecated "Use `Submonoid.mul_mem _ hx hy` instead." (since := "2026-01-07")]
/-
**mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight (hx : x in nonZer
oDivisorsRight M₀) (hy : y in nonZeroDivisorsRight M₀) : x * y in nonZeroDivisor
sRight M₀
参数：hx : x in nonZeroDivisorsRight M₀；hy : y in nonZeroDivisorsRight M₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
-/
lemma mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight (hx : x ∈ nonZeroDivisorsRight M₀)
    (hy : y ∈ nonZeroDivisorsRight M₀) :
    x * y ∈ nonZeroDivisorsRight M₀ := Submonoid.mul_mem _ hx hy
/-
**mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors (hx : x in M₀⁰) (hy : y in 
M₀⁰) : x * y in M₀⁰
参数：hx : x in M₀⁰；hy : y in M₀⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff'`：mem_nonZeroDivisors_iff' : r in M₀⁰ ↔ r in non
ZeroDivisorsLeft M₀ ∧ r in nonZeroDivisorsRight M₀
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors (hx : x ∈ M₀⁰) (hy : y ∈ M₀⁰) :
    x * y ∈ M₀⁰ :=
  mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

section Nontrivial
variable [Nontrivial M₀]

/-
**zero_notMem_nonZeroDivisorsLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀ :=
  fun h ↦ one_ne_zero <| h 1 <| zero_mul _
/-
**zero_notMem_nonZeroDivisorsRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_notMem_nonZeroDivisorsRight : 0 ∉ nonZeroDivisorsRight M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem zero_notMem_nonZeroDivisorsRight : 0 ∉ nonZeroDivisorsRight M₀ :=
  fun h ↦ one_ne_zero <| h 1 <| mul_zero _
/-
**zero_notMem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_notMem_nonZeroDivisorsLeft`：zero_notMem_nonZeroDivisorsLeft : 0 ∉ n
onZeroDivisorsLeft M₀
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰ := fun h ↦ zero_notMem_nonZeroDivisorsLeft h.1
/-
**nonZeroDivisors.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 0
参数：hx : x in M₀⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
-/
theorem nonZeroDivisors.ne_zero (hx : x ∈ M₀⁰) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

@[simp]
/-
**nonZeroDivisors.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) != 0
参数：x : M₀⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) ≠ 0 := nonZeroDivisors.ne_zero x.2
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLeftCancelMulZero M₀] : LeftCancelMonoid M₀⁰ where
  mul_left_cancel z _ _ h := Subtype.ext <|
    mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsRightCancelMulZero M₀] : RightCancelMonoid M₀⁰ where
  mul_right_cancel z _ _ h := Subtype.ext <|
    mul_right_cancel₀ (nonZeroDivisors.coe_ne_zero z) (by
      simpa only [Subtype.ext_iff, Submonoid.coe_mul] using h)

end Nontrivial

section NoZeroDivisors
variable [NoZeroDivisors M₀]

/-
**eq_zero_of_ne_zero_of_mul_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x != 0) (hxy : y * x = 0) : 
y = 0
参数：hx : x != 0；hxy : y * x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
-/
theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx
/-
**eq_zero_of_ne_zero_of_mul_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x != 0) (hxy : x * y = 0) : y
 = 0
参数：hx : x != 0；hxy : x * y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
-/
theorem eq_zero_of_ne_zero_of_mul_left_eq_zero (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx
/-
**mem_nonZeroDivisors_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_of_ne_zero (hx : x != 0) : x in M₀⁰
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`：eq_zero_of_ne_zero_of_mul_left_e
q_zero (hx : x != 0) (hxy : x * y = 0) : y = 0
· 使用定理 `eq_zero_of_ne_zero_of_mul_right_eq_zero`：eq_zero_of_ne_zero_of_mul_right
_eq_zero (hx : x != 0) (hxy : y * x = 0) : y = 0
-/
theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ :=
  ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩
/-
**mem_nonZeroDivisors_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] {x : M₀} [NoZeroDivisors M₀] 
[Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
-/
@[simp] lemma mem_nonZeroDivisors_iff_ne_zero [Nontrivial M₀] : x ∈ M₀⁰ ↔ x ≠ 0 :=
  ⟨nonZeroDivisors.ne_zero, mem_nonZeroDivisors_of_ne_zero⟩
/-
**le_nonZeroDivisors_of_noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S
) : S <= M₀⁰
参数：hS : (0 : M₀) ∉ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S ≤ M₀⁰ := fun _ hx ↦
  mem_nonZeroDivisors_of_ne_zero <| by rintro rfl; exact hS hx
/-
**powers_le_nonZeroDivisors_of_noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x != 0) : Submonoid.powe
rs x <= M₀⁰
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nonZeroDivisors_of_noZeroDivisors`：le_nonZeroDivisors_of_noZeroDiviso
rs {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) : S <= M₀⁰
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
-/
theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x ≠ 0) : Submonoid.powers x ≤ M₀⁰ :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hx (h.recOn fun _ ↦ eq_zero_of_pow_eq_zero)

end NoZeroDivisors

/-
**IsLeftRegular.mem_nonZeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) : r in nonZero
DivisorsLeft M₀
参数：h : IsLeftRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLeftRegular.mul_left_eq_zero_iff`：∀ {R : Type u_1} [inst : MulZeroClas
s R] {a b : R}, IsLeftRegular b → (b * a = 0 ↔ a = 0)
-/
lemma IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) :
    r ∈ nonZeroDivisorsLeft M₀ := fun _x hx ↦ h.mul_left_eq_zero_iff.mp hx
/-
**IsRightRegular.mem_nonZeroDivisorsRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) : r in nonZ
eroDivisorsRight M₀
参数：h : IsRightRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsRightRegular.mul_right_eq_zero_iff`：∀ {R : Type u_1} [inst : MulZeroCl
ass R] {a b : R}, IsRightRegular b → (a * b = 0 ↔ a = 0)
-/
lemma IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r ∈ nonZeroDivisorsRight M₀ := fun _x hx ↦ h.mul_right_eq_zero_iff.mp hx
/-
**IsRegular.mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r in M₀⁰
参数：h : IsRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLeftRegular.mem_nonZeroDivisorsLeft`：IsLeftRegular.mem_nonZeroDivisors
Left (h : IsLeftRegular r) : r in nonZeroDivisorsLeft M₀
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用引理 `IsRightRegular.mem_nonZeroDivisorsRight`：IsRightRegular.mem_nonZeroDivis
orsRight (h : IsRightRegular r) : r in nonZeroDivisorsRight M₀
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
-/
lemma IsRegular.mem_nonZeroDivisors (h : IsRegular r) : r ∈ M₀⁰ :=
  ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩
/-
**noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft : NoZeroDivisors M₀ ↔ fo
rall x : M₀, x != 0 -> x in nonZeroDivisorsLeft M₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `noZeroDivisors_iff_right_eq_zero_of_mul`：noZeroDivisors_iff_right_eq_zer
o_of_mul : NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, x * y = 0 -> y
 = 0
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsLeft M₀ :=
  noZeroDivisors_iff_right_eq_zero_of_mul
/-
**noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight : NoZeroDivisors M₀ ↔ f
orall x : M₀, x != 0 -> x in nonZeroDivisorsRight M₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `noZeroDivisors_iff_left_eq_zero_of_mul`：noZeroDivisors_iff_left_eq_zero_
of_mul : NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, y * x = 0 -> y =
 0
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsRight M₀ :=
  noZeroDivisors_iff_left_eq_zero_of_mul
/-
**noZeroDivisors_iff_forall_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_iff_forall_mem_nonZeroDivisors : NoZeroDivisors M₀ ↔ forall
 x : M₀, x != 0 -> x in M₀⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `noZeroDivisors_iff_eq_zero_of_mul`：noZeroDivisors_iff_eq_zero_of_mul : N
oZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> (forall y, x * y = 0 -> y = 0) ∧ (fo
rall y, y * x = 0 -> y …
-/
lemma noZeroDivisors_iff_forall_mem_nonZeroDivisors :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ M₀⁰ :=
  noZeroDivisors_iff_eq_zero_of_mul
/-
**IsSMulRegular.mem_nonZeroSMulDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulActionWithZ
ero M₀ M] {m₀ : M₀} (h : IsSMulRegular M m₀) : m₀ in nonZeroSMulDivisors M₀ M
参数：h : IsSMulRegular M m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.right_eq_zero_of_smul`：∀ {R : Type u_1} {M : Type u_3} [in
st : Zero M] [inst_1 : SMulZeroClass R M] {r : R} {x : M},   IsSMulRegular M r →
 r • x = 0 → x = 0
-/
lemma IsSMulRegular.mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulActionWithZero M₀ M] {m₀ : M₀}
    (h : IsSMulRegular M m₀) : m₀ ∈ nonZeroSMulDivisors M₀ M :=
  fun _ ↦ h.right_eq_zero_of_smul
/-
**isSMulRegular_iff_mem_nonZeroSMulDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [Distri
bMulAction M₀ M] {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ in nonZeroSMulDivisors M₀ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSMulRegular_iff_right_eq_zero_of_smul`：isSMulRegular_iff_right_eq_zero
_of_smul [AddGroup M] [DistribSMul R M] {r : R} : IsSMulRegular M r ↔ forall m :
 M, r • m = 0 -> m = 0 where …
-/
lemma isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
    {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ ∈ nonZeroSMulDivisors M₀ M :=
  isSMulRegular_iff_right_eq_zero_of_smul

variable [FunLike F M₀ M₀']

-- TODO: nonZeroDivisorsLeft/Right also works
/-
**map_ne_zero_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀']
 (g : F) (hg : Injective (g : M₀ -> M₀')) {x : M₀} (h : x in M₀⁰) : g x != 0
参数：g : F；hg : Injective (g : M₀ -> M₀')；h : x in M₀⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective (g : M₀ → M₀')) {x : M₀} (h : x ∈ M₀⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))
/-
**map_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass
 F M₀ M₀'] (g : F) (hg : Injective g) {x : M₀} (h : x in M₀⁰) : g x in M₀'⁰
参数：g : F；hg : Injective g；h : x in M₀⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`：eq_zero_of_ne_zero_of_mul_left_e
q_zero (hx : x != 0) (hxy : x * y = 0) : y = 0
· 使用定理 `map_ne_zero_of_mem_nonZeroDivisors`：map_ne_zero_of_mem_nonZeroDivisors [
Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective (g : M₀ -> M₀')) 
{x : M₀} (h : x in M₀⁰) …
· 使用定理 `eq_zero_of_ne_zero_of_mul_right_eq_zero`：eq_zero_of_ne_zero_of_mul_right
_eq_zero (hx : x != 0) (hxy : y * x = 0) : y = 0
-/
theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Injective g) {x : M₀} (h : x ∈ M₀⁰) : g x ∈ M₀'⁰ :=
  ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩
/-
**MulEquivClass.map_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [Mo
noidWithZero S] [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) : Submonoid.ma
p h (nonZeroDivisors M₀) = nonZeroDivisors S
参数：h : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : M ≃* N) 
(K : Submonoid M) : K.map f = K.comap f.symm
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]
/-
**map_le_nonZeroDivisors_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHo
mClass F M₀ M₀'] (f : F) (hf : Injective f) {S : Submonoid M₀} (hS : S <= M₀⁰) :
 S.map f <= M₀'⁰
参数：f : F；hf : Injective f；hS : S <= M₀⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Submonoid.map_bot`：map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥
· 使用定理 `le_nonZeroDivisors_of_noZeroDivisors`：le_nonZeroDivisors_of_noZeroDiviso
rs {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) : S <= M₀⁰
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Injective f) {S : Submonoid M₀} (hS : S ≤ M₀⁰) : S.map f ≤ M₀'⁰ := by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
    exact zero_notMem_nonZeroDivisors <| hS <| map_eq_zero_iff f hf |>.mp hx0 ▸ hx
/-
**nonZeroDivisors_le_comap_nonZeroDivisors_of_injective** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
 [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective f) : M₀⁰ <= M₀'⁰.coma
p f
参数：f : F；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.le_comap_of_map_le`：le_comap_of_map_le {T : Submonoid N} {f : 
F} : S.map f <= T -> S <= T.comap f
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_le_nonZeroDivisors_of_injective`：map_le_nonZeroDivisors_of_injective
 [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective 
f) {S : Submonoid M₀} (hS…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Injective f) : M₀⁰ ≤ M₀'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

/-- If an element maps to a non-zero-divisor via injective homomorphism,
then it is a non-zero-divisor. -/
/-
**mem_nonZeroDivisors_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
 (hf : Injective f) (hx : f x in M₀'⁰) : x in M₀⁰
参数：hf : Injective f；hx : f x in M₀'⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If an element maps to a non-zero-divisor via injective homomorphism,
then it is a non-zero-divisor.
-/
theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) (hx : f x ∈ M₀'⁰) : x ∈ M₀⁰ :=
  ⟨fun y hy ↦ hf <| map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
    fun y hy ↦ hf <| map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩
/-
**comap_nonZeroDivisors_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f
 : F} (hf : Injective f) : M₀'⁰.comap f <= M₀⁰
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mem_nonZeroDivisors_of_injective`：mem_nonZeroDivisors_of_injective [Mono
idWithZeroHomClass F M₀ M₀'] {f : F} (hf : Injective f) (hx : f x in M₀'⁰) : x i
n M₀⁰
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_comap`：mem_comap {S : Submonoid N} {f : F} {x : M} : x in 
S.comap f ↔ f x in S
-/
theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Injective f) : M₀'⁰.comap f ≤ M₀⁰ :=
  fun _ ha ↦ mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

/-
**nonZeroDivisorsLeft_eq_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroD
ivisors M₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonZeroDivisors.eq_1`：∀ (M₀ : Type u_1) [inst : MonoidWithZero M₀], nonZ
eroDivisors M₀ = nonZeroDivisorsLeft M₀ ⊓ nonZeroDivisorsRight M₀
· 使用引理 `nonZeroDivisorsLeft_eq_right`：nonZeroDivisorsLeft_eq_right (M₀ : Type*) 
[CommMonoidWithZero M₀] : nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
lemma nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀ := by
  rw [nonZeroDivisors, nonZeroDivisorsLeft_eq_right, inf_idem]
/-
**nonZeroDivisorsRight_eq_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZer
oDivisors M₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `nonZeroDivisorsLeft_eq_right`：nonZeroDivisorsLeft_eq_right (M₀ : Type*) 
[CommMonoidWithZero M₀] : nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀
· 使用引理 `nonZeroDivisorsLeft_eq_nonZeroDivisors`：nonZeroDivisorsLeft_eq_nonZeroDi
visors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
-/
lemma nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀ := by
  rw [← nonZeroDivisorsLeft_eq_right, nonZeroDivisorsLeft_eq_nonZeroDivisors]
/-
**nonZeroDivisorsRight_eq_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonZeroDivisorsRight_eq_left : nonZeroDivisorsRight M₀ = nonZeroDivisorsLe
ft M₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nonZeroDivisorsLeft_eq_right`：nonZeroDivisorsLeft_eq_right (M₀ : Type*) 
[CommMonoidWithZero M₀] : nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀
-/
lemma nonZeroDivisorsRight_eq_left : nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀ := by
  rw [nonZeroDivisorsLeft_eq_right]
/-
**mem_nonZeroDivisors_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_iff_left : r in M₀⁰ ↔ forall x, r * x = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `nonZeroDivisorsLeft_eq_nonZeroDivisors`：nonZeroDivisorsLeft_eq_nonZeroDi
visors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonZeroDivisors_iff_left : r ∈ M₀⁰ ↔ ∀ x, r * x = 0 → x = 0 := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl
/-
**mem_nonZeroDivisors_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nonZeroDivisors_iff_right : r in M₀⁰ ↔ forall x, x * r = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `nonZeroDivisorsRight_eq_nonZeroDivisors`：nonZeroDivisorsRight_eq_nonZero
Divisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nonZeroDivisors_iff_right : r ∈ M₀⁰ ↔ ∀ x, x * r = 0 → x = 0 := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl
/-
**notMem_nonZeroDivisors_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisors_iff_left : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s != 0}.Nonem
pty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma notMem_nonZeroDivisors_iff_left : r ∉ M₀⁰ ↔ {s | r * s = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_left, Set.nonempty_def]
/-
**notMem_nonZeroDivisors_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s != 0}.None
mpty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma notMem_nonZeroDivisors_iff_right : r ∉ M₀⁰ ↔ {s | s * r = 0 ∧ s ≠ 0}.Nonempty := by
  simp [mem_nonZeroDivisors_iff_right, Set.nonempty_def]
/-
**mul_left_mem_nonZeroDivisors_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r in M₀⁰) : r * x = 0 ↔ x =
 0
参数：hr : r in M₀⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`：mul_right_mem_nonZeroDivisors
_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

@[simp]
/-
**mul_left_coe_nonZeroDivisors_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x 
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_left_mem_nonZeroDivisors_eq_zero_iff`：mul_left_mem_nonZeroDivisors_e
q_zero_iff (hr : r in M₀⁰) : r * x = 0 ↔ x = 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 :=
  mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop
/-
**mul_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M₀⁰ ∧ b in M₀⁰ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `nonZeroDivisorsRight_eq_nonZeroDivisors`：nonZeroDivisorsRight_eq_nonZero
Divisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mul_mem_nonZeroDivisors : a * b ∈ M₀⁰ ↔ a ∈ M₀⁰ ∧ b ∈ M₀⁰ where
  mp h := by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h ↦ mul_mem h.1 h.2
/-
**nonZeroDivisors_dvd_iff_dvd_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} : a ∣ b ↔ (a : M₀) ∣ (b : M₀)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} :
    a ∣ b ↔ (a : M₀) ∣ (b : M₀) :=
  ⟨fun ⟨c, hc⟩ ↦ by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ ↦ ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩
/-
**prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors {ι : Type*} {s : Finset ι}
 {f : ι -> M₀} (h : forall i in s, f i in M₀⁰) : ∏ i in s, f i in M₀⁰
参数：h : forall i in s, f i in M₀⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
lemma prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    {ι : Type*} {s : Finset ι} {f : ι → M₀} (h : ∀ i ∈ s, f i ∈ M₀⁰) :
    ∏ i ∈ s, f i ∈ M₀⁰ :=
  s.prod_induction _ _ (fun _ _ ↦ and_imp.mp mul_mem_nonZeroDivisors.mpr) (one_mem _) h

end CommMonoidWithZero

section GroupWithZero
variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

/-- Canonical isomorphism between the non-zero-divisors and units of a group with zero. -/
@[simps]
/-
**nonZeroDivisorsEquivUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical isomorphism between the non-zero-divisors and units of a group with ze
ro.
-/
noncomputable def nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where
  toFun u := .mk0 _ <| mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  right_inv u := by simp
  map_mul' u v := by simp
/-
**isUnit_of_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_of_mem_nonZeroDivisors (hx : x in nonZeroDivisors G₀) : IsUnit x
参数：hx : x in nonZeroDivisors G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma isUnit_of_mem_nonZeroDivisors (hx : x ∈ nonZeroDivisors G₀) : IsUnit x :=
  (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

end GroupWithZero

section nonZeroSMulDivisors

open nonZeroSMulDivisors

variable {M₀ M : Type*} [MonoidWithZero M₀] [Zero M] [MulAction M₀ M] {x : M₀}

/-
**mem_nonZeroSMulDivisors_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nonZeroSMulDivisors_iff : x in M₀⁰[M] ↔ forall (m : M), x • m = 0 -> m
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonZeroSMulDivisors_iff : x ∈ M₀⁰[M] ↔ ∀ (m : M), x • m = 0 → m = 0 := Iff.rfl

end nonZeroSMulDivisors

open scoped nonZeroDivisors

variable {M₀}

section MonoidWithZero
variable [MonoidWithZero M₀] {a b : M₀⁰}

/-- The units of the monoid of non-zero divisors of `M₀` are equivalent to the units of `M₀`. -/
@[simps]
/-
**unitsNonZeroDivisorsEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitsNonZeroDivisorsEquiv : M₀⁰ˣ ≃* M₀ˣ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The units of the monoid of non-zero divisors of `M₀` are equivalent to the units
 of `M₀`.
-/
def unitsNonZeroDivisorsEquiv : M₀⁰ˣ ≃* M₀ˣ where
  __ := Units.map M₀⁰.subtype
  invFun u := ⟨⟨u, u.isUnit.mem_nonZeroDivisors⟩, ⟨(u⁻¹ : M₀ˣ), u⁻¹.isUnit.mem_nonZeroDivisors⟩,
    by simp, by simp⟩
/-
**nonZeroDivisors.associated_coe** 是 Mathlib 中的一个定理，位于命名空间 `nonZeroDivisors`。
形式化陈述：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a b : ↥(nonZeroDivisors M₀)}
, Associated ↑a ↑b ↔ Associated a b
参数：nonZeroDivisors M₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `unitsNonZeroDivisorsEquiv_apply`：∀ {M₀ : Type u_1} [inst : MonoidWithZer
o M₀] (a : (↥(nonZeroDivisors M₀))ˣ),   unitsNonZeroDivisorsEquiv a = (↑(Units.m
ap (nonZeroDivisors M…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma nonZeroDivisors.associated_coe : Associated (a : M₀) b ↔ Associated a b :=
  unitsNonZeroDivisorsEquiv.symm.exists_congr_left.trans <| by simp [Associated]; norm_cast

end MonoidWithZero

section CommMonoidWithZero
variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

/-
**mk_mem_nonZeroDivisors_associates** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mk_mem_nonZeroDivisors_associates : Associates.mk a in (Associates M₀)⁰ ↔ 
a in M₀⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_eq_zero`：mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0
· 使用定理 `Associates.mk_mul_mk`：mk_mul_mk {x y : M} : Associates.mk x * Associates
.mk y = Associates.mk (x * y)
· 使用定理 `Associates.quot_mk_eq_mk`：quot_mk_eq_mk [Monoid M] (a : M) : Quot.mk Set
oid.r a = Associates.mk a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Associates.mk_zero`：∀ {M : Type u_1} [inst : Zero M] [inst_1 : Monoid M]
, Associates.mk 0 = 0
-/
theorem mk_mem_nonZeroDivisors_associates : Associates.mk a ∈ (Associates M₀)⁰ ↔ a ∈ M₀⁰ := by
  rw [mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

/-- The non-zero divisors of associates of a monoid with zero `M₀` are isomorphic to the associates
of the non-zero divisors of `M₀` under the map `⟨⟦a⟧, _⟩ ↦ ⟦⟨a, _⟩⟧`. -/
/-
**associatesNonZeroDivisorsEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：associatesNonZeroDivisorsEquiv : (Associates M₀)⁰ ≃* Associates M₀⁰ where 
toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-zero divisors of associates of a monoid with zero `M₀` are isomorphic to
 the associates
of the non-zero divisors of `M₀` under the map `⟨⟦a⟧, _⟩ ↦ ⟦⟨a, _⟩⟧`.
-/
def associatesNonZeroDivisorsEquiv : (Associates M₀)⁰ ≃* Associates M₀⁰ where
  toEquiv := .subtypeQuotientEquivQuotientSubtype _ (s₂ := Associated.setoid _)
    (· ∈ nonZeroDivisors _)
    (by simp [mem_nonZeroDivisors_iff, Quotient.forall, Associates.mk_mul_mk])
    (by simp +instances [Associated.setoid])
  map_mul' := by simp [Quotient.forall, Associates.mk_mul_mk]

@[simp]
/-
**associatesNonZeroDivisorsEquiv_mk_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) : associatesNonZeroDivi
sorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧
参数：a : M₀；ha。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧ := rfl

@[simp]
/-
**associatesNonZeroDivisorsEquiv_symm_mk_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) : associatesNonZer
oDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩
参数：a : M₀；ha。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩ :=
  rfl

end CommMonoidWithZero

