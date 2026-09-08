/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Use

/-!
# Equality modulo an element

This file defines equality modulo an element in an additive commutative monoid.
In case of a group, `a` and `b` are congruent modulo `p` iff `b - a ∈ zmultiples p`.

In case of a monoid, the definition is a bit more complicated,
and it is given with the use case of natural numbers in mind.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo `p`.

## See also

`SModEq` is a generalisation to arbitrary submodules.

## TODO

- Delete `Nat.ModEq` and `Int.ModEq` in favour of `AddCommGroup.ModEq`.
- Relate to `SModEq`.
-/

public section

assert_not_exists Module IsOrderedMonoid Function.support

namespace AddCommGroup

section AddCommMonoid
variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

/-- `a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

If `a`, `b` are elements of an additive group,
then `a ≡ b [PMOD p]` iff `m • p = b - a` for some `m : ℤ`, see `modEq_iff_zsmul` below.
For additive commutative monoid, the definition is given by `modEq_iff_nsmul`.

Equivalently (as shown in `Algebra.Order.ToIntervalMod`), `b` does not lie in the open interval
`(a, a + p)` modulo `p`, or `toIcoMod hp a` disagrees with `toIocMod hp a` at `b`, or
`toIcoDiv hp a` disagrees with `toIocDiv hp a` at `b`. -/
/-
**AddCommGroup.ModEq** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGroup`。
形式化陈述：ModEq (p a b : M) : Prop
参数：p a b : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a ≡ b [PMOD p]` means that `b` is congruent to `a` modulo `p`.

If `a`, `b` are elements of an additive group,
then `a ≡ b [PMOD p]` iff `m • p = b - a` for some `m : ℤ`, see `modEq_iff_zsmul
` below.
For additive commutative monoid, the definition is given by `modEq_iff_nsmul`.

Equivalently (as shown in `Algebra.Order.ToIntervalMod`), `b` does not lie in th
e open interval
`(a, a + p)` modulo `p`, or `toIcoMod hp a` disagrees with `toIocMod hp a` at `b
`, or
`toIcoDiv hp a` disagrees with `toIocDiv hp a` at `b`.
-/
def ModEq (p a b : M) : Prop :=
  ∃ m n : ℕ, m • p + a = n • p + b

@[inherit_doc]
notation:50 a " ≡ " b " [PMOD " p "]" => ModEq p a b
/-
**AddCommGroup.modEq_iff_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists m n : Nat, m • p + a = n • p + b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_iff_nsmul : a ≡ b [PMOD p] ↔ ∃ m n : ℕ, m • p + a = n • p + b := by
  rfl

@[refl, simp]
/-
**AddCommGroup.modEq_refl** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_refl (a : M) : a ≡ a [PMOD p]
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modEq_refl (a : M) : a ≡ a [PMOD p] :=
  ⟨0, 0, by simp⟩
/-
**AddCommGroup.modEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_rfl : a ≡ a [PMOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.modEq_refl`：modEq_refl (a : M) : a ≡ a [PMOD p]
-/
theorem modEq_rfl : a ≡ a [PMOD p] :=
  modEq_refl _
/-
**AddCommGroup.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (ModEq p) := ⟨modEq_refl⟩

@[symm]
/-
**AddCommGroup.ModEq.symm** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M}, a ≡ b [PMOD p] → b 
≡ a [PMOD p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩
/-
**AddCommGroup.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (ModEq p) := ⟨fun _ _ ↦ .symm⟩
/-
**AddCommGroup.modEq_comm** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.symm`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b 
p : M}, a ≡ b [PMOD p] → b ≡ a [PMOD p]
-/
theorem modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p] := ⟨.symm, .symm⟩

@[trans]
/-
**AddCommGroup.ModEq.trans** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b c p : M}, a ≡ b [PMOD p] → 
b ≡ c [PMOD p] → a ≡ c [PMOD p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
-/
protected theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul, add_assoc, hab, add_nsmul, add_assoc, ← hbc, add_left_comm]
/-
**AddCommGroup.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans M (ModEq p) := ⟨fun _ _ _ ↦ .trans⟩

@[simp]
/-
**AddCommGroup.modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_zero : a ≡ b [PMOD 0] ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [modEq_iff_nsmul]

@[simp]
/-
**AddCommGroup.self_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：self_modEq_zero : p ≡ 0 [PMOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_modEq_zero : p ≡ 0 [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩
/-
**AddCommGroup.add_nsmul_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：add_nsmul_modEq (n : Nat) : a + n • p ≡ a [PMOD p]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩
/-
**AddCommGroup.nsmul_add_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：nsmul_add_modEq (n : Nat) : n • p + a ≡ a [PMOD p]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] :=
  modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

namespace ModEq

/-
**AddCommGroup.ModEq.add** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b c d p : M}, a ≡ b [PMOD p] 
→ c ≡ d [PMOD p] → a + c ≡ b + d [PMOD p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
protected theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  rw [modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul, add_add_add_comm, hab, hcd, add_nsmul, add_add_add_comm]
/-
**AddCommGroup.ModEq.add_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} (c : M), a ≡ b [PMOD
 p] → c + a ≡ c + b [PMOD p]
参数：c : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.add`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b c
 d p : M}, a ≡ b [PMOD p] → c ≡ d [PMOD p] → a + c ≡ b + d [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem add_left (c : M) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] :=
  modEq_rfl.add h
/-
**AddCommGroup.ModEq.add_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} (c : M), a ≡ b [PMOD
 p] → a + c ≡ b + c [PMOD p]
参数：c : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.add`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b c
 d p : M}, a ≡ b [PMOD p] → c ≡ d [PMOD p] → a + c ≡ b + d [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem add_right (c : M) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] :=
  h.add modEq_rfl
/-
**AddCommGroup.ModEq.of_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} {n : ℕ}, a ≡ b [PMOD
 n • p] → a ≡ b [PMOD p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
-/
protected theorem of_nsmul {n : ℕ} : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩
/-
**AddCommGroup.ModEq.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} {n : ℕ}, a ≡ b [PMOD
 p] → n • a ≡ n • b [PMOD n • p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m *
 n) • a = n • m • a
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
-/
protected theorem nsmul {n : ℕ} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul, mul_nsmul', ← nsmul_add, h, nsmul_add, ← mul_nsmul, mul_nsmul']
/-
**AddCommGroup.ModEq.add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} (n : ℕ), a ≡ b [PMOD
 p] → a + n • p ≡ b [PMOD p]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.trans`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b
 c p : M}, a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p]
· 使用定理 `AddCommGroup.add_nsmul_modEq`：add_nsmul_modEq (n : Nat) : a + n • p ≡ a 
[PMOD p]
-/
protected theorem add_nsmul (n : ℕ) : a ≡ b [PMOD p] → a + n • p ≡ b [PMOD p] :=
  (add_nsmul_modEq _).trans
/-
**AddCommGroup.ModEq.nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b p : M} (n : ℕ), a ≡ b [PMOD
 p] → n • p + a ≡ b [PMOD p]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.trans`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b
 c p : M}, a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p]
· 使用定理 `AddCommGroup.nsmul_add_modEq`：nsmul_add_modEq (n : Nat) : n • p + a ≡ a 
[PMOD p]
-/
protected theorem nsmul_add (n : ℕ) : a ≡ b [PMOD p] → n • p + a ≡ b [PMOD p] :=
  (nsmul_add_modEq _).trans
/-
**AddCommGroup.ModEq.map** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M
 N] (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p]
参数：f : F；h : a ≡ b [PMOD p]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
-/
theorem map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p] := by
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

end ModEq

/-
**AddCommGroup.map_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHo
mClass F M N] (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b
 [PMOD p]
参数：f : F；hf : Function.Injective f。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b [PMOD p] := by
  simp only [modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

@[simp]
/-
**AddCommGroup.nsmul_modEq_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：nsmul_modEq_nsmul [IsAddTorsionFree M] {n : Nat} (hn : n != 0) : n • a ≡ n
 • b [PMOD n • p] ↔ a ≡ b [PMOD p]
参数：hn : n != 0。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m *
 n) • a = n • m • a
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nsmul_modEq_nsmul [IsAddTorsionFree M] {n : ℕ} (hn : n ≠ 0) :
    n • a ≡ n • b [PMOD n • p] ↔ a ≡ b [PMOD p] := by
  simp only [modEq_iff_nsmul, ← mul_nsmul _ n, mul_nsmul' _ n, ← nsmul_add, nsmul_right_inj hn]

alias ⟨ModEq.nsmul_cancel, _⟩ := nsmul_modEq_nsmul

end AddCommMonoid

section AddCancelCommMonoid
variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

namespace ModEq

@[simp]
/-
**AddCommGroup.ModEq.add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`
。
形式化陈述：∀ {M : Type u_1} [inst : AddCancelCommMonoid M] {a b c d p : M},   a ≡ b [
PMOD p] → (a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p])
参数：a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `AddCommGroup.ModEq.add`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b c
 d p : M}, a ≡ b [PMOD p] → c ≡ d [PMOD p] → a + c ≡ b + d [PMOD p]
-/
protected theorem add_iff_left (h : a ≡ b [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ c ≡ d [PMOD p] := by
  refine ⟨fun hadd ↦ ?_, h.add⟩
  rw [modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  rcases hadd with ⟨m, n, hadd⟩
  use m + l, n + k
  apply add_right_cancel (b := a)
  rw [add_assoc, add_comm c, add_nsmul, add_right_comm, hadd, ← add_assoc, add_right_comm _ b,
    add_right_comm _ b, add_assoc, ← h, add_add_add_comm, add_nsmul, ← add_assoc]

@[simp]
/-
**AddCommGroup.ModEq.add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq
`。
形式化陈述：∀ {M : Type u_1} [inst : AddCancelCommMonoid M] {a b c d p : M},   c ≡ d [
PMOD p] → (a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p])
参数：a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddCommGroup.ModEq.add_iff_left`：∀ {M : Type u_1} [inst : AddCancelCommM
onoid M] {a b c d p : M},   a ≡ b [PMOD p] → (a + c ≡ b + d [PMOD p] ↔ c ≡ d [PM
OD p])
-/
protected theorem add_iff_right (h : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] ↔ a ≡ b [PMOD p] := by
  simpa only [add_comm c, add_comm d] using h.add_iff_left

protected alias ⟨add_left_cancel, _⟩ := ModEq.add_iff_left

protected alias ⟨add_right_cancel, _⟩ := ModEq.add_iff_right
/-
**AddCommGroup.ModEq.add_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Mo
dEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCancelCommMonoid M] {a b p : M} (c : M), c + a
 ≡ c + b [PMOD p] → a ≡ b [PMOD p]
参数：c : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.add_left_cancel`：∀ {M : Type u_1} [inst : AddCancelCo
mmMonoid M] {a b c d p : M},   a ≡ b [PMOD p] → a + c ≡ b + d [PMOD p] → c ≡ d [
PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem add_left_cancel' (c : M) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_left_cancel
/-
**AddCommGroup.ModEq.add_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.M
odEq`。
形式化陈述：∀ {M : Type u_1} [inst : AddCancelCommMonoid M] {a b p : M} (c : M), a + c
 ≡ b + c [PMOD p] → a ≡ b [PMOD p]
参数：c : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.add_right_cancel`：∀ {M : Type u_1} [inst : AddCancelC
ommMonoid M] {a b c d p : M},   c ≡ d [PMOD p] → a + c ≡ b + d [PMOD p] → a ≡ b 
[PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem add_right_cancel' (c : M) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.add_right_cancel

end ModEq

@[simp]
/-
**AddCommGroup.add_modEq_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddCommGroup.ModEq.add_iff_left`：∀ {M : Type u_1} [inst : AddCancelCommM
onoid M] {a b c d p : M},   a ≡ b [PMOD p] → (a + c ≡ b + d [PMOD p] ↔ c ≡ d [PM
OD p])
· 使用定理 `AddCommGroup.modEq_refl`：modEq_refl (a : M) : a ≡ a [PMOD p]
-/
theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by
  simpa using (modEq_refl a).add_iff_left (d := 0)

@[simp]
/-
**AddCommGroup.add_modEq_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [add_comm a]

end AddCancelCommMonoid

section AddCommGroup
variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

/-
**AddCommGroup.modEq_iff_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists m : Int, m • p = b - a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_nsmul`：modEq_iff_nsmul : a ≡ b [PMOD p] ↔ exists 
m n : Nat, m • p + a = n • p + b
· 使用定理 `sub_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m - 
n) • a = m • a + -(n • a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_eq_sub_iff_add_eq_add`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b
 c d : G}, a - b = c - d ↔ a + d = c + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Int.toNat_sub_toNat_neg`：∀ (n : ℤ), ↑n.toNat - ↑(-n).toNat = n
-/
theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := by
  rw [modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]
/-
**AddCommGroup.modEq_iff_zsmul'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ exists m : Int, b - a = m • p
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
theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p := by
  simp only [modEq_iff_zsmul, eq_comm]

@[simp]
/-
**AddCommGroup.neg_modEq_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨ModEq.of_neg, ModEq.neg⟩ := neg_modEq_neg

@[simp]
/-
**AddCommGroup.modEq_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_neg'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ
), n • -a = -n • a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] :=
  modEq_comm.trans <| by simp [modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨ModEq.of_neg', ModEq.neg'⟩ := modEq_neg
/-
**AddCommGroup.modEq_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_sub (a b : G) : a ≡ b [PMOD b - a]
参数：a b : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modEq_sub (a b : G) : a ≡ b [PMOD b - a] :=
  ⟨1, 0, by simp [one_nsmul]⟩

@[simp]
/-
**AddCommGroup.zsmul_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：zsmul_modEq_zero (z : Int) : z • p ≡ 0 [PMOD p]
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_zsmul`：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists 
m : Int, m • p = b - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩
/-
**AddCommGroup.add_zsmul_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：add_zsmul_modEq (z : Int) : a + z • p ≡ a [PMOD p]
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_zsmul`：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists 
m : Int, m • p = b - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩
/-
**AddCommGroup.zsmul_add_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：zsmul_add_modEq (z : Int) : z • p + a ≡ a [PMOD p]
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGroup.modEq_iff_zsmul`：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists 
m : Int, m • p = b - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] :=
  modEq_iff_zsmul.mpr ⟨-z, by simp⟩

namespace ModEq

/-
**AddCommGroup.ModEq.add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (z : ℤ), a ≡ b [PMOD 
p] → a + z • p ≡ b [PMOD p]
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.trans`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b
 c p : M}, a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p]
· 使用定理 `AddCommGroup.add_zsmul_modEq`：add_zsmul_modEq (z : Int) : a + z • p ≡ a 
[PMOD p]
-/
protected theorem add_zsmul (z : ℤ) : a ≡ b [PMOD p] → a + z • p ≡ b [PMOD p] :=
  (add_zsmul_modEq _).trans
/-
**AddCommGroup.ModEq.zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (z : ℤ), a ≡ b [PMOD 
p] → z • p + a ≡ b [PMOD p]
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.trans`：∀ {M : Type u_1} [inst : AddCommMonoid M] {a b
 c p : M}, a ≡ b [PMOD p] → b ≡ c [PMOD p] → a ≡ c [PMOD p]
· 使用定理 `AddCommGroup.zsmul_add_modEq`：zsmul_add_modEq (z : Int) : z • p + a ≡ a 
[PMOD p]
-/
protected theorem zsmul_add (z : ℤ) : a ≡ b [PMOD p] → z • p + a ≡ b [PMOD p] :=
  (zsmul_add_modEq _).trans
/-
**AddCommGroup.ModEq.of_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} {z : ℤ}, a ≡ b [PMOD 
z • p] → a ≡ b [PMOD p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_zsmul`：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists 
m : Int, m • p = b - a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]
/-
**AddCommGroup.ModEq.zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} {z : ℤ}, a ≡ b [PMOD 
p] → z • a ≡ z • b [PMOD z • p]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_zsmul`：modEq_iff_zsmul : a ≡ b [PMOD p] ↔ exists 
m : Int, m • p = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α) (
n : ℤ), n • (a - b) = n • a - n • b
· 使用定理 `mul_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n : 
ℤ), (m * n) • a = m • n • a
· 使用定理 `mul_zsmul'`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n :
 ℤ), (m * n) • a = n • m • a
-/
protected theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub, ← h, ← mul_zsmul, ← mul_zsmul']

end ModEq

@[simp]
/-
**AddCommGroup.zsmul_modEq_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：zsmul_modEq_zsmul [IsAddTorsionFree G] (hn : z != 0) : z • a ≡ z • b [PMOD
 z • p] ↔ a ≡ b [PMOD p]
参数：hn : z != 0。
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
· 使用定理 `zsmul_comm`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n :
 ℤ), n • m • a = m • n • a
· 使用定理 `zsmul_right_inj`：∀ {G : Type u_2} [inst : AddGroup G] [IsAddTorsionFree 
G] {n : ℤ} {a b : G}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zsmul_modEq_zsmul [IsAddTorsionFree G] (hn : z ≠ 0) :
    z • a ≡ z • b [PMOD z • p] ↔ a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul, ← zsmul_sub, zsmul_comm, zsmul_right_inj hn]

alias ⟨ModEq.zsmul_cancel, _⟩ := zsmul_modEq_zsmul

namespace ModEq

@[simp]
/-
**AddCommGroup.ModEq.sub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`
。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a₁ a₂ b₁ b₂ : G},   a₁ ≡ b₁ [P
MOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p])
参数：a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem sub_iff_left (h : a₁ ≡ b₁ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₂ ≡ b₂ [PMOD p] := by
  simp [sub_eq_add_neg, h]

@[simp]
/-
**AddCommGroup.ModEq.sub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq
`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a₁ a₂ b₁ b₂ : G},   a₂ ≡ b₂ [P
MOD p] → (a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p])
参数：a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem sub_iff_right (h : a₂ ≡ b₂ [PMOD p]) :
    a₁ - a₂ ≡ b₁ - b₂ [PMOD p] ↔ a₁ ≡ b₁ [PMOD p] := by
  simp [h, sub_eq_add_neg]

protected alias ⟨sub_left_cancel, sub⟩ := ModEq.sub_iff_left

protected alias ⟨sub_right_cancel, _⟩ := ModEq.sub_iff_right
/-
**AddCommGroup.ModEq.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (c : G), a ≡ b [PMOD 
p] → c - a ≡ c - b [PMOD p]
参数：c : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.sub`：∀ {G : Type u_1} [inst : AddCommGroup G] {p a₁ a
₂ b₁ b₂ : G},   a₁ ≡ b₁ [PMOD p] → a₂ ≡ b₂ [PMOD p] → a₁ - a₂ ≡ b₁ - b₂ [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem sub_left (c : G) (h : a ≡ b [PMOD p]) : c - a ≡ c - b [PMOD p] :=
  modEq_rfl.sub h
/-
**AddCommGroup.ModEq.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.ModEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (c : G), a ≡ b [PMOD 
p] → a - c ≡ b - c [PMOD p]
参数：c : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.sub`：∀ {G : Type u_1} [inst : AddCommGroup G] {p a₁ a
₂ b₁ b₂ : G},   a₁ ≡ b₁ [PMOD p] → a₂ ≡ b₂ [PMOD p] → a₁ - a₂ ≡ b₁ - b₂ [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem sub_right (c : G) (h : a ≡ b [PMOD p]) : a - c ≡ b - c [PMOD p] :=
  h.sub modEq_rfl
/-
**AddCommGroup.ModEq.sub_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.Mo
dEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (c : G), c - a ≡ c - 
b [PMOD p] → a ≡ b [PMOD p]
参数：c : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.sub_left_cancel`：∀ {G : Type u_1} [inst : AddCommGrou
p G] {p a₁ a₂ b₁ b₂ : G},   a₁ ≡ b₁ [PMOD p] → a₁ - a₂ ≡ b₁ - b₂ [PMOD p] → a₂ ≡
 b₂ [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_left_cancel
/-
**AddCommGroup.ModEq.sub_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup.M
odEq`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {p a b : G} (c : G), a - c ≡ b - 
c [PMOD p] → a ≡ b [PMOD p]
参数：c : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.ModEq.sub_right_cancel`：∀ {G : Type u_1} [inst : AddCommGro
up G] {p a₁ a₂ b₁ b₂ : G},   a₂ ≡ b₂ [PMOD p] → a₁ - a₂ ≡ b₁ - b₂ [PMOD p] → a₁ 
≡ b₁ [PMOD p]
· 使用定理 `AddCommGroup.modEq_rfl`：modEq_rfl : a ≡ a [PMOD p]
-/
protected theorem sub_right_cancel' (c : G) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] :=
  modEq_rfl.sub_right_cancel

end ModEq

/-
**AddCommGroup.modEq_sub_iff_add_modEq'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`
。
形式化陈述：modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p]
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [modEq_iff_zsmul', sub_sub]
/-
**AddCommGroup.modEq_sub_iff_add_modEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_sub_iff_add_modEq'`：modEq_sub_iff_add_modEq' : a ≡ b 
- c [PMOD p] ↔ c + a ≡ b [PMOD p]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] :=
  modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]
/-
**AddCommGroup.sub_modEq_iff_modEq_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`
。
形式化陈述：sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `AddCommGroup.modEq_sub_iff_add_modEq'`：modEq_sub_iff_add_modEq' : a ≡ b 
- c [PMOD p] ↔ c + a ≡ b [PMOD p]
-/
theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq'.trans modEq_comm
/-
**AddCommGroup.sub_modEq_iff_modEq_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `AddCommGroup.modEq_sub_iff_add_modEq`：modEq_sub_iff_add_modEq : a ≡ b - 
c [PMOD p] ↔ a + c ≡ b [PMOD p]
-/
theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] :=
  modEq_comm.trans <| modEq_sub_iff_add_modEq.trans modEq_comm

@[simp]
/-
**AddCommGroup.sub_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [sub_modEq_iff_modEq_add]

-- this matches `Int.modEq_iff_add_fac`
/-
**AddCommGroup.modEq_iff_eq_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ exists z : Int, b = a + z • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [modEq_iff_zsmul', sub_eq_iff_eq_add']

-- this roughly matches `Int.modEq_zero_iff_dvd`
/-
**AddCommGroup.modEq_zero_iff_eq_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ exists z : Int, a = z • p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `AddCommGroup.modEq_iff_eq_add_zsmul`：modEq_iff_eq_add_zsmul : a ≡ b [PMO
D p] ↔ exists z : Int, b = a + z • p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ ∃ z : ℤ, a = z • p := by
  rw [modEq_comm, modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]
/-
**AddCommGroup.not_modEq_iff_ne_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrou
p`。
形式化陈述：not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ forall z : Int, b != a + z 
• p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_iff_eq_add_zsmul`：modEq_iff_eq_add_zsmul : a ≡ b [PMO
D p] ↔ exists z : Int, b = a + z • p
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [modEq_iff_eq_add_zsmul, not_exists]

/-- If `a ≡ b [PMOD p]`, then mod `n • p` there are `n` cases. -/
/-
**AddCommGroup.modEq_nsmul_cases** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_nsmul_cases (n : Nat) (hn : n != 0) : a ≡ b [PMOD p] ↔ exists i < n,
 a ≡ b + i • p [PMOD (n • p)]
参数：n : Nat；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
· 使用定理 `Int.ediv_mul_add_emod`：∀ (a b : ℤ), a / b * b + a % b = a

--- 原说明 ---
If `a ≡ b [PMOD p]`, then mod `n • p` there are `n` cases.
-/
theorem modEq_nsmul_cases (n : ℕ) (hn : n ≠ 0) :
    a ≡ b [PMOD p] ↔ ∃ i < n, a ≡ b + i • p [PMOD (n • p)] := by
  simp_rw [← sub_modEq_iff_modEq_add, modEq_comm (b := b)]
  simp_rw [modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

end AddCommGroup

end AddCommGroup

