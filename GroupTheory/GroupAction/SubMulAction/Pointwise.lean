/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise monoid structures on SubMulAction

This file provides `SubMulAction.Monoid` and weaker typeclasses, which show that `SubMulAction`s
inherit the same pointwise multiplications as sets.

To match `Submodule.idemSemiring`, we do not put these in the `Pointwise` locale.

-/

public section


open scoped Pointwise

variable {R M : Type*}

namespace SubMulAction

section One

variable [Monoid R] [MulAction R M] [One M]

/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (SubMulAction R M) where
  one :=
    { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r _ ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }
/-
**SubMulAction.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M) :=
  rfl

@[simp]
/-
**SubMulAction.mem_one** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_one {x : M} : x in (1 : SubMulAction R M) ↔ exists r : R, r • (1 : M) 
= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_one {x : M} : x ∈ (1 : SubMulAction R M) ↔ ∃ r : R, r • (1 : M) = x :=
  Iff.rfl
/-
**SubMulAction.subset_coe_one** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：subset_coe_one : (1 : Set M) subseteq (1 : SubMulAction R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subset_coe_one : (1 : Set M) ⊆ (1 : SubMulAction R M) := fun _ hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩

end One

section Mul

variable [Monoid R] [MulAction R M] [Mul M] [IsScalarTower R M M]

/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (SubMulAction R M) where
  mul p q :=
    { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r _ ⟨m₁, hm₁, m₂, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]
/-
**SubMulAction.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M)
参数：p q : SubMulAction R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl
/-
**SubMulAction.mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_mul {p q : SubMulAction R M} {x : M} : x in p * q ↔ exists y in p, exi
sts z in q, y * z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
-/
theorem mem_mul {p q : SubMulAction R M} {x : M} : x ∈ p * q ↔ ∃ y ∈ p, ∃ z ∈ q, y * z = x :=
  Set.mem_mul

end Mul

section MulOneClass

variable [Monoid R] [MulAction R M] [MulOneClass M] [IsScalarTower R M M] [SMulCommClass R M M]

/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulOneClass (SubMulAction R M) where
  mul_one a := by
    ext x
    simp only [mem_mul, mem_one, mul_smul_comm, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext x
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_exists_eq_and, one_mul]
    refine ⟨?_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

end MulOneClass

section Semigroup

variable [Monoid R] [MulAction R M] [Semigroup M] [IsScalarTower R M M]

/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semigroup (SubMulAction R M) where
  mul_assoc _ _ _ := SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

end Semigroup

section Monoid

variable [Monoid R] [MulAction R M] [Monoid M] [IsScalarTower R M M] [SMulCommClass R M M]

/-
**SubMulAction.** 是 Mathlib 中的一个实例，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (SubMulAction R M) := { }
/-
**SubMulAction.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Monoid R] [inst_1 : MulAction R M]
 [inst_2 : Monoid M]   [inst_3 : IsScalarTower R M M] [inst_4 : SMulCommClass R 
M M] (p : SubMulAction R M) {n : ℕ},   n ≠ 0 → ↑(p ^ n) = ↑p ^ n
参数：p : SubMulAction R M；p ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (p : SubMulAction R M) : ∀ {n : ℕ} (_ : n ≠ 0), ↑(p ^ n) = (p : Set M) ^ n
  | 0, hn => (hn rfl).elim
  | 1, _ => by rw [pow_one, pow_one]
  | n + 2, _ => by
    rw [pow_succ _ (n + 1), pow_succ _ (n + 1), coe_mul, coe_pow _ n.succ_ne_zero]
/-
**SubMulAction.subset_coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Monoid R] [inst_1 : MulAction R M]
 [inst_2 : Monoid M]   [inst_3 : IsScalarTower R M M] [inst_4 : SMulCommClass R 
M M] (p : SubMulAction R M) {n : ℕ}, ↑p ^ n ⊆ ↑(p ^ n)
参数：p : SubMulAction R M；p ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `SubMulAction.subset_coe_one`：subset_coe_one : (1 : Set M) subseteq (1 : 
SubMulAction R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `SubMulAction.coe_pow`：∀ {R : Type u_1} {M : Type u_2} [inst : Monoid R] 
[inst_1 : MulAction R M] [inst_2 : Monoid M]   [inst_3 : IsScalarTower R M M] [i
nst_4 : SM…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem subset_coe_pow (p : SubMulAction R M) : ∀ {n : ℕ}, (p : Set M) ^ n ⊆ ↑(p ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact subset_coe_one
  | n + 1 => by rw [← Nat.succ_eq_add_one, coe_pow _ n.succ_ne_zero]

end Monoid

end SubMulAction

