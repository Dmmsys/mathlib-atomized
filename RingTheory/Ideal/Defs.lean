/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Tactic.Abel

/-!

# Ideals over a ring

This file defines `Ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

/-- A (left) ideal in a semiring `R` is an additive submonoid `s` such that
`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup. -/
/-
**Ideal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal (R : Type u) [Semiring R]
参数：R : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (left) ideal in a semiring `R` is an additive submonoid `s` such that
`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup
.
-/
abbrev Ideal (R : Type u) [Semiring R] :=
  Submodule R R

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- A left ideal `I : Ideal R` is two-sided if it is also a right ideal. -/
/-
**Ideal.IsTwoSided** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{α : Type u} → [inst : Semiring α] → Ideal α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left ideal `I : Ideal R` is two-sided if it is also a right ideal.
-/
@[mk_iff] class IsTwoSided : Prop where
  mul_mem_of_left {a : α} (b : α) : a ∈ I → a * b ∈ I
/-
**Ideal.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
参数：I : Ideal α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
protected theorem zero_mem : (0 : α) ∈ I :=
  Submodule.zero_mem I
/-
**Ideal.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α}, a ∈ I → b ∈ I 
→ a + b ∈ I
参数：I : Ideal α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
protected theorem add_mem : a ∈ I → b ∈ I → a + b ∈ I :=
  Submodule.add_mem I

variable (a)
/-
**Ideal.mul_mem_left** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mul_mem_left : b in I -> a * b in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem mul_mem_left : b ∈ I → a * b ∈ I :=
  Submodule.smul_mem I a
/-
**Ideal.mul_mem_right** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I : Ideal α) [I.IsTwoSided
] (h : a in I) : a * b in I
参数：b : α；I : Ideal α；h : a in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsTwoSided.mul_mem_of_left`：∀ {α : Type u} {inst : Semiring α} {I 
: Ideal α} [self : I.IsTwoSided] {a : α} (b : α), a ∈ I → a * b ∈ I
-/
theorem mul_mem_right {α} {a : α} (b : α) [Semiring α] (I : Ideal α) [I.IsTwoSided]
    (h : a ∈ I) : a * b ∈ I :=
  IsTwoSided.mul_mem_of_left b h

variable {a}

@[ext]
/-
**Ideal.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
参数：h : forall x, x in I ↔ x in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {I J : Ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h

@[simp]
/-
**Ideal.unit_mul_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x in I ↔ x in I
参数：hy : IsUnit y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x ∈ I ↔ x ∈ I := by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this
/-
**Ideal.pow_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n) : a ^ n in I
参数：ha : a in I；n : Nat；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem pow_mem_of_mem (ha : a ∈ I) (n : ℕ) (hn : 0 < n) : a ^ n ∈ I :=
  Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn
/-
**Ideal.pow_mem_of_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_mem_of_pow_mem {m n : Nat} (ha : a ^ m in I) (h : m <= n) : a ^ n in I
参数：ha : a ^ m in I；h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem pow_mem_of_pow_mem {m n : ℕ} (ha : a ^ m ∈ I) (h : m ≤ n) : a ^ n ∈ I := by
  rw [← Nat.add_sub_of_le h, add_comm, pow_add]
  exact I.mul_mem_left _ ha

end Ideal

/-- For two elements `m` and `m'` in an `R`-module `M`, the set of elements `r : R` with
equal scalar product with `m` and `m'` is an ideal of `R`. If `M` is a group, this coincides
with the kernel of `LinearMap.toSpanSingleton R M (m - m')`. -/
/-
**Module.eqIdeal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.eqIdeal (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' :
 M) : Ideal R where carrier
参数：R；m m' : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two elements `m` and `m'` in an `R`-module `M`, the set of elements `r : R` 
with
equal scalar product with `m` and `m'` is an ideal of `R`. If `M` is a group, th
is coincides
with the kernel of `LinearMap.toSpanSingleton R M (m - m')`.
-/
def Module.eqIdeal (R) {M} [Semiring R] [AddCommMonoid M] [Module R M] (m m' : M) : Ideal R where
  carrier := {r : R | r • m = r • m'}
  add_mem' h h' := by simpa [add_smul] using congr($h + $h')
  zero_mem' := by simp_rw [Set.mem_ofPred, zero_smul]
  smul_mem' _ _ h := by simpa [mul_smul] using congr(_ • $h)

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : I.IsTwoSided := ⟨fun b ha ↦ mul_comm b _ ▸ I.smul_mem _ ha⟩
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [CommRing α] (I : Ideal α) : I.IsTwoSided := inferInstance

@[simp]
/-
**Ideal.mul_unit_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y in I ↔ x in I
参数：hy : IsUnit y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.unit_mul_mem_iff_mem`：unit_mul_mem_iff_mem {x y : α} (hy : IsUnit 
y) : y * x in I ↔ x in I
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y ∈ I ↔ x ∈ I :=
  mul_comm y x ▸ unit_mul_mem_iff_mem I hy
/-
**Ideal.mem_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：mem_of_dvd (hab : a ∣ b) (ha : a in I) : b in I
参数：hab : a ∣ b；ha : a in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_of_dvd (hab : a ∣ b) (ha : a ∈ I) : b ∈ I := by
  obtain ⟨c, rfl⟩ := hab; exact I.mul_mem_right _ ha

end Ideal

end CommSemiring

section Ring

namespace Ideal

variable [Ring α] (I : Ideal α) {a b c d : α}

/-
**Ideal.neg_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a : α}, -a ∈ I ↔ a ∈ I
参数：I : Ideal α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
-/
protected theorem neg_mem_iff : -a ∈ I ↔ a ∈ I :=
  Submodule.neg_mem_iff I
/-
**Ideal.add_mem_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, b ∈ I → (a + b ∈ I
 ↔ a ∈ I)
参数：I : Ideal α；a + b ∈ I ↔ a ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem_iff_left`：∀ {R : Type u} {M : Type v} [inst : Ring R] 
[inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {
x y : M}, y ∈ p …
-/
protected theorem add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) :=
  Submodule.add_mem_iff_left I
/-
**Ideal.add_mem_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a ∈ I → (a + b ∈ I
 ↔ b ∈ I)
参数：I : Ideal α；a + b ∈ I ↔ b ∈ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …
-/
protected theorem add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) :=
  Submodule.add_mem_iff_right I
/-
**Ideal.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a ∈ I → b ∈ I → a 
- b ∈ I
参数：I : Ideal α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
-/
protected theorem sub_mem : a ∈ I → b ∈ I → a - b ∈ I :=
  Submodule.sub_mem I
/-
**Ideal.mul_sub_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mul_sub_mul_mem [I.IsTwoSided] (h1 : a - b in I) (h2 : c - d in I) : a * c
 - b * d in I
参数：h1 : a - b in I；h2 : c - d in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `_private.Mathlib.RingTheory.Ideal.Defs.0.Ideal.mul_sub_mul_mem._abel_1_1
`：∀ {α : Type u_1} [inst : Ring α] {a b c d : α}, a * c - b * d = a * c - b * c 
+ (b * c - b * d)
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
-/
theorem mul_sub_mul_mem [I.IsTwoSided]
    (h1 : a - b ∈ I) (h2 : c - d ∈ I) : a * c - b * d ∈ I := by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul, mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

section inertia

variable (G : Type*) [Group G] [MulAction G α] (I : Ideal α)

/-- The subgroup of elements `g` of `G` such that `∀ x, g • x - x ∈ I`. -/
/-
**Ideal.inertia** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal`。
形式化陈述：inertia : Subgroup G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of elements `g` of `G` such that `∀ x, g • x - x ∈ I`.
-/
abbrev inertia : Subgroup G := I.toAddSubgroup.inertia G

variable {I G} in
/-
**Ideal.coe_mem_inertia** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ in I.inertia G ↔ σ in I.iner
tia H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubgroup.coe_mem_inertia`：coe_mem_inertia {H : Subgroup G} {σ : H} : 
↑σ in I.inertia G ↔ σ in I.inertia H
-/
theorem coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ ∈ I.inertia G ↔ σ ∈ I.inertia H :=
  I.toAddSubgroup.coe_mem_inertia

end inertia

end Ideal

end Ring

