/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Conjugacy of group elements

See also `MulAut.conj` and `Quandle.conj`.
-/

@[expose] public section

assert_not_exists MonoidWithZero Multiset MulAction

universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
@[to_additive /-- We say that `a` is additively conjugate to `b` if for some additive unit `c` we
have `c + a + -c = b`. -/]
/-
**IsConj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsConj (a b : α)
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b

@[to_additive (attr := refl)]
/-
**IsConj.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConj.refl (a : α) : IsConj a a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.one_left`：one_left (x : M) : SemiconjBy 1 x x
-/
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩

@[to_additive (attr := symm)]
/-
**IsConj.symm** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.ComplexEmbedding`。
形式化陈述：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
参数：hσ : IsConj φ σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_symm_left`：units_inv_symm_left {a : Mˣ} {x y : M} (
h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x
-/
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩

@[to_additive]
/-
**isConj_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_comm {g h : α} : IsConj g h ↔ IsConj h g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
-/
theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩

@[to_additive (attr := trans)]
/-
**IsConj.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsConj`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {a b c : α}, IsConj a b → IsConj b c → Is
Conj a c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_left`：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b
 x y) : SemiconjBy (a * b) x z
-/
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[to_additive]
/-
**IsConj.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsConj`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {a b : α} (n : ℕ), IsConj a b → IsConj (a
 ^ n) (b ^ n)
参数：n : ℕ；a ^ n；b ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
-/
theorem IsConj.pow {a b : α} (n : ℕ) : IsConj a b → IsConj (a ^ n) (b ^ n)
  | ⟨c, hc⟩ => ⟨c, hc.pow_right n⟩

@[to_additive (attr := simp)]
/-
**isConj_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ 
= c ↔ a = c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
-/
theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc
    exact hc, fun h => by rw [h]⟩

@[to_additive]
/-
**MonoidHom.map_isConj** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Monoid α] [inst_1 : Monoid β] (f : α →
* β) {a b : α},   IsConj a b → IsConj (f a) (f b)
参数：f : α →* β；f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.coe_map`：coe_map (f : M ->* N) (x : Mˣ) : ↑(map f x) = f x
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
-/
protected theorem MonoidHom.map_isConj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩

@[to_additive (attr := simp)]
/-
**isConj_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_one_right {a : α} : IsConj 1 a ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_eq_right`：mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
-/
theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 := by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy, mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

@[to_additive (attr := simp)]
/-
**isConj_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_one_left {a : α} : IsConj a 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
· 使用定理 `isConj_one_right`：isConj_one_right {a : α} : IsConj 1 a ↔ a = 1
-/
theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

end Monoid

section Group

variable [Group α]

@[to_additive (attr := simp)]
/-
**isConj_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻¹ = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[to_additive]
/-
**conj_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ := by
  simp [mul_assoc]

@[to_additive (attr := simp)]
/-
**conj_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by
  simp [mul_assoc]

@[to_additive (attr := simp)]
/-
**conj_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_pow {i : Nat} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `conj_mul`：conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * 
c) * b⁻¹
-/
theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

@[to_additive (attr := simp)]
/-
**conj_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_zpow {i : Int} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `conj_pow`：conj_pow {i : Nat} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i *
 a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

@[to_additive]
/-
**conj_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  fun a b ↦ by simp

end Group

namespace IsConj

/- This small quotient API is largely copied from the API of `Associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `IsConj` iff there is a unit `u` such that `u * x = y * u` -/
@[to_additive (attr := instance_reducible) /-- The setoid of the relation `IsAddConj` iff there
is an additive unit `u` such that `u + x = y + u` -/]
/-
**IsConj.setoid** 是 Mathlib 中的一个定义，位于命名空间 `IsConj`。
形式化陈述：(α : Type u_1) → [Monoid α] → Setoid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

end IsConj

attribute [local instance] IsConj.setoid
attribute [local instance] IsAddConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
@[to_additive /-- The quotient type of additive conjugacy classes of an additive group. -/]
/-
**ConjClasses** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConjClasses (α : Type*) [Monoid α] : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient type of conjugacy classes of a group.
-/
def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)

namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

/-- The canonical quotient map from a monoid `α` into the `ConjClasses` of `α` -/
@[to_additive /-- The canonical quotient map from an additive monoid `α` into the
`AddConjClasses` of `α` -/]
/-
**ConjClasses.mk** 是 Mathlib 中的一个定义，位于命名空间 `ConjClasses`。
形式化陈述：{α : Type u_1} → [inst : Monoid α] → α → ConjClasses α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧

@[to_additive]
/-
**ConjClasses.** 是 Mathlib 中的一个实例，位于命名空间 `ConjClasses`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ConjClasses α) := ⟨⟦1⟧⟩

@[to_additive]
/-
**ConjClasses.mk_eq_mk_iff_isConj** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsCo
nj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotient.exact Quot.sound

@[to_additive]
/-
**ConjClasses.quotient_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl

@[to_additive]
/-
**ConjClasses.quot_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a :=
  rfl

@[to_additive]
/-
**ConjClasses.forall_isConj** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：forall_isConj {p : ConjClasses α -> Prop} : (forall a, p a) ↔ forall a, p 
(ConjClasses.mk a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

@[to_additive]
/-
**ConjClasses.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mk_surjective : Function.Surjective (@ConjClasses.mk α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ConjClasses.forall_isConj`：forall_isConj {p : ConjClasses α -> Prop} : (
forall a, p a) ↔ forall a, p (ConjClasses.mk a)
-/
theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_isConj.2 fun a => ⟨a, rfl⟩

@[to_additive]
/-
**ConjClasses.** 是 Mathlib 中的一个实例，位于命名空间 `ConjClasses`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

@[to_additive]
/-
**ConjClasses.one_eq_mk_one** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl

@[to_additive]
/-
**ConjClasses.exists_rep** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：exists_rep (a : ConjClasses α) : exists a0 : α, ConjClasses.mk a0 = a
参数：a : ConjClasses α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a

/-- A `MonoidHom` maps conjugacy classes of one group to conjugacy classes of another. -/
@[to_additive /-- An `AddMonoidHom` maps additive conjugacy classes of one additive group to
additive conjugacy classes of another. -/]
/-
**ConjClasses.map** 是 Mathlib 中的一个定义，位于命名空间 `ConjClasses`。
形式化陈述：map (f : α ->* β) : ConjClasses α -> ConjClasses β
参数：f : α ->* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)

@[to_additive]
/-
**ConjClasses.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：map_surjective {f : α ->* β} (hf : Function.Surjective f) : Function.Surje
ctive (ConjClasses.map f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConjClasses.mk_surjective`：mk_surjective : Function.Surjective (@ConjCla
sses.mk α _)
-/
theorem map_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note «slow-failing instance priority» /--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
* a class `C` has instances `instT : C T` and `instT' : C T'`;
* types `T` and `T'` are both reducible specializations of another type `S`;
* the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
  instead they have to be found by instance search.

If those conditions hold, the instance `instT` should be assigned lower priority.

Note that there is no issue unless `T` and `T'` are reducibly equal to `S`, Otherwise the instance
discrimination tree can distinguish them, and the note does not apply.

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/

@[to_additive]
/-
**ConjClasses.** 是 Mathlib 中的一个实例，位于命名空间 `ConjClasses`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Certain instances trigger further searches when they are considered as candidate
 instances;
these instances should be assigned a priority lower than the default of 1000 (fo
r example, 900).

The conditions for this rule are as follows:
* a class `C` has instances `instT : C T` and `instT' : C T'`;
* types `T` and `T'` are both reducible specializations of another type `S`;
* the parameters supplied to `S` to produce `T` are not (fully) determined by `i
nstT`,
  instead they have to be found by instance search.

If those conditions hold, the instance `instT` should be assigned lower priority
.

Note that there is no issue unless `T` and `T'` are reducibly equal to `S`, Othe
rwise the instance
discrimination tree can distinguish them, and the note does not apply.

If the type involved is a free variable (rather than an instantiation of some ty
pe `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/
instance [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  inferInstanceAs <| DecidableEq <| Quotient (IsConj.setoid α)

end Monoid

section CommMonoid

variable [CommMonoid α]

@[to_additive]
/-
**ConjClasses.mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mk_injective : Function.Injective (@ConjClasses.mk α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ConjClasses.mk_eq_mk_iff_isConj`：mk_eq_mk_iff_isConj {a b : α} : ConjCla
sses.mk a = ConjClasses.mk b ↔ IsConj a b
· 使用定理 `isConj_iff_eq`：isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsCo
nj a b ↔ a = b
-/
theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

@[to_additive]
/-
**ConjClasses.mk_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mk_bijective : Function.Bijective (@ConjClasses.mk α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConjClasses.mk_injective`：mk_injective : Function.Injective (@ConjClasse
s.mk α _)
· 使用定理 `ConjClasses.mk_surjective`：mk_surjective : Function.Surjective (@ConjCla
sses.mk α _)
-/
theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
@[to_additive /-- The bijection between an `AddCommGroup` and its `AddConjClasses`. -/]
/-
**ConjClasses.mkEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ConjClasses`。
形式化陈述：mkEquiv : α ≃ ConjClasses α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between a `CommGroup` and its `ConjClasses`.
-/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse, Function.LeftInverse, forall_isConj]
    solve_by_elim⟩

end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
@[to_additive /-- Given an element `a`, `addConjugatesOf a` is the set of additive conjugates. -/]
/-
**conjugatesOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conjugatesOf (a : α) : Set α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `a`, `conjugatesOf a` is the set of conjugates.
-/
def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }

@[to_additive]
/-
**mem_conjugatesOf_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_conjugatesOf_self {a : α} : a in conjugatesOf a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
-/
theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a :=
  IsConj.refl _

@[to_additive]
/-
**IsConj.conjugatesOf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conj
ugatesOf b
参数：ab : IsConj a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsConj.trans`：∀ {α : Type u} [inst : Monoid α] {a b c : α}, IsConj a b →
 IsConj b c → IsConj a c
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
-/
theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

@[to_additive]
/-
**isConj_iff_conjugatesOf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conju
gatesOf b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConj.conjugatesOf_eq`：IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a 
b) : conjugatesOf a = conjugatesOf b
· 使用定理 `mem_conjugatesOf_self`：mem_conjugatesOf_self {a : α} : a in conjugatesOf
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
@[to_additive /-- Given an additive conjugacy class `a`, `carrier a` is the set it represents. -/]
/-
**ConjClasses.carrier** 是 Mathlib 中的一个定义，位于命名空间 `ConjClasses`。
形式化陈述：carrier : ConjClasses α -> Set α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsConj.conjugatesOf_eq`：IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a 
b) : conjugatesOf a = conjugatesOf b

--- 原说明 ---
Given a conjugacy class `a`, `carrier a` is the set it represents.
-/
def carrier : ConjClasses α → Set α :=
  Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab

@[to_additive]
/-
**ConjClasses.mem_carrier_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mem_carrier_mk {a : α} : a in carrier (ConjClasses.mk a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
-/
theorem mem_carrier_mk {a : α} : a ∈ carrier (ConjClasses.mk a) :=
  IsConj.refl _

@[to_additive]
/-
**ConjClasses.mem_carrier_iff_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} : a in carrier b ↔ ConjC
lasses.mk a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjClasses.forall_isConj`：forall_isConj {p : ConjClasses α -> Prop} : (
forall a, p a) ↔ forall a, p (ConjClasses.mk a)
· 使用定理 `IsConj.conjugatesOf_eq`：IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a 
b) : conjugatesOf a = conjugatesOf b
· 使用定理 `ConjClasses.carrier.eq_1`：∀ {α : Type u} [inst : Monoid α], ConjClasses.
carrier = Quotient.lift conjugatesOf ⋯
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ConjClasses.mk_eq_mk_iff_isConj`：mk_eq_mk_iff_isConj {a b : α} : ConjCla
sses.mk a = ConjClasses.mk b ↔ IsConj a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ConjClasses.quotient_mk_eq_mk`：quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjCla
sses.mk a
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [forall_isConj]
  intro b
  rw [carrier, eq_comm, mk_eq_mk_iff_isConj, ← quotient_mk_eq_mk, Quotient.lift_mk]
  rfl

@[to_additive]
/-
**ConjClasses.carrier_eq_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹
' {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ConjClasses.mem_carrier_iff_mk_eq`：mem_carrier_iff_mk_eq {a : α} {b : Co
njClasses α} : a in carrier b ↔ ConjClasses.mk a = b
-/
theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun _ => mem_carrier_iff_mk_eq

end ConjClasses

