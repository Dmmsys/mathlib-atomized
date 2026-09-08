/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Ring.Defs

/-!
# Theorems about additively and multiplicatively invertible elements in rings

-/

@[expose] public section

open scoped Ring

variable {R : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

/-- Multiplying an additive unit from the left produces another additive unit. -/
/-
**AddUnits.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddUnits`。
形式化陈述：{R : Type u_1} → [inst : NonUnitalNonAssocSemiring R] → AddUnits R → R → A
ddUnits R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying an additive unit from the left produces another additive unit.
-/
@[simps] def AddUnits.mulLeft : AddUnits R where
  val := y * x.val
  neg := y * x.neg
  val_neg := by simp [← mul_add]
  neg_val := by simp [← mul_add]

/-- Multiplying an additive unit from the right produces another additive unit. -/
/-
**AddUnits.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddUnits`。
形式化陈述：{R : Type u_1} → [inst : NonUnitalNonAssocSemiring R] → AddUnits R → R → A
ddUnits R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying an additive unit from the right produces another additive unit.
-/
@[simps] def AddUnits.mulRight : AddUnits R where
  val := x.val * y
  neg := x.neg * y
  val_neg := by simp [← add_mul]
  neg_val := by simp [← add_mul]

variable {x y}
/-
**AddUnits.neg_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLeft y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLeft y := rfl
/-
**AddUnits.neg_mulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddUnits.neg_mulRight : -(x.mulRight y) = (-x).mulRight y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddUnits.neg_mulRight : -(x.mulRight y) = (-x).mulRight y := rfl
/-
**AddUnits.neg_mul_eq_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddUnits.neg_mul_eq_mul_neg {x y : AddUnits R} : (↑(-x) * y : R) = x * ↑(-
y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddUnits.neg_eq_val_neg`：∀ {α : Type u} [inst : AddMonoid α] (a : AddUni
ts α), a.neg = ↑(-a)
· 使用定理 `AddUnits.val_neg_mulRight`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSem
iring R] (x : AddUnits R) (y : R), ↑(-x.mulRight y) = x.neg * y
· 使用定理 `AddUnits.neg_eq_of_add_eq_zero_left`：∀ {α : Type u} [inst : AddMonoid α]
 {u : AddUnits α} {a : α}, a + ↑u = 0 → ↑(-u) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddUnits.val_mulRight`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemirin
g R] (x : AddUnits R) (y : R), ↑(x.mulRight y) = ↑x * y
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `AddUnits.neg_add`：∀ {α : Type u} [inst : AddMonoid α] (a : AddUnits α), 
↑(-a) + ↑a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AddUnits.neg_mul_eq_mul_neg {x y : AddUnits R} : (↑(-x) * y : R) = x * ↑(-y) := by
  rw [← neg_eq_val_neg, ← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]
/-
**AddUnits.neg_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddUnits.neg_mul_neg {x y : AddUnits R} : ↑(-x) * ↑(-y) = (x * y : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddUnits.val_mulLeft`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring
 R] (x : AddUnits R) (y : R), ↑(x.mulLeft y) = y * ↑x
· 使用定理 `AddUnits.ext_iff`：∀ {α : Type u} [inst : AddMonoid α] {u v : AddUnits α}
, u = v ↔ ↑u = ↑v
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `AddUnits.neg_mulLeft`：AddUnits.neg_mulLeft : -(x.mulLeft y) = (-x).mulLe
ft y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `AddUnits.ext`：∀ {α : Type u} [inst : AddMonoid α] {u v : AddUnits α}, ↑u
 = ↑v → u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddUnits.neg_mul_eq_mul_neg`：AddUnits.neg_mul_eq_mul_neg {x y : AddUnits
 R} : (↑(-x) * y : R) = x * ↑(-y)
· 使用定理 `AddUnits.val_neg_mulLeft`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemi
ring R] (x : AddUnits R) (y : R), ↑(-x.mulLeft y) = y * x.neg
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AddUnits.neg_mul_neg {x y : AddUnits R} : ↑(-x) * ↑(-y) = (x * y : R) := by
  rw [← val_mulLeft, ← val_mulLeft, ← AddUnits.ext_iff, ← neg_inj, ← y.neg_mulLeft, neg_neg]
  apply AddUnits.ext
  simp [neg_mul_eq_mul_neg]
/-
**IsAddUnit.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAddUnit.mul_left {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (y * x)
参数：h : IsAddUnit x；y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddUnits.isAddUnit`：∀ {M : Type u_1} [inst : AddMonoid M] (u : AddUnits 
M), IsAddUnit ↑u
-/
theorem IsAddUnit.mul_left {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (y * x) :=
  (h.addUnit.mulLeft y).isAddUnit
/-
**IsAddUnit.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAddUnit.mul_right {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (x * y)
参数：h : IsAddUnit x；y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddUnits.isAddUnit`：∀ {M : Type u_1} [inst : AddMonoid M] (u : AddUnits 
M), IsAddUnit ↑u
-/
theorem IsAddUnit.mul_right {x : R} (h : IsAddUnit x) (y : R) : IsAddUnit (x * y) :=
  (h.addUnit.mulRight y).isAddUnit

end NonUnitalNonAssocSemiring

/-- `-⅟a` is the inverse of `-a` -/
@[instance_reducible]
/-
**invertibleNeg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleNeg [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a] : I
nvertible (-a)
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`-⅟a` is the inverse of `-a`
-/
def invertibleNeg [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a] : Invertible (-a) :=
  ⟨-⅟a, by simp, by simp⟩

@[simp]
/-
**invOf_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible 
(-a)] : ⅟(-a) = -⅟a
参数：a : R；-a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOf_neg [Monoid R] [HasDistribNeg R] (a : R) [Invertible a] [Invertible (-a)] :
    ⅟(-a) = -⅟a :=
  invOf_eq_right_inv (by simp)

@[simp]
/-
**one_sub_invOf_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 - (⅟2 : R) = ⅟2
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 - (⅟2 : R) = ⅟2 :=
  (isUnit_of_invertible (2 : R)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, ← one_add_one_eq_two, add_sub_cancel_right]

@[simp]
/-
**invOf_two_add_invOf_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_two_add_invOf_two [NonAssocSemiring R] [Invertible (2 : R)] : (⅟2 : 
R) + (⅟2 : R) = 1
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
-/
theorem invOf_two_add_invOf_two [NonAssocSemiring R] [Invertible (2 : R)] :
    (⅟2 : R) + (⅟2 : R) = 1 := by rw [← two_mul, mul_invOf_self]
/-
**pos_of_invertible_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_invertible_cast [NonAssocSemiring R] [Nontrivial R] (n : Nat) [Inve
rtible (n : R)] : 0 < n
参数：n : Nat；n : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pos_of_invertible_cast [NonAssocSemiring R] [Nontrivial R] (n : ℕ) [Invertible (n : R)] :
    0 < n :=
  Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)
/-
**invOf_add_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [Invertible b] : ⅟a 
+ ⅟b = ⅟a * (a + b) * ⅟b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a + ⅟b = ⅟a * (a + b) * ⅟b := by
  rw [mul_add, invOf_mul_self, add_mul, one_mul, mul_assoc, mul_invOf_self, mul_one, add_comm]

/-- A version of `inv_sub_inv'` for `invOf`. -/
/-
**invOf_sub_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Invertible b] : ⅟a - ⅟b
 = ⅟a * (b - a) * ⅟b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
A version of `inv_sub_inv'` for `invOf`.
-/
theorem invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Invertible b] :
    ⅟a - ⅟b = ⅟a * (b - a) * ⅟b := by
  rw [mul_sub, invOf_mul_self, sub_mul, one_mul, mul_assoc, mul_invOf_self, mul_one]
/-
**neg_add_eq_mul_invOf_mul_same_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_add_eq_mul_invOf_mul_same_iff [Ring R] {a b : R} [Invertible a] [Inver
tible b] : -(b + a) = a * ⅟b * a ↔ -1 = ⅟a * b + ⅟b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `add_neg_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 a + b + -a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
· 使用定理 `invOf_mul_cancel_left'`：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a *
 (a * b) = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma neg_add_eq_mul_invOf_mul_same_iff [Ring R] {a b : R} [Invertible a] [Invertible b] :
    -(b + a) = a * ⅟b * a ↔ -1 = ⅟a * b + ⅟b * a :=
  calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h ↦ by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h ↦ by simpa using congr_arg (⅟a * ·) h, fun h ↦ by simp [← h]⟩
/-
**neg_one_eq_invOf_mul_add_invOf_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_eq_invOf_mul_add_invOf_mul_iff [Ring R] {a b : R} [Invertible a] [
Invertible b] [Invertible (a + b)] : ⅟(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a * b + ⅟b * a
参数：a + b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_inj_of_invertible`：mul_left_inj_of_invertible : a * c = b * c ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma neg_one_eq_invOf_mul_add_invOf_mul_iff [Ring R] {a b : R} [Invertible a]
    [Invertible b] [Invertible (a + b)] : ⅟(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a * b + ⅟b * a := by
  calc ⅟(a + b) = ⅟a + ⅟b
      ↔ ⅟(a + b) * (a + b) = (⅟a + ⅟b) * (a + b) := by rw [mul_left_inj_of_invertible]
    _ ↔ 1 = ⅟a * a + ⅟b * a + (⅟a * b + ⅟b * b) := by rw [invOf_mul_self, mul_add, add_mul, add_mul]
    _ ↔ 1 = 1 + ⅟b * a + (1 + ⅟a * b) := by rw [invOf_mul_self, invOf_mul_self, add_comm _ 1]
    _ ↔ 1 = 1 + 1 + ⅟b * a + ⅟a * b := by rw [← add_assoc, add_comm _ 1, ← add_assoc]
    _ ↔ -2 + 1 = -2 + (2 + ⅟b * a + ⅟a * b) := by rw [one_add_one_eq_two, add_right_inj]
    _ ↔ -2 + 1 = ⅟b * a + ⅟a * b := by rw [← add_assoc, ← add_assoc, neg_add_cancel, zero_add]
    _ ↔ -1 + 0 = ⅟b * a + ⅟a * b := by rw [← one_add_one_eq_two, neg_add, add_assoc, neg_add_cancel]
    _ ↔ -1 = ⅟a * b + ⅟b * a := by rw [add_zero, add_comm]
/-
**eq_of_invOf_add_eq_invOf_add_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Inve
rtible b] [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) : a * ⅟b * a = b * ⅟a * 
b
参数：a + b；h : ⅟(a + b) = ⅟a + ⅟b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `neg_one_eq_invOf_mul_add_invOf_mul_iff`：neg_one_eq_invOf_mul_add_invOf_m
ul_iff [Ring R] {a b : R} [Invertible a] [Invertible b] [Invertible (a + b)] : ⅟
(a + b) = ⅟a + ⅟b ↔ -1 = ⅟a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `neg_add_eq_mul_invOf_mul_same_iff`：neg_add_eq_mul_invOf_mul_same_iff [Ri
ng R] {a b : R} [Invertible a] [Invertible b] : -(b + a) = a * ⅟b * a ↔ -1 = ⅟a 
* b + ⅟b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_invOf_add_eq_invOf_add_invOf [Ring R] {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h' := neg_one_eq_invOf_mul_add_invOf_mul_iff.mp h
  have h_a_binv_a : -(b + a) = a * ⅟b * a := neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h'
    exact neg_add_eq_mul_invOf_mul_same_iff.mpr h'
  rw [← h_a_binv_a, ← h_b_ainv_b, add_comm]

/-- A version of `inv_add_inv'` for `Ring.inverse`. -/
/-
**Ring.inverse_add_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_add_inverse [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b) 
: a⁻¹ʳ + b⁻¹ʳ = a⁻¹ʳ * (a + b) * b⁻¹ʳ
参数：h : IsUnit a ↔ IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_add_invOf`：invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [
Invertible b] : ⅟a + ⅟b = ⅟a * (a + b) * ⅟b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
A version of `inv_add_inv'` for `Ring.inverse`.
-/
theorem Ring.inverse_add_inverse [Semiring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ + b⁻¹ʳ = a⁻¹ʳ * (a + b) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

/-- A version of `inv_sub_inv'` for `Ring.inverse`. -/
/-
**Ring.inverse_sub_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) : a⁻
¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ
参数：h : IsUnit a ↔ IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.nonempty_invertible`：IsUnit.nonempty_invertible [Monoid α] {a : α
} (h : IsUnit a) : Nonempty (Invertible a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_sub_invOf`：invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Inve
rtible b] : ⅟a - ⅟b = ⅟a * (b - a) * ⅟b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
A version of `inv_sub_inv'` for `Ring.inverse`.
-/
theorem Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]
