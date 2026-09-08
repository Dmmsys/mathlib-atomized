/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The degree of rational functions

## Main definitions
We define the degree of a rational function, with values in `ℤ`:
- `intDegree` is the degree of a rational function, defined as the difference between the
  `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
  `intDegree 0 = 0`.
-/

@[expose] public section


noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section IntDegree

open Polynomial

variable [Field K]

/-- `intDegree x` is the degree of the rational function `x`, defined as the difference between
the `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
`intDegree 0 = 0`. -/
/-
**RatFunc.intDegree** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：intDegree (x : K⟮X⟯) : Int
参数：x : K⟮X⟯。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`intDegree x` is the degree of the rational function `x`, defined as the differe
nce between
the `natDegree` of its numerator and the `natDegree` of its denominator. In part
icular,
`intDegree 0 = 0`.
-/
def intDegree (x : K⟮X⟯) : ℤ :=
  natDegree x.num - natDegree x.denom

@[simp]
/-
**RatFunc.intDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_zero : intDegree (0 : K⟮X⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `RatFunc.num_zero`：num_zero : num (0 : K⟮X⟯) = 0
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `RatFunc.denom_zero`：denom_zero : denom (0 : K⟮X⟯) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem intDegree_zero : intDegree (0 : K⟮X⟯) = 0 := by
  rw [intDegree, num_zero, natDegree_zero, denom_zero, natDegree_one, sub_self]

@[simp]
/-
**RatFunc.intDegree_one** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_one : intDegree (1 : K⟮X⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `RatFunc.num_one`：num_one : num (1 : K⟮X⟯) = 1
· 使用定理 `RatFunc.denom_one`：denom_one : denom (1 : K⟮X⟯) = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem intDegree_one : intDegree (1 : K⟮X⟯) = 0 := by
  rw [intDegree, num_one, denom_one, sub_self]

@[simp]
/-
**RatFunc.intDegree_C** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_C (k : K) : intDegree (C k) = 0
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `RatFunc.num_C`：num_C (c : K) : num (C c) = Polynomial.C c
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `RatFunc.denom_C`：denom_C (c : K) : denom (C c) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem intDegree_C (k : K) : intDegree (C k) = 0 := by
  rw [intDegree, num_C, natDegree_C, denom_C, natDegree_one, sub_self]

@[simp]
/-
**RatFunc.intDegree_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_X : intDegree (X : K⟮X⟯) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `RatFunc.num_X`：num_X : num (X : K⟮X⟯) = Polynomial.X
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RatFunc.denom_X`：denom_X : denom (X : K⟮X⟯) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem intDegree_X : intDegree (X : K⟮X⟯) = 1 := by
  rw [intDegree, num_X, Polynomial.natDegree_X, denom_X, Polynomial.natDegree_one,
    Int.ofNat_one, Int.ofNat_zero, sub_zero]

@[simp]
/-
**RatFunc.intDegree_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_polynomial {p : K[X]} : intDegree (algebraMap K[X] K⟮X⟯ p) = nat
Degree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `RatFunc.num_algebraMap`：num_algebraMap (p : K[X]) : num (algebraMap _ _ 
p) = p
· 使用定理 `RatFunc.denom_algebraMap`：denom_algebraMap (p : K[X]) : denom (algebraMa
p _ K⟮X⟯ p) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem intDegree_polynomial {p : K[X]} :
    intDegree (algebraMap K[X] K⟮X⟯ p) = natDegree p := by
  rw [intDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_one,
    Int.ofNat_zero, sub_zero]
/-
**RatFunc.intDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_mul {x y : K⟮X⟯} (hx : x != 0) (hy : y != 0) : intDegree (x * y)
 = intDegree x + intDegree y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_sub_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b c
 : α), a - (b - c) = a + c - b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `RatFunc.num_denom_mul`：num_denom_mul (x y : K⟮X⟯) : (x * y).num * (x.den
om * y.denom) = x.num * y.num * (x * y).denom
-/
theorem intDegree_mul {x y : K⟮X⟯} (hx : x ≠ 0) (hy : y ≠ 0) :
    intDegree (x * y) = intDegree x + intDegree y := by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero, ←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    ← Polynomial.natDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy), ←
    Polynomial.natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (x * y).denom_ne_zero,
    RatFunc.num_denom_mul]

@[simp]
/-
**RatFunc.intDegree_inv** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_inv (x : K⟮X⟯) : intDegree (x⁻¹) = - intDegree x
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `RatFunc.intDegree_zero`：intDegree_zero : intDegree (0 : K⟮X⟯) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.intDegree_mul`：intDegree_mul {x y : K⟮X⟯} (hx : x != 0) (hy : y 
!= 0) : intDegree (x * y) = intDegree x + intDegree y
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RatFunc.intDegree_one`：intDegree_one : intDegree (1 : K⟮X⟯) = 0
-/
theorem intDegree_inv (x : K⟮X⟯) : intDegree (x⁻¹) = - intDegree x := by
  by_cases hx : x = 0 <;> simp [hx, eq_neg_iff_add_eq_zero, ← intDegree_mul (inv_ne_zero hx) hx]
/-
**RatFunc.intDegree_div** 是 Mathlib 中的一个引理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_div {x y : RatFunc K} (hx : x != 0) (hy : y != 0) : (x / y).intD
egree = x.intDegree - y.intDegree
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `RatFunc.intDegree_mul`：intDegree_mul {x y : K⟮X⟯} (hx : x != 0) (hy : y 
!= 0) : intDegree (x * y) = intDegree x + intDegree y
· 使用定理 `RatFunc.intDegree_inv`：intDegree_inv (x : K⟮X⟯) : intDegree (x⁻¹) = - in
tDegree x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
lemma intDegree_div {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).intDegree = x.intDegree - y.intDegree := by
  rw [div_eq_mul_inv, intDegree_mul, intDegree_inv, ← sub_eq_add_neg] <;> grind

@[simp]
/-
**RatFunc.intDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_neg (x : K⟮X⟯) : intDegree (-x) = intDegree x
参数：x : K⟮X⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `RatFunc.intDegree.eq_1`：∀ {K : Type u} [inst : Field K] (x : RatFunc K),
 x.intDegree = ↑x.num.natDegree - ↑x.denom.natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用引理 `Polynomial.natDegree_sub_eq_of_prod_eq`：natDegree_sub_eq_of_prod_eq {p₁ 
p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0) (hp₂ : p₂ != 0) (hq₂ : q₂ != 0)
 (h_eq : p₁ * q₂ = p₂ * q₁) …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `RatFunc.num_denom_neg`：num_denom_neg (x : K⟮X⟯) : (-x).num * x.denom = -
x.num * (-x).denom
-/
theorem intDegree_neg (x : K⟮X⟯) : intDegree (-x) = intDegree x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)
/-
**RatFunc.intDegree_add** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_add {x y : K⟮X⟯} (hxy : x + y != 0) : (x + y).intDegree = (x.num
 * y.denom + x.denom * y.num).natDegree - (x.denom * y.denom).natDegree
参数：hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.natDegree_sub_eq_of_prod_eq`：natDegree_sub_eq_of_prod_eq {p₁ 
p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0) (hp₂ : p₂ != 0) (hq₂ : q₂ != 0)
 (h_eq : p₁ * q₂ = p₂ * q₁) …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `RatFunc.num_mul_denom_add_denom_mul_num_ne_zero`：num_mul_denom_add_denom
_mul_num_ne_zero {x y : K⟮X⟯} (hxy : x + y != 0) : x.num * y.denom + x.denom * y
.num != 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `RatFunc.num_denom_add`：num_denom_add (x y : K⟮X⟯) : (x + y).num * (x.den
om * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom
-/
theorem intDegree_add {x y : K⟮X⟯} (hxy : x + y ≠ 0) :
    (x + y).intDegree =
      (x.num * y.denom + x.denom * y.num).natDegree - (x.denom * y.denom).natDegree :=
  natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)
/-
**RatFunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree** 是 
Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : K⟮X
⟯} (hx : x != 0) {s : K[X]} (hs : s != 0) : ((x.num * s).natDegree : Int) - (s *
 x.denom).natDegree = x.intDegree
参数：hx : x != 0；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.natDegree_sub_eq_of_prod_eq`：natDegree_sub_eq_of_prod_eq {p₁ 
p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁ != 0) (hp₂ : p₂ != 0) (hq₂ : q₂ != 0)
 (h_eq : p₁ * q₂ = p₂ * q₁) …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : K⟮X⟯}
    (hx : x ≠ 0) {s : K[X]} (hs : s ≠ 0) :
    ((x.num * s).natDegree : ℤ) - (s * x.denom).natDegree = x.intDegree := by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]
/-
**RatFunc.intDegree_add_le** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：intDegree_add_le {x y : K⟮X⟯} (hy : y != 0) (hxy : x + y != 0) : intDegree
 (x + y) <= max (intDegree x) (intDegree y)
参数：hy : y != 0；hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.intDegree_zero`：intDegree_zero : intDegree (0 : K⟮X⟯) = 0
· 使用定理 `RatFunc.intDegree_add`：intDegree_add {x y : K⟮X⟯} (hxy : x + y != 0) : (
x + y).intDegree = (x.num * y.denom + x.denom * y.num).natDegree - (x.denom * y.
denom).natD…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegre
e`：natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : K⟮X⟯} 
(hx : x != 0) {s : K[X]} (hs : s != 0) : ((x.num * s).natDegree…
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `sub_le_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a b : α} (c : α), a - c ≤ b - c ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
-/
theorem intDegree_add_le {x y : K⟮X⟯} (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    intDegree (x + y) ≤ max (intDegree x) (intDegree y) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intDegree_add hxy, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero,
    mul_comm y.denom, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero,
    le_max_iff, sub_le_sub_iff_right, Int.ofNat_le, sub_le_sub_iff_right, Int.ofNat_le, ←
    le_max_iff, mul_comm y.num]
  exact natDegree_add_le _ _

end IntDegree

end RatFunc

