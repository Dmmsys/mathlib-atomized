/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`Set.Icc`, `Set.Ioc`, `Set.Ioc`, and `Set.Ioo`) from `0` to `1`.
Note: Instances for the interval `Ici 0` are dealt with in
`Mathlib/Algebra/Order/Nonneg/Basic.lean`.

## Main definitions

The strongest typeclass provided on each interval is:
* `Set.Icc.commMonoidWithZero`
* `Set.Icc.instIsCancelMulZero`
* `Set.Ico.commSemigroup`
* `Set.Ioc.commMonoid`
* `Set.Ioo.commSemigroup`

## TODO

* algebraic instances for intervals -1 to 1
* algebraic instances for `Ici 1`
* algebraic instances for `(Ioo (-1) 1)ᶜ`
* provide `distribNeg` instances where applicable
* prove versions of `mul_le_{left,right}` for other intervals
* prove versions of the lemmas in `Topology/UnitInterval` with `ℝ` generalized to
  some arbitrary ordered semiring
-/

@[expose] public section

assert_not_exists RelIso

open Set

variable {R : Type*}

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-! ### Instances for `↥(Set.Icc 0 1)` -/


namespace Set.Icc

/-
**Set.Icc.instZero** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instZero : Zero (Icc (0 : R) 1) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (Icc (0 : R) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩
/-
**Set.Icc.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instOne : One (Icc (0 : R) 1) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (Icc (0 : R) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩
/-
**Set.Icc.instZeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instZeroLEOneClass : ZeroLEOneClass (Icc (0 : R) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
instance instZeroLEOneClass : ZeroLEOneClass (Icc (0 : R) 1) := ⟨Subtype.coe_le_coe.mp zero_le_one⟩

@[simp, norm_cast]
/-
**Set.Icc.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_zero : ↑(0 : Icc (0 : R) 1) = (0 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : Icc (0 : R) 1) = (0 : R) :=
  rfl

@[simp, norm_cast]
/-
**Set.Icc.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_one : ↑(1 : Icc (0 : R) 1) = (1 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : Icc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
/-
**Set.Icc.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：mk_zero (h : (0 : R) in Icc (0 : R) 1) : (⟨0, h⟩ : Icc (0 : R) 1) = 0
参数：h : (0 : R) in Icc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zero (h : (0 : R) ∈ Icc (0 : R) 1) : (⟨0, h⟩ : Icc (0 : R) 1) = 0 :=
  rfl

@[simp, grind =]
/-
**Set.Icc.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：mk_one (h : (1 : R) in Icc (0 : R) 1) : (⟨1, h⟩ : Icc (0 : R) 1) = 1
参数：h : (1 : R) in Icc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one (h : (1 : R) ∈ Icc (0 : R) 1) : (⟨1, h⟩ : Icc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Set.Icc.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x = 0
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff
/-
**Set.Icc.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_ne_zero {x : Icc (0 : R) 1} : (x : R) != 0 ↔ x != 0
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.Icc.coe_eq_zero`：coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x =
 0
-/
theorem coe_ne_zero {x : Icc (0 : R) 1} : (x : R) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
/-
**Set.Icc.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff
/-
**Set.Icc.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_ne_one {x : Icc (0 : R) 1} : (x : R) != 1 ↔ x != 1
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.Icc.coe_eq_one`：coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1
-/
theorem coe_ne_one {x : Icc (0 : R) 1} : (x : R) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsOrderedRing R] in
/-
**Set.Icc.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_nonneg (x : Icc (0 : R) 1) : 0 <= (x : R)
参数：x : Icc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_nonneg (x : Icc (0 : R) 1) : 0 ≤ (x : R) :=
  x.2.1

omit [IsOrderedRing R] in
/-
**Set.Icc.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_le_one (x : Icc (0 : R) 1) : (x : R) <= 1
参数：x : Icc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_le_one (x : Icc (0 : R) 1) : (x : R) ≤ 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Icc (0:R) 1`. -/
/-
**Set.Icc.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：nonneg {t : Icc (0 : R) 1} : 0 <= t
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `coe_nonneg`, but with the inequality in `Icc (0:R) 1`.
-/
theorem nonneg {t : Icc (0 : R) 1} : 0 ≤ t :=
  t.2.1

/-- like `coe_le_one`, but with the inequality in `Icc (0:R) 1`. -/
/-
**Set.Icc.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：le_one {t : Icc (0 : R) 1} : t <= 1
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `coe_le_one`, but with the inequality in `Icc (0:R) 1`.
-/
theorem le_one {t : Icc (0 : R) 1} : t ≤ 1 :=
  t.2.2
/-
**Set.Icc.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instMul : Mul (Icc (0 : R) 1) where mul p q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (Icc (0 : R) 1) where
  mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one₀ p.2.2 q.2.1 q.2.2⟩⟩
/-
**Set.Icc.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instPow : Pow (Icc (0 : R) 1) Nat where pow p n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow : Pow (Icc (0 : R) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one₀ p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
/-
**Set.Icc.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R)
参数：x y : Icc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
/-
**Set.Icc.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_pow (x : Icc (0 : R) 1) (n : Nat) : ↑(x ^ n) = ((x : R) ^ n)
参数：x : Icc (0 : R) 1；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (x : Icc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl
/-
**Set.Icc.mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：mul_le_left {x y : Icc (0 : R) 1} : x * y <= x
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_le_left {x y : Icc (0 : R) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one _)
/-
**Set.Icc.mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：mul_le_right {x y : Icc (0 : R) 1} : x * y <= y
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_le_right {x y : Icc (0 : R) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul _)
/-
**Set.Icc.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instMonoidWithZero : MonoidWithZero (Icc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero : MonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow
/-
**Set.Icc.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instCommMonoidWithZero {R : Type*} [CommSemiring R] [PartialOrder R] [IsOr
deredRing R] : CommMonoidWithZero (Icc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommMonoidWithZero (Icc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow
/-
**Set.Icc.instIsCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：instIsCancelMulZero {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R
] [NoZeroDivisors R] : IsCancelMulZero (Icc (0 : R) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Set.Icc.coe_zero`：coe_zero : ↑(0 : Icc (0 : R) 1) = (0 : R)
· 使用定理 `Set.Icc.coe_mul`：coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R)
· 使用引理 `NoZeroDivisors.toIsCancelMulZero`：NoZeroDivisors.toIsCancelMulZero [NonU
nitalNonAssocRing α] [NoZeroDivisors α] : IsCancelMulZero α where mul_left_cance
l_of_ne_zero ha
-/
instance instIsCancelMulZero {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [NoZeroDivisors R] :
    IsCancelMulZero (Icc (0 : R) 1) :=
  @Function.Injective.isCancelMulZero _ R _ _ _ _ _ Subtype.coe_injective coe_zero coe_mul
    NoZeroDivisors.toIsCancelMulZero

/-- The coercion from `Set.Icc 0 1` as a `MonoidWithZeroHom`. -/
@[simps]
/-
**Set.Icc.coeMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `Set.Icc`。
形式化陈述：coeMonoidWithZeroHom : (Icc (0 : R) 1) ->*₀ R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc.coe_mul`：coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R)

--- 原说明 ---
The coercion from `Set.Icc 0 1` as a `MonoidWithZeroHom`.
-/
def coeMonoidWithZeroHom : (Icc (0 : R) 1) →*₀ R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl
  map_zero' := rfl

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]
/-
**Set.Icc.one_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：one_sub_mem {t : β} (ht : t in Icc (0 : β) 1) : 1 - t in Icc (0 : β) 1
参数：ht : t in Icc (0 : β) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_le_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] (a : α) {b : α}, a - b ≤ a ↔ 0 ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem one_sub_mem {t : β} (ht : t ∈ Icc (0 : β) 1) : 1 - t ∈ Icc (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩
/-
**Set.Icc.mem_iff_one_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：mem_iff_one_sub_mem {t : β} : t in Icc (0 : β) 1 ↔ 1 - t in Icc (0 : β) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc.one_sub_mem`：one_sub_mem {t : β} (ht : t in Icc (0 : β) 1) : 1 -
 t in Icc (0 : β) 1
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem mem_iff_one_sub_mem {t : β} : t ∈ Icc (0 : β) 1 ↔ 1 - t ∈ Icc (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩
/-
**Set.Icc.one_sub_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：one_sub_nonneg (x : Icc (0 : β) 1) : 0 <= 1 - (x : β)
参数：x : Icc (0 : β) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_sub_nonneg (x : Icc (0 : β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2
/-
**Set.Icc.one_sub_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) <= 1
参数：x : Icc (0 : β) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1

end Set.Icc

/-! ### Instances for `↥(Set.Ico 0 1)` -/


namespace Set.Ico

/-
**Set.Ico.instZero** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：instZero [Nontrivial R] : Zero (Ico (0 : R) 1) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Nontrivial R] : Zero (Ico (0 : R) 1) where zero := ⟨0, by simp⟩

@[simp, norm_cast]
/-
**Set.Ico.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_zero [Nontrivial R] : ↑(0 : Ico (0 : R) 1) = (0 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero [Nontrivial R] : ↑(0 : Ico (0 : R) 1) = (0 : R) :=
  rfl

@[simp, grind =]
/-
**Set.Ico.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：mk_zero [Nontrivial R] (h : (0 : R) in Ico (0 : R) 1) : (⟨0, h⟩ : Ico (0 :
 R) 1) = 0
参数：h : (0 : R) in Ico (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zero [Nontrivial R] (h : (0 : R) ∈ Ico (0 : R) 1) : (⟨0, h⟩ : Ico (0 : R) 1) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Set.Ico.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_eq_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) = 0 ↔ x = 0
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff
/-
**Set.Ico.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_ne_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) != 0 ↔ x != 0
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.Ico.coe_eq_zero`：coe_eq_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x
 : R) = 0 ↔ x = 0
-/
theorem coe_ne_zero [Nontrivial R] {x : Ico (0 : R) 1} : (x : R) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

omit [IsOrderedRing R] in
/-
**Set.Ico.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_nonneg (x : Ico (0 : R) 1) : 0 <= (x : R)
参数：x : Ico (0 : R) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_nonneg (x : Ico (0 : R) 1) : 0 ≤ (x : R) :=
  x.2.1

omit [IsOrderedRing R] in
/-
**Set.Ico.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_lt_one (x : Ico (0 : R) 1) : (x : R) < 1
参数：x : Ico (0 : R) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_lt_one (x : Ico (0 : R) 1) : (x : R) < 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Ico (0:R) 1`. -/
/-
**Set.Ico.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：nonneg [Nontrivial R] {t : Ico (0 : R) 1} : 0 <= t
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `coe_nonneg`, but with the inequality in `Ico (0:R) 1`.
-/
theorem nonneg [Nontrivial R] {t : Ico (0 : R) 1} : 0 ≤ t :=
  t.2.1
/-
**Set.Ico.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：instMul : Mul (Ico (0 : R) 1) where mul p q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (Ico (0 : R) 1) where
  mul p q :=
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]
/-
**Set.Ico.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：coe_mul (x y : Ico (0 : R) 1) : ↑(x * y) = (x * y : R)
参数：x y : Ico (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : Ico (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl
/-
**Set.Ico.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：instSemigroup : Semigroup (Ico (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup : Semigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul
/-
**Set.Ico.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrdered
Ring R] : CommSemigroup (Ico (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] :
    CommSemigroup (Ico (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ico 0 1` as a `MulHom`. -/
@[simps]
/-
**Set.Ico.coeMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Set.Ico`。
形式化陈述：coeMulHom : (Ico (0 : R) 1) ->ₙ* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico.coe_mul`：coe_mul (x y : Ico (0 : R) 1) : ↑(x * y) = (x * y : R)

--- 原说明 ---
The coercion from `Set.Ico 0 1` as a `MulHom`.
-/
def coeMulHom : (Ico (0 : R) 1) →ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

end Set.Ico

end OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-! ### Instances for `↥(Set.Ioc 0 1)` -/


namespace Set.Ioc

/-
**Set.Ioc.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instOne : One (Ioc (0 : R) 1) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (Ioc (0 : R) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]
/-
**Set.Ioc.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_one : ↑(1 : Ioc (0 : R) 1) = (1 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : Ioc (0 : R) 1) = (1 : R) :=
  rfl

@[simp, grind =]
/-
**Set.Ioc.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：mk_one (h : (1 : R) in Ioc (0 : R) 1) : (⟨1, h⟩ : Ioc (0 : R) 1) = 1
参数：h : (1 : R) in Ioc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one (h : (1 : R) ∈ Ioc (0 : R) 1) : (⟨1, h⟩ : Ioc (0 : R) 1) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Set.Ioc.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_eq_one {x : Ioc (0 : R) 1} : (x : R) = 1 ↔ x = 1
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_one {x : Ioc (0 : R) 1} : (x : R) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff
/-
**Set.Ioc.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_ne_one {x : Ioc (0 : R) 1} : (x : R) != 1 ↔ x != 1
参数：0 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Set.Ioc.coe_eq_one`：coe_eq_one {x : Ioc (0 : R) 1} : (x : R) = 1 ↔ x = 1
-/
theorem coe_ne_one {x : Ioc (0 : R) 1} : (x : R) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

omit [IsStrictOrderedRing R] in
/-
**Set.Ioc.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_pos (x : Ioc (0 : R) 1) : 0 < (x : R)
参数：x : Ioc (0 : R) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_pos (x : Ioc (0 : R) 1) : 0 < (x : R) :=
  x.2.1

omit [IsStrictOrderedRing R] in
/-
**Set.Ioc.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_le_one (x : Ioc (0 : R) 1) : (x : R) <= 1
参数：x : Ioc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_le_one (x : Ioc (0 : R) 1) : (x : R) ≤ 1 :=
  x.2.2

/-- like `coe_le_one`, but with the inequality in `Ioc (0:R) 1`. -/
/-
**Set.Ioc.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：le_one {t : Ioc (0 : R) 1} : t <= 1
参数：0 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `coe_le_one`, but with the inequality in `Ioc (0:R) 1`.
-/
theorem le_one {t : Ioc (0 : R) 1} : t ≤ 1 :=
  t.2.2
/-
**Set.Ioc.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instMul : Mul (Ioc (0 : R) 1) where mul p q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (Ioc (0 : R) 1) where
  mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one₀ p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩
/-
**Set.Ioc.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instPow : Pow (Ioc (0 : R) 1) Nat where pow p n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow : Pow (Ioc (0 : R) 1) ℕ where
  pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one₀ (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
/-
**Set.Ioc.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_mul (x y : Ioc (0 : R) 1) : ↑(x * y) = (x * y : R)
参数：x y : Ioc (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : Ioc (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl

@[simp, norm_cast]
/-
**Set.Ioc.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：coe_pow (x : Ioc (0 : R) 1) (n : Nat) : ↑(x ^ n) = ((x : R) ^ n)
参数：x : Ioc (0 : R) 1；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (x : Ioc (0 : R) 1) (n : ℕ) : ↑(x ^ n) = ((x : R) ^ n) :=
  rfl
/-
**Set.Ioc.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instSemigroup : Semigroup (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup : Semigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul
/-
**Set.Ioc.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instMonoid : Monoid (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.monoid _ coe_one coe_mul coe_pow
/-
**Set.Ioc.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictO
rderedRing R] : CommSemigroup (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul
/-
**Set.Ioc.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instCommMonoid {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrde
redRing R] : CommMonoid (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid (Ioc (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commMonoid _ coe_one coe_mul coe_pow
/-
**Set.Ioc.instCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instCancelMonoid {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRin
g R] [IsDomain R] : CancelMonoid (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCancelMonoid {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [IsDomain R] : CancelMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instMonoid with
    mul_left_cancel := fun a _ _ h =>
      Subtype.ext <| mul_left_cancel₀ a.prop.1.ne' <| (congr_arg Subtype.val h :)
    mul_right_cancel := fun b _ _ h =>
      Subtype.ext <| mul_right_cancel₀ b.prop.1.ne' <| (congr_arg Subtype.val h :) }
/-
**Set.Ioc.instCancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：instCancelCommMonoid {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOr
deredRing R] [IsDomain R] : CancelCommMonoid (Ioc (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCancelCommMonoid {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
    [IsDomain R] :
    CancelCommMonoid (Ioc (0 : R) 1) :=
  { Set.Ioc.instCommMonoid, Set.Ioc.instCancelMonoid with }

/-- The coercion from `Set.Ioc 0 1` as a `MonoidHom`. -/
@[simps]
/-
**Set.Ioc.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Set.Ioc`。
形式化陈述：coeMonoidHom : (Ioc (0 : R) 1) ->* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc.coe_mul`：coe_mul (x y : Ioc (0 : R) 1) : ↑(x * y) = (x * y : R)

--- 原说明 ---
The coercion from `Set.Ioc 0 1` as a `MonoidHom`.
-/
def coeMonoidHom : (Ioc (0 : R) 1) →* R where
  toFun := (↑)
  map_mul' := coe_mul
  map_one' := rfl

end Set.Ioc

/-! ### Instances for `↥(Set.Ioo 0 1)` -/


namespace Set.Ioo

omit [IsStrictOrderedRing R] in
/-
**Set.Ioo.pos** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：pos (x : Ioo (0 : R) 1) : 0 < (x : R)
参数：x : Ioo (0 : R) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem pos (x : Ioo (0 : R) 1) : 0 < (x : R) :=
  x.2.1

omit [IsStrictOrderedRing R] in
/-
**Set.Ioo.lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：lt_one (x : Ioo (0 : R) 1) : (x : R) < 1
参数：x : Ioo (0 : R) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lt_one (x : Ioo (0 : R) 1) : (x : R) < 1 :=
  x.2.2
/-
**Set.Ioo.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioo`。
形式化陈述：instMul : Mul (Ioo (0 : R) 1) where mul p q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (Ioo (0 : R) 1) where
  mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]
/-
**Set.Ioo.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：coe_mul (x y : Ioo (0 : R) 1) : ↑(x * y) = (x * y : R)
参数：x y : Ioo (0 : R) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : Ioo (0 : R) 1) : ↑(x * y) = (x * y : R) :=
  rfl
/-
**Set.Ioo.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioo`。
形式化陈述：instSemigroup : Semigroup (Ioo (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup : Semigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.semigroup _ coe_mul
/-
**Set.Ioo.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioo`。
形式化陈述：instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictO
rderedRing R] : CommSemigroup (Ioo (0 : R) 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommSemigroup (Ioo (0 : R) 1) := fast_instance%
  Subtype.coe_injective.commSemigroup _ coe_mul

/-- The coercion from `Set.Ioo 0 1` as a `MulHom`. -/
@[simps]
/-
**Set.Ioo.coeMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Set.Ioo`。
形式化陈述：coeMulHom : (Ioo (0 : R) 1) ->ₙ* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo.coe_mul`：coe_mul (x y : Ioo (0 : R) 1) : ↑(x * y) = (x * y : R)

--- 原说明 ---
The coercion from `Set.Ioo 0 1` as a `MulHom`.
-/
def coeMulHom : (Ioo (0 : R) 1) →ₙ* R where
  toFun := (↑)
  map_mul' := coe_mul

variable {β : Type*} [Ring β] [PartialOrder β] [IsOrderedRing β]
/-
**Set.Ioo.one_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：one_sub_mem {t : β} (ht : t in Ioo (0 : β) 1) : 1 - t in Ioo (0 : β) 1
参数：ht : t in Ioo (0 : β) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem one_sub_mem {t : β} (ht : t ∈ Ioo (0 : β) 1) : 1 - t ∈ Ioo (0 : β) 1 := by
  simp_all only [mem_Ioo, sub_pos, sub_lt_self_iff, and_self]
/-
**Set.Ioo.mem_iff_one_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：mem_iff_one_sub_mem {t : β} : t in Ioo (0 : β) 1 ↔ 1 - t in Ioo (0 : β) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo.one_sub_mem`：one_sub_mem {t : β} (ht : t in Ioo (0 : β) 1) : 1 -
 t in Ioo (0 : β) 1
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem mem_iff_one_sub_mem {t : β} : t ∈ Ioo (0 : β) 1 ↔ 1 - t ∈ Ioo (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩
/-
**Set.Ioo.one_minus_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β)
参数：x : Ioo (0 : β) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2
/-
**Set.Ioo.one_minus_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1
参数：x : Ioo (0 : β) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

end Set.Ioo

