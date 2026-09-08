/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Nat.Basic

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

/-
**eq_zero_of_zero_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
参数：h : 0 ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.elim`：Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b =
 a * c -> P) : P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
product with zero equals `a` iff `a` equals zero. -/
@[simp]
/-
**zero_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_dvd_iff : 0 ∣ a ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an element `a` of a commutative semigroup with zero, there exists another 
element whose
product with zero equals `a` iff `a` equals zero.
-/
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

@[simp]
/-
**dvd_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_zero (a : α) : a ∣ 0
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)

end SemigroupWithZero

/-- Given two elements `b`, `c` of a cancellative `MonoidWithZero` and a nonzero element `a`,
`a*b` divides `a*c` iff `b` divides `c`. -/
/-
**mul_dvd_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCancelMulZero α] {a b c : α
} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given two elements `b`, `c` of a cancellative `MonoidWithZero` and a nonzero ele
ment `a`,
`a*b` divides `a*c` iff `b` divides `c`.
-/
theorem mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCancelMulZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

/-- Given two elements `a`, `b` of a commutative cancellative `MonoidWithZero` and a nonzero
element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
/-
**mul_dvd_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsCancelMulZero α] {a b c : 
α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given two elements `a`, `b` of a commutative cancellative `MonoidWithZero` and a
 nonzero
element `c`, `a*c` divides `b*c` iff `a` divides `b`.
-/
theorem mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsCancelMulZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
/-
**DvdNotUnit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DvdNotUnit (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divide
d by `a`
is not a unit.
-/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x
/-
**dvdNotUnit_of_dvd_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNo
tUnit a b
参数：hd : a ∣ b；hnd : ¬b ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

variable {x y : α}
/-
**isRelPrime_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `IsUnit.isRelPrime_right`：IsUnit.isRelPrime_right (h : IsUnit y) : IsRelP
rime x y
-/
theorem isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x :=
  ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩
/-
**isRelPrime_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `isRelPrime_zero_left`：isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x
-/
theorem isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x :=
  isRelPrime_comm.trans isRelPrime_zero_left
/-
**not_isRelPrime_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRelPrime_zero_right`：isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
theorem not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0 :=
  mt isRelPrime_zero_right.mp not_isUnit_zero
/-
**IsRelPrime.ne_zero_or_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x != 0
 ∨ y != 0
参数：h : IsRelPrime x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `not_isRelPrime_zero_zero`：not_isRelPrime_zero_zero [Nontrivial α] : ¬IsR
elPrime (0 : α) 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x ≠ 0 ∨ y ≠ 0 :=
  not_or_of_imp <| by rintro rfl rfl; exact not_isRelPrime_zero_zero h

end CommMonoidWithZero

/-
**isRelPrime_of_no_nonunits_factors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : 
¬(x = 0 ∧ y = 0)) (H : forall z, ¬ IsUnit z -> z != 0 -> z ∣ x -> ¬z ∣ y) : IsRe
lPrime x y
参数：nonzero : ¬(x = 0 ∧ y = 0)；H : forall z, ¬ IsUnit z -> z != 0 -> z ∣ x -> ¬z 
∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z, ¬ IsUnit z → z ≠ 0 → z ∣ x → ¬z ∣ y) : IsRelPrime x y := by
  refine fun z hx hy ↦ by_contra fun h ↦ H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩
/-
**dvd_and_not_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCancelMulZero α] {x y : α} :
 x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCancelMulZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by conv =>
            lhs
            rw [he, hdx]
            simp [mul_assoc]⟩)⟩⟩

section MonoidWithZero

variable [MonoidWithZero α]

/-
**ne_zero_of_dvd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (h₂ : p ∣ q) : p != 0
参数：h₁ : q != 0；h₂ : p ∣ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁
/-
**isPrimal_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimal_zero : IsPrimal (0 : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
-/
theorem isPrimal_zero : IsPrimal (0 : α) :=
  fun a b h ↦ ⟨a, b, dvd_rfl, dvd_rfl, (zero_dvd_iff.mp h).symm⟩
/-
**IsPrimal.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimal.mul {α} [CommMonoidWithZero α] [IsCancelMulZero α] {m n : α} (hm 
: IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n)
参数：hm : IsPrimal m；hn : IsPrimal n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_of_mul_right_dvd`：dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
-/
theorem IsPrimal.mul {α} [CommMonoidWithZero α] [IsCancelMulZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : ℕ}

section Subsingleton
variable [Subsingleton αˣ]

/-
**dvd_antisymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `mul_right_eq_self₀`：mul_right_eq_self₀ [IsLeftCancelMulZero M₀] : a * b 
= a ↔ b = 1 ∨ a = 0
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc, eq_comm, mul_right_eq_self₀, mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp
/-
**dvd_antisymm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_antisymm' : a ∣ b -> b ∣ a -> b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
-/
theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a :=
  flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'
/-
**eq_of_forall_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b
参数：h : forall c, a ∣ c ↔ b ∣ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.antisymm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCanc
elMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b :=
  ((h _).2 dvd_rfl).antisymm <| (h _).1 dvd_rfl
/-
**eq_of_forall_dvd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_dvd' (h : forall c, c ∣ a ↔ c ∣ b) : a = b
参数：h : forall c, c ∣ a ↔ c ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.antisymm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCanc
elMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
  ((h _).1 dvd_rfl).antisymm <| (h _).2 dvd_rfl

end Subsingleton

/-
**pow_dvd_pow_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_dvd_pow_iff (ha₀ : a != 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n <= m
参数：ha₀ : a != 0；ha : ¬IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
-/
lemma pow_dvd_pow_iff (ha₀ : a ≠ 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ, mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  · apply pow_dvd_pow

end CancelCommMonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `∣` is not a useful definition if an inverse is available. -/
@[simp]
/-
**GroupWithZero.dvd_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupWithZero.dvd_iff {m n : α} : m ∣ n ↔ (m = 0 -> n = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a

--- 原说明 ---
`∣` is not a useful definition if an inverse is available.
-/
lemma GroupWithZero.dvd_iff {m n : α} : m ∣ n ↔ (m = 0 → n = 0) := by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

end GroupWithZero

