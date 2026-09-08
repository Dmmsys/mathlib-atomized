/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

@[expose] public section


section

open EuclideanDomain Set Ideal

section GCDMonoid

variable {R : Type*} [EuclideanDomain R] [GCDMonoid R] {p q : R}

/-
**left_div_gcd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_div_gcd_ne_zero {p q : R} (hp : p != 0) : p / GCDMonoid.gcd p q != 0
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) : p / GCDMonoid.gcd p q ≠ 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  nth_rw 1 [hr]
  rw [mul_comm, mul_div_cancel_right₀ _ pq0]
  exact r0
/-
**right_div_gcd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q / GCDMonoid.gcd p q != 0
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) : q / GCDMonoid.gcd p q ≠ 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  nth_rw 1 [hr]
  rw [mul_comm, mul_div_cancel_right₀ _ pq0]
  exact r0
/-
**isCoprime_div_gcd_div_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_div_gcd_div_gcd (hq : q != 0) : IsCoprime (p / GCDMonoid.gcd p q
) (q / GCDMonoid.gcd p q)
参数：hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `gcd_isUnit_iff`：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime 
x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `isUnit_gcd_of_eq_mul_gcd`：isUnit_gcd_of_eq_mul_gcd {α : Type*} [CommMono
idWithZero α] [GCDMonoid α] {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gc
d x y * y') (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
· 使用定理 `gcd_ne_zero_of_right`：gcd_ne_zero_of_right [GCDMonoid α] {a b : α} (hb :
 b != 0) : gcd a b != 0
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
-/
theorem isCoprime_div_gcd_div_gcd (hq : q ≠ 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
  (gcd_isUnit_iff _ _).1 <|
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_left _ _).symm
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_right _ _).symm <|
      gcd_ne_zero_of_right hq

/-- This is a version of `isCoprime_div_gcd_div_gcd` which replaces the `q ≠ 0` assumption with
`gcd p q ≠ 0`. -/
/-
**isCoprime_div_gcd_div_gcd_of_gcd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (hpq : GCDMonoid.gcd p q != 0) : 
IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q)
参数：hpq : GCDMonoid.gcd p q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `gcd_isUnit_iff`：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime 
x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `isUnit_gcd_of_eq_mul_gcd`：isUnit_gcd_of_eq_mul_gcd {α : Type*} [CommMono
idWithZero α] [GCDMonoid α] {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gc
d x y * y') (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b

--- 原说明 ---
This is a version of `isCoprime_div_gcd_div_gcd` which replaces the `q ≠ 0` assu
mption with
`gcd p q ≠ 0`.
-/
theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (hpq : GCDMonoid.gcd p q ≠ 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
  (gcd_isUnit_iff _ _).1 <|
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_left _ _).symm
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_right _ _).symm <| hpq

end GCDMonoid

namespace EuclideanDomain

/-- Create a `GCDMonoid` whose `GCDMonoid.gcd` matches `EuclideanDomain.gcd`. -/
@[instance_reducible]
/-
**EuclideanDomain.gcdMonoid** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
形式化陈述：gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where gcd
参数：R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.gcd_dvd_left`：gcd_dvd_left (a b : R) : gcd a b ∣ a
· 使用定理 `EuclideanDomain.gcd_dvd_right`：gcd_dvd_right (a b : R) : gcd a b ∣ b
· 使用定理 `EuclideanDomain.dvd_gcd`：dvd_gcd {a b c : R} : c ∣ a -> c ∣ b -> c ∣ gcd
 a b
· 使用定理 `EuclideanDomain.lcm_zero_left`：lcm_zero_left (x : R) : lcm 0 x = 0
· 使用定理 `EuclideanDomain.lcm_zero_right`：lcm_zero_right (x : R) : lcm x 0 = 0

--- 原说明 ---
Create a `GCDMonoid` whose `GCDMonoid.gcd` matches `EuclideanDomain.gcd`.
-/
def gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]; rfl
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

variable {α : Type*} [EuclideanDomain α]
/-
**EuclideanDomain.span_gcd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：span_gcd [DecidableEq α] (x y : α) : span ({gcd x y} : Set α) = span ({x, 
y} : Set α)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `span_gcd`：span_gcd (x y : R) : span {gcd x y} = span {x, y}
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
-/
theorem span_gcd [DecidableEq α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y
/-
**EuclideanDomain.gcd_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gcd_isUnit_iff`：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime 
x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
-/
theorem gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

-- this should be proved for UFDs surely?
/-
**EuclideanDomain.isCoprime_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：isCoprime_of_dvd {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z in n
onunits α, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
参数：nonzero : ¬(x = 0 ∧ y = 0)；H : forall z in nonunits α, z != 0 -> z ∣ x -> ¬z 
∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_of_dvd`：isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0)
) (H : forall z in nonunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
-/
theorem isCoprime_of_dvd {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

-- this should be proved for UFDs surely?
/-
**EuclideanDomain.dvd_or_coprime** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：dvd_or_coprime (x y : α) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y
参数：x y : α；h : Irreducible x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_or_isCoprime`：dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y
 ∨ IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
-/
theorem dvd_or_coprime (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

end EuclideanDomain

end

