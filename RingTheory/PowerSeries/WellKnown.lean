/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.invOneSubPow`: given a commutative ring `S` and a number `d : ℕ`,
  `PowerSeries.invOneSubPow S d` is the multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`.
  When `d` is `0`, `PowerSeries.invOneSubPow S d` will just be `1`. When `d` is positive,
  `PowerSeries.invOneSubPow S d` will be `∑ n, Nat.choose (d - 1 + n) (d - 1)`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/

@[expose] public section


namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- The power series for `1 / (u - x)`. -/
/-
**PowerSeries.invUnitsSub** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：invUnitsSub (u : Rˣ) : PowerSeries R
参数：u : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power series for `1 / (u - x)`.
-/
def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)

@[simp]
/-
**PowerSeries.coeff_invUnitsSub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_invUnitsSub (u : Rˣ) (n : Nat) : coeff n (invUnitsSub u) = 1 /ₚ u ^ 
(n + 1)
参数：u : Rˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem coeff_invUnitsSub (u : Rˣ) (n : ℕ) : coeff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk _ _

@[simp]
/-
**PowerSeries.constantCoeff_invUnitsSub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff (invUnitsSub u) = 1 /ₚ 
u
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
· 使用定理 `PowerSeries.coeff_invUnitsSub`：coeff_invUnitsSub (u : Rˣ) (n : Nat) : co
eff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff (invUnitsSub u) = 1 /ₚ u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invUnitsSub, zero_add, pow_one]

@[simp]
/-
**PowerSeries.invUnitsSub_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C (u : R)
 - 1
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PowerSeries.constantCoeff_invUnitsSub`：constantCoeff_invUnitsSub (u : Rˣ
) : constantCoeff (invUnitsSub u) = 1 /ₚ u
· 使用定理 `one_divp`：one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_succ_mul_X`：coeff_succ_mul_X (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (φ * X) = coeff n φ
· 使用定理 `PowerSeries.coeff_invUnitsSub`：coeff_invUnitsSub (u : Rˣ) (n : Nat) : co
eff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_mul_C`：coeff_mul_C (n : Nat) (φ : R⟦X⟧) (a : R) : coef
f n (φ * C a) = coeff n φ * a
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
（共 33 条，此处仅展示前 30 条）
-/
theorem invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C (u : R) - 1 := by
  ext (_ | n)
  · simp
  · simp [pow_succ']

@[simp]
/-
**PowerSeries.invUnitsSub_mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C (u : R) - X) = 1
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `PowerSeries.invUnitsSub_mul_X`：invUnitsSub_mul_X (u : Rˣ) : invUnitsSub 
u * X = invUnitsSub u * C (u : R) - 1
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C (u : R) - X) = 1 := by
  simp [mul_sub, sub_sub_cancel]
/-
**PowerSeries.map_invUnitsSub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_invUnitsSub (f : R ->+* S) (u : Rˣ) : map f (invUnitsSub u) = invUnits
Sub (Units.map (f : R ->* S) u)
参数：f : R ->+* S；u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.coeff_invUnitsSub`：coeff_invUnitsSub (u : Rˣ) (n : Nat) : co
eff n (invUnitsSub u) = 1 /ₚ u ^ (n + 1)
· 使用定理 `one_divp`：one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹
-/
theorem map_invUnitsSub (f : R →+* S) (u : Rˣ) :
    map f (invUnitsSub u) = invUnitsSub (Units.map (f : R →* S) u) := by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

end Ring

section invOneSubPow

variable (S : Type*) [CommRing S] (d : ℕ)

/--
(1 + X + X^2 + ...) * (1 - X) = 1.

Note that the power series `1 + X + X^2 + ...` is written as `mk 1` where `1` is the constant
function so that `mk 1` is the power series with all coefficients equal to one.
-/
/-
**PowerSeries.mk_one_mul_one_sub_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：mk_one_mul_one_sub_eq_one : (mk 1 : S⟦X⟧) * (1 - X) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `PowerSeries.coeff_succ_X_mul`：coeff_succ_X_mul (n : Nat) (φ : R⟦X⟧) : co
eff (n + 1) (X * φ) = coeff n φ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
(1 + X + X^2 + ...) * (1 - X) = 1.

Note that the power series `1 + X + X^2 + ...` is written as `mk 1` where `1` is
 the constant
function so that `mk 1` is the power series with all coefficients equal to one.
-/
theorem mk_one_mul_one_sub_eq_one : (mk 1 : S⟦X⟧) * (1 - X) = 1 := by
  rw [mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

/--
Note that `mk 1` is the constant function `1` so the power series `1 + X + X^2 + ...`. This theorem
states that for any `d : ℕ`, `(1 + X + X^2 + ... : S⟦X⟧) ^ (d + 1)` is equal to the power series
`mk fun n => Nat.choose (d + n) d : S⟦X⟧`.
-/
/-
**PowerSeries.mk_one_pow_eq_mk_choose_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
`。
形式化陈述：mk_one_pow_eq_mk_choose_add : (mk 1 : S⟦X⟧) ^ (d + 1) = (mk fun n => Nat.c
hoose (d + n) d : S⟦X⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_antidiagonal_choose_add`：sum_antidiagonal_choose_add (d n : N
at) : (∑ ij in antidiagonal n, (d + ij.2).choose d) = (d + n + 1).choose (d + 1)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b

--- 原说明 ---
Note that `mk 1` is the constant function `1` so the power series `1 + X + X^2 +
 ...`. This theorem
states that for any `d : ℕ`, `(1 + X + X^2 + ... : S⟦X⟧) ^ (d + 1)` is equal to 
the power series
`mk fun n => Nat.choose (d + n) d : S⟦X⟧`.
-/
theorem mk_one_pow_eq_mk_choose_add :
    (mk 1 : S⟦X⟧) ^ (d + 1) = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add, hd, pow_one, mul_comm, coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add, add_right_comm]

/--
Given a natural number `d : ℕ` and a commutative ring `S`, `PowerSeries.invOneSubPow S d` is the
multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`. When `d` is `0`, `PowerSeries.invOneSubPow S d`
will just be `1`. When `d` is positive, `PowerSeries.invOneSubPow S d` will be the power series
`mk fun n => Nat.choose (d - 1 + n) (d - 1)`.
-/
/-
**PowerSeries.invOneSubPow** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：invOneSubPow : Nat -> S⟦X⟧ˣ | 0 => 1 | d + 1 => { val
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural number `d : ℕ` and a commutative ring `S`, `PowerSeries.invOneSu
bPow S d` is the
multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`. When `d` is `0`, `PowerSerie
s.invOneSubPow S d`
will just be `1`. When `d` is positive, `PowerSeries.invOneSubPow S d` will be t
he power series
`mk fun n => Nat.choose (d - 1 + n) (d - 1)`.
-/
noncomputable def invOneSubPow : ℕ → S⟦X⟧ˣ
  | 0 => 1
  | d + 1 => {
    val := mk fun n => Nat.choose (d + n) d
    inv := (1 - X) ^ (d + 1)
    val_inv := by
      rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]
    inv_val := by
      rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
    }
/-
**PowerSeries.invOneSubPow_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invOneSubPow_zero : invOneSubPow S 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOneSubPow_zero : invOneSubPow S 0 = 1 := by
  delta invOneSubPow
  simp only
/-
**PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos** 是 Mathlib 中的一个定
理，位于命名空间 `PowerSeries`。
形式化陈述：invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (h : 0 < d) : (invOneSubP
ow S d).val = (mk fun n => Nat.choose (d - 1 + n) (d - 1) : S⟦X⟧)
参数：h : 0 < d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_one_add_one_eq_of_pos`：∀ {n : ℕ}, 0 < n → n - 1 + 1 = n
· 使用定理 `PowerSeries.invOneSubPow.eq_2`：∀ (S : Type u_1) [inst : CommRing S] (d :
 ℕ),   PowerSeries.invOneSubPow S d.succ =     { val := PowerSeries.mk fun n => 
↑((d + n).choose d)…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (h : 0 < d) :
    (invOneSubPow S d).val = (mk fun n => Nat.choose (d - 1 + n) (d - 1) : S⟦X⟧) := by
  rw [← Nat.sub_one_add_one_eq_of_pos h, invOneSubPow, add_tsub_cancel_right]
/-
**PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries`。
形式化陈述：invOneSubPow_val_succ_eq_mk_add_choose : (invOneSubPow S (d + 1)).val = (m
k fun n => Nat.choose (d + n) d : S⟦X⟧)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invOneSubPow_val_succ_eq_mk_add_choose :
    (invOneSubPow S (d + 1)).val = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := rfl
/-
**PowerSeries.invOneSubPow_val_one_eq_invUnitSub_one** 是 Mathlib 中的一个定理，位于命名空间 `
PowerSeries`。
形式化陈述：invOneSubPow_val_one_eq_invUnitSub_one : (invOneSubPow S 1).val = invUnits
Sub (1 : Sˣ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Units.mk.congr_simp`：∀ {α : Type u} [inst : Monoid α] (val val_1 : α) (e
_val : val = val_1) (inv inv_1 : α) (e_inv : inv = inv_1)   (val_inv : val * inv
 = 1) (in…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `divp_one`：divp_one (a : α) : a /ₚ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOneSubPow_val_one_eq_invUnitSub_one :
    (invOneSubPow S 1).val = invUnitsSub (1 : Sˣ) := by
  simp [invOneSubPow, invUnitsSub]

/--
The theorem `PowerSeries.mk_one_mul_one_sub_eq_one` implies that `1 - X` is a unit in `S⟦X⟧`
whose inverse is the power series `1 + X + X^2 + ...`. This theorem states that for any `d : ℕ`,
`PowerSeries.invOneSubPow S d` is equal to `(1 - X)⁻¹ ^ d`.
-/
/-
**PowerSeries.invOneSubPow_eq_inv_one_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries`。
形式化陈述：invOneSubPow_eq_inv_one_sub_pow : invOneSubPow S d = (Units.mkOfMulEqOne (
1 - X) (mk 1 : S⟦X⟧) <| Eq.trans (mul_comm _ _) (mk_one_mul_one_sub_eq_one S))⁻¹
 ^ d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.mk_one_mul_one_sub_eq_one`：mk_one_mul_one_sub_eq_one : (mk 1
 : S⟦X⟧) * (1 - X) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `DivisionMonoid.inv_eq_of_mul`：∀ {G : Type u} [self : DivisionMonoid G] (
a b : G), a * b = 1 → a⁻¹ = b
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1

--- 原说明 ---
The theorem `PowerSeries.mk_one_mul_one_sub_eq_one` implies that `1 - X` is a un
it in `S⟦X⟧`
whose inverse is the power series `1 + X + X^2 + ...`. This theorem states that 
for any `d : ℕ`,
`PowerSeries.invOneSubPow S d` is equal to `(1 - X)⁻¹ ^ d`.
-/
theorem invOneSubPow_eq_inv_one_sub_pow :
    invOneSubPow S d =
      (Units.mkOfMulEqOne (1 - X) (mk 1 : S⟦X⟧) <|
        Eq.trans (mul_comm _ _) (mk_one_mul_one_sub_eq_one S))⁻¹ ^ d := by
  induction d with
  | zero => exact Eq.symm <| pow_zero _
  | succ d _ =>
      rw [inv_pow]
      exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow S (d + 1)) <| by
        rw [← Units.val_eq_one, Units.val_mul, Units.val_pow_eq_pow_val]
        exact (invOneSubPow S (d + 1)).inv_val).symm
/-
**PowerSeries.invOneSubPow_inv_eq_one_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries`。
形式化陈述：invOneSubPow_inv_eq_one_sub_pow : (invOneSubPow S d).inv = (1 - X : S⟦X⟧) 
^ d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem invOneSubPow_inv_eq_one_sub_pow :
    (invOneSubPow S d).inv = (1 - X : S⟦X⟧) ^ d := by
  induction d with
  | zero => exact Eq.symm <| pow_zero _
  | succ d => rfl
/-
**PowerSeries.invOneSubPow_inv_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：invOneSubPow_inv_zero_eq_one : (invOneSubPow S 0).inv = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOneSubPow_inv_zero_eq_one : (invOneSubPow S 0).inv = 1 := by
  delta invOneSubPow
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one]
/-
**PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries`。
形式化陈述：mk_add_choose_mul_one_sub_pow_eq_one : (mk fun n => Nat.choose (d + n) d :
 S⟦X⟧) * ((1 - X) ^ (d + 1)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
-/
theorem mk_add_choose_mul_one_sub_pow_eq_one :
    (mk fun n ↦ Nat.choose (d + n) d : S⟦X⟧) * ((1 - X) ^ (d + 1)) = 1 :=
  (invOneSubPow S (d + 1)).val_inv
/-
**PowerSeries.invOneSubPow_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：invOneSubPow_add (e : Nat) : invOneSubPow S (d + e) = invOneSubPow S d * i
nvOneSubPow S e
参数：e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PowerSeries.mk_one_mul_one_sub_eq_one`：mk_one_mul_one_sub_eq_one : (mk 1
 : S⟦X⟧) * (1 - X) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.invOneSubPow_eq_inv_one_sub_pow`：invOneSubPow_eq_inv_one_sub
_pow : invOneSubPow S d = (Units.mkOfMulEqOne (1 - X) (mk 1 : S⟦X⟧) <| Eq.trans 
(mul_comm _ _) (mk_one_mul_one_su…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOneSubPow_add (e : ℕ) :
    invOneSubPow S (d + e) = invOneSubPow S d * invOneSubPow S e := by
  simp_rw [invOneSubPow_eq_inv_one_sub_pow, pow_add]
/-
**PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val** 是 Mathl
ib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (e : Nat) : (1 - 
X) ^ e * (invOneSubPow S (d + e)).val = (invOneSubPow S d).val
参数：e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.invOneSubPow_add`：invOneSubPow_add (e : Nat) : invOneSubPow 
S (d + e) = invOneSubPow S d * invOneSubPow S e
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (e : ℕ) :
    (1 - X) ^ e * (invOneSubPow S (d + e)).val = (invOneSubPow S d).val := by
  simp [invOneSubPow_add, Units.val_mul, mul_comm, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow]
/-
**PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow** 是 Mathlib 中的
一个定理，位于命名空间 `PowerSeries`。
形式化陈述：one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (e : Nat) : (1 - X) ^ 
(d + e) * (invOneSubPow S e).val = (1 - X) ^ d
参数：e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.invOneSubPow_inv_eq_one_sub_pow`：invOneSubPow_inv_eq_one_sub
_pow : (invOneSubPow S d).inv = (1 - X : S⟦X⟧) ^ d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (e : ℕ) :
    (1 - X) ^ (d + e) * (invOneSubPow S e).val = (1 - X) ^ d := by
  simp [pow_add, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow S e]

end invOneSubPow

section Field

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

/-- Power series for the sine function at zero. -/
/-
**PowerSeries.sin** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：sin : PowerSeries A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Power series for the sine function at zero.
-/
def sin : PowerSeries A :=
  mk fun n => if Even n then 0 else algebraMap ℚ A ((-1) ^ (n / 2) / n !)

/-- Power series for the cosine function at zero. -/
/-
**PowerSeries.cos** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：cos : PowerSeries A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Power series for the cosine function at zero.
-/
def cos : PowerSeries A :=
  mk fun n => if Even n then algebraMap ℚ A ((-1) ^ (n / 2) / n !) else 0

variable {A A'} (n : ℕ) (f : A →+* A')

@[simp]
/-
**PowerSeries.map_sin** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_sin : map f (sin A) = sin A'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.map_rat_algebraMap`：map_rat_algebraMap [Semiring R] [Semiring S]
 [Algebra Rat R] [Algebra Rat S] (f : R ->+* S) (r : Rat) : f (algebraMap Rat R 
r) = algebraMap …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_sin : map f (sin A) = sin A' := by
  ext
  simp [sin, apply_ite f]

@[simp]
/-
**PowerSeries.map_cos** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_cos : map f (cos A) = cos A'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.map_rat_algebraMap`：map_rat_algebraMap [Semiring R] [Semiring S]
 [Algebra Rat R] [Algebra Rat S] (f : R ->+* S) (r : Rat) : f (algebraMap Rat R 
r) = algebraMap …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_cos : map f (cos A) = cos A' := by
  ext
  simp [cos, apply_ite f]

end Field


end PowerSeries

