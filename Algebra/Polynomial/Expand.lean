/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

## Main definitions

* `Polynomial.expand R p f`: expand the polynomial `f` with coefficients in a
  commutative semiring `R` by a factor of p, so `expand R p (∑ aₙ xⁿ)` is `∑ aₙ xⁿᵖ`.
* `Polynomial.contract p f`: the opposite of `expand`, so it sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.

-/

@[expose] public section


universe u v w

open Polynomial

open Finset

namespace Polynomial

section CommSemiring

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`. -/
/-
**Polynomial.expand** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：expand : R[X] ->ₐ[R] R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/
noncomputable def expand : R[X] →ₐ[R] R[X] :=
  { (eval₂RingHom C (X ^ p) : R[X] →+* R[X]) with commutes' := fun _ => eval₂_C _ _ }
/-
**Polynomial.coe_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_expand : (expand R p : R[X] -> R[X]) = eval₂ C (X ^ p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_expand : (expand R p : R[X] → R[X]) = eval₂ C (X ^ p) :=
  rfl

variable {R}
/-
**Polynomial.expand_eq_comp_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem expand_eq_comp_X_pow {f : R[X]} : expand R p f = f.comp (X ^ p) := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.expand_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^
 e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_eq_sum`：eval₂_eq_sum {f : R ->+* S} {x : S} : p.eval₂ f
 x = p.sum fun e a => f a * x ^ e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_eq_sum {f : R[X]} : expand R p f = f.sum fun e a => C a * (X ^ p) ^ e := by
  simp [expand, eval₂_eq_sum]

@[simp]
/-
**Polynomial.expand_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_C (r : R) : expand R p (C r) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
-/
theorem expand_C (r : R) : expand R p (C r) = C r :=
  eval₂_C _ _

@[simp]
/-
**Polynomial.expand_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_X : expand R p X = X ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
-/
theorem expand_X : expand R p X = X ^ p :=
  eval₂_X _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Polynomial.expand_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_monomial (r : R) : expand R p (monomial q r) = monomial (q * p) r := by
  simp_rw [← smul_X_eq_monomial, map_smul, map_pow, expand_X, mul_comm, pow_mul]
/-
**Polynomial.expand_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem expand_expand (f : R[X]) : expand R p (expand R q f) = expand R (p * q) f :=
  Polynomial.induction_on f (fun r => by simp_rw [expand_C])
    (fun f g ihf ihg => by simp_rw [map_add, ihf, ihg]) fun n r _ => by
    simp_rw [map_mul, expand_C, map_pow, expand_X, map_pow, expand_X, pow_mul]
/-
**Polynomial.expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f)
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_expand`：expand_expand (f : R[X]) : expand R p (expand 
R q f) = expand R (p * q) f
-/
theorem expand_mul (f : R[X]) : expand R (p * q) f = expand R p (expand R q f) :=
  (expand_expand p q f).symm

@[simp]
/-
**Polynomial.expand_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f)
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `Polynomial.eval₂_at_one`：eval₂_at_one {S : Type*} [Semiring S] (f : R ->
+* S) : p.eval₂ f 1 = f (p.eval 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_zero (f : R[X]) : expand R 0 f = C (eval 1 f) := by simp [expand]

@[simp]
/-
**Polynomial.expand_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_one (f : R[X]) : expand R 1 f = f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem expand_one (f : R[X]) : expand R 1 f = f :=
  Polynomial.induction_on f (fun r => by rw [expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul, expand_C, map_pow, expand_X, pow_one]
/-
**Polynomial.expand_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `Function.iterate_zero`：iterate_zero : f^[0] = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Polynomial.expand_mul`：expand_mul (f : R[X]) : expand R (p * q) f = expa
nd R p (expand R q f)
-/
theorem expand_pow (f : R[X]) : expand R (p ^ q) f = (expand R p)^[q] f :=
  Nat.recOn q (by rw [pow_zero, expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply', pow_succ', expand_mul, ih]
/-
**Polynomial.derivative_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) = expa
nd R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X]))
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_expand`：coe_expand : (expand R p : R[X] -> R[X]) = eval₂ 
C (X ^ p)
· 使用定理 `Polynomial.derivative_eval₂_C`：derivative_eval₂_C (p q : R[X]) : derivat
ive (p.eval₂ C q) = p.derivative.eval₂ C q * derivative q
· 使用定理 `Polynomial.derivative_pow`：derivative_pow (p : R[X]) (n : Nat) : derivat
ive (p ^ n) = C (n : R) * p ^ (n - 1) * derivative p
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem derivative_expand (f : R[X]) : Polynomial.derivative (expand R p f) =
    expand R p (Polynomial.derivative f) * (p * (X ^ (p - 1) : R[X])) := by
  rw [coe_expand, derivative_eval₂_C, derivative_pow, C_eq_natCast, derivative_X, mul_one]
/-
**Polynomial.coeff_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) : (expand R p f).
coeff n = if p ∣ n then f.coeff (n / p) else 0
参数：hp : 0 < p；f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_eq_sum`：expand_eq_sum {f : R[X]} : expand R p f = f.su
m fun e a => C a * (X ^ p) ^ e
· 使用定理 `Polynomial.coeff_sum`：coeff_sum [Semiring S] (n : Nat) (f : Nat -> R -> 
S[X]) : coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.notMem_support_iff`：notMem_support_iff : n ∉ p.support ↔ p.co
eff n = 0
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
-/
theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  simp only [expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3, Nat.mul_div_cancel_left b hp]
    · intro hn
      rw [notMem_support_iff.1 hn]
      split_ifs <;> rfl
  · rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    exact fun hkn => h ⟨k, hkn.symm⟩

@[simp]
/-
**Polynomial.coeff_expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_expand_mul {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) : (expand R p
 f).coeff (n * p) = f.coeff n
参数：hp : 0 < p；f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
-/
theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (n * p) = f.coeff n := by
  rw [coeff_expand hp, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hp]

@[simp]
/-
**Polynomial.coeff_expand_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_expand_mul' {p : Nat} (hp : 0 < p) (f : R[X]) (n : Nat) : (expand R 
p f).coeff (p * n) = f.coeff n
参数：hp : 0 < p；f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.coeff_expand_mul`：coeff_expand_mul {p : Nat} (hp : 0 < p) (f 
: R[X]) (n : Nat) : (expand R p f).coeff (n * p) = f.coeff n
-/
theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (expand R p f).coeff (p * n) = f.coeff n := by rw [mul_comm, coeff_expand_mul hp]

/-- Expansion is injective. -/
/-
**Polynomial.expand_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_injective {n : Nat} (hn : 0 < n) : Function.Injective (expand R n)
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_expand_mul`：coeff_expand_mul {p : Nat} (hp : 0 < p) (f 
: R[X]) (n : Nat) : (expand R p f).coeff (n * p) = f.coeff n

--- 原说明 ---
Expansion is injective.
-/
theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand R n) := fun g g' H =>
  ext fun k => by rw [← coeff_expand_mul hn, H, coeff_expand_mul hn]
/-
**Polynomial.expand_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_inj {p : Nat} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p
 g ↔ f = g
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.expand_injective`：expand_injective {n : Nat} (hn : 0 < n) : F
unction.Injective (expand R n)
-/
theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : R[X]} : expand R p f = expand R p g ↔ f = g :=
  (expand_injective hp).eq_iff
/-
**Polynomial.expand_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_eq_zero {p : Nat} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 
0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Polynomial.expand_injective`：expand_injective {n : Nat} (hn : 0 < n) : F
unction.Injective (expand R n)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)
/-
**Polynomial.expand_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_ne_zero {p : Nat} (hp : 0 < p) {f : R[X]} : expand R p f != 0 ↔ f !
= 0
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.expand_eq_zero`：expand_eq_zero {p : Nat} (hp : 0 < p) {f : R[
X]} : expand R p f = 0 ↔ f = 0
-/
theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : R[X]} : expand R p f ≠ 0 ↔ f ≠ 0 :=
  (expand_eq_zero hp).not
/-
**Polynomial.expand_eq_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_eq_C {p : Nat} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r
 ↔ f = C r
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `Polynomial.expand_inj`：expand_inj {p : Nat} (hp : 0 < p) {f g : R[X]} : 
expand R p f = expand R p g ↔ f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : R[X]} {r : R} : expand R p f = C r ↔ f = C r := by
  rw [← expand_C, expand_inj hp, expand_C]
/-
**Polynomial.natDegree_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_expand (p : Nat) (f : R[X]) : (expand R p f).natDegree = f.natDe
gree * p
参数：p : Nat；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coe_expand`：coe_expand : (expand R p : R[X] -> R[X]) = eval₂ 
C (X ^ p)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.expand_eq_zero`：expand_eq_zero {p : Nat} (hp : 0 < p) {f : R[
X]} : expand R p f = 0 ↔ f = 0
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 37 条，此处仅展示前 30 条）
-/
theorem natDegree_expand (p : ℕ) (f : R[X]) : (expand R p f).natDegree = f.natDegree * p := by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, map_zero, natDegree_zero, zero_mul]
  have hf1 : expand R p f ≠ 0 := mt (expand_eq_zero hp).1 hf
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree hf1]
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun n hn => ?_) ?_
  · rw [coeff_expand hp]
    split_ifs with hpn
    · rw [coeff_eq_zero_of_natDegree_lt]
      contrapose! hn
      norm_cast
      rw [← Nat.div_mul_cancel hpn]
      exact Nat.mul_le_mul_right p hn
    · rfl
  · refine le_degree_of_ne_zero ?_
    rw [coeff_expand_mul hp, ← leadingCoeff]
    exact mt leadingCoeff_eq_zero.1 hf
/-
**Polynomial.leadingCoeff_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_expand {p : Nat} {f : R[X]} (hp : 0 < p) : (expand R p f).lea
dingCoeff = f.leadingCoeff
参数：hp : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_expand`：natDegree_expand (p : Nat) (f : R[X]) : (ex
pand R p f).natDegree = f.natDegree * p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_expand_mul`：coeff_expand_mul {p : Nat} (hp : 0 < p) (f 
: R[X]) (n : Nat) : (expand R p f).coeff (n * p) = f.coeff n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_expand {p : ℕ} {f : R[X]} (hp : 0 < p) :
    (expand R p f).leadingCoeff = f.leadingCoeff := by
  simp_rw [leadingCoeff, natDegree_expand, coeff_expand_mul hp]
/-
**Polynomial.monic_expand_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_expand_iff {p : Nat} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic 
↔ f.Monic
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_expand`：leadingCoeff_expand {p : Nat} {f : R[X]}
 (hp : 0 < p) : (expand R p f).leadingCoeff = f.leadingCoeff
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monic_expand_iff {p : ℕ} {f : R[X]} (hp : 0 < p) : (expand R p f).Monic ↔ f.Monic := by
  simp only [Monic, leadingCoeff_expand hp]

alias ⟨_, Monic.expand⟩ := monic_expand_iff
/-
**Polynomial.map_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : map f (expand R p q) = ex
pand S p (map f q)
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
· 使用定理 `Polynomial.expand_zero`：expand_zero (f : R[X]) : expand R 0 f = C (eval 
1 f)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.eval_one_map`：eval_one_map (f : R ->+* S) (p : R[X]) : (p.map
 f).eval 1 = f (p.eval 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem map_expand {p : ℕ} {f : R →+* S} {q : R[X]} :
    map f (expand R p q) = expand S p (map f q) := by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map, coeff_expand (Nat.pos_of_ne_zero hp), coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all

@[simp]
/-
**Polynomial.expand_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_eval (p : Nat) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r
 ^ p) P
参数：p : Nat；P : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
-/
theorem expand_eval (p : ℕ) (P : R[X]) (r : R) : eval r (expand R p P) = eval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add, eval_add, eval_add, hf, hg]

@[simp]
/-
**Polynomial.expand_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : Nat) (P : R[X]) (
r : A) : aeval r (expand R p P) = aeval (r ^ p) P
参数：p : Nat；P : R[X]；r : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_add`：aeval_add : aeval x (p + q) = aeval x p + aeval x 
q
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem expand_aeval {A : Type*} [Semiring A] [Algebra R A] (p : ℕ) (P : R[X]) (r : A) :
    aeval r (expand R p P) = aeval (r ^ p) P := by
  refine Polynomial.induction_on P (fun a => by simp) (fun f g hf hg => ?_) fun n a _ => by simp
  rw [map_add, aeval_add, aeval_add, hf, hg]

/-- The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`. -/
/-
**Polynomial.contract** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：contract (p : Nat) (f : R[X]) : R[X]
参数：p : Nat；f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of `expand`: sends `∑ aₙ xⁿᵖ` to `∑ aₙ xⁿ`.
-/
noncomputable def contract (p : ℕ) (f : R[X]) : R[X] :=
  ∑ n ∈ range (f.natDegree + 1), monomial n (f.coeff (n * p))
/-
**Polynomial.coeff_contract** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_contract {p : Nat} (hp : p != 0) (f : R[X]) (n : Nat) : (contract p 
f).coeff n = f.coeff (n * p)
参数：hp : p != 0；f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem coeff_contract {p : ℕ} (hp : p ≠ 0) (f : R[X]) (n : ℕ) :
    (contract p f).coeff n = f.coeff (n * p) := by
  simp only [contract, coeff_monomial, sum_ite_eq', finsetSum_coeff, mem_range, not_lt,
    ite_eq_left_iff]
  intro hn
  apply (coeff_eq_zero_of_natDegree_lt _).symm
  calc
    f.natDegree < f.natDegree + 1 := Nat.lt_succ_self _
    _ ≤ n * 1 := by simpa only [mul_one] using hn
    _ ≤ n * p := by gcongr; exact hp.bot_lt
/-
**Polynomial.map_contract** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_contract {p : Nat} (hp : p != 0) {f : R ->+* S} {q : R[X]} : (q.contra
ct p).map f = (q.map f).contract p
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_contract {p : ℕ} (hp : p ≠ 0) {f : R →+* S} {q : R[X]} :
    (q.contract p).map f = (q.map f).contract p := ext fun n ↦ by
  simp only [coeff_map, coeff_contract hp]
/-
**Polynomial.contract_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：contract_expand {f : R[X]} (hp : p != 0) : contract p (expand R p f) = f
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem contract_expand {f : R[X]} (hp : p ≠ 0) : contract p (expand R p f) = f := by
  ext
  simp [coeff_contract hp, coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]
/-
**Polynomial.contract_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：contract_one {f : R[X]} : contract 1 f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem contract_one {f : R[X]} : contract 1 f = f :=
  ext fun n ↦ by rw [coeff_contract one_ne_zero, mul_one]
/-
**Polynomial.contract_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] (p : ℕ) (r : R), Polynomial.contrac
t p (Polynomial.C r) = Polynomial.C r
参数：p : ℕ；r : R；Polynomial.C r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem contract_C (r : R) : contract p (C r) = C r := by simp [contract]
/-
**Polynomial.contract_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：contract_add {p : Nat} (hp : p != 0) (f g : R[X]) : contract p (f + g) = c
ontract p f + contract p g
参数：hp : p != 0；f g : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem contract_add {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f + g) = contract p f + contract p g := by
  ext; simp_rw [coeff_add, coeff_contract hp, coeff_add]
/-
**Polynomial.contract_mul_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：contract_mul_expand {p : Nat} (hp : p != 0) (f g : R[X]) : contract p (f *
 expand R p g) = contract p f * g
参数：hp : p != 0；f g : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_add_iff_left`：∀ {k m n : ℕ}, k ∣ n → (k ∣ m ↔ k ∣ m + n)
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_right_cancel_iff`：∀ {m : ℕ}, 0 < m → ∀ {n k : ℕ}, n * m = k * m 
↔ n = k
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 31 条，此处仅展示前 30 条）
-/
theorem contract_mul_expand {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    contract p (f * expand R p g) = contract p f * g := by
  ext n
  rw [coeff_contract hp, coeff_mul, coeff_mul, ← sum_subset
    (s₁ := (antidiagonal n).image fun x ↦ (x.1 * p, x.2 * p)), sum_image]
  · simp_rw [coeff_expand_mul hp.bot_lt, coeff_contract hp]
  · intro x hx y hy eq; simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp.bot_lt] using eq
  · simp_rw [subset_iff, mem_image, mem_antidiagonal]; rintro _ ⟨x, rfl, rfl⟩; simp_rw [add_mul]
  simp_rw [mem_image, mem_antidiagonal]
  intro ⟨x, y⟩ eq nex
  by_cases h : p ∣ y
  · obtain ⟨x, rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left h).mpr (eq ▸ dvd_mul_left p n)
    obtain ⟨y, rfl⟩ := h
    refine (nex ⟨⟨x, y⟩, (Nat.mul_right_cancel_iff hp.bot_lt).mp ?_, by simp_rw [mul_comm]⟩).elim
    rw [← eq, mul_comm, mul_add]
  · rw [coeff_expand hp.bot_lt, if_neg h, mul_zero]
/-
**Polynomial.isCoprime_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {f g : Polynomial R} {p : ℕ},   p ≠
 0 → (IsCoprime ((Polynomial.expand R p) f) ((Polynomial.expand R p) g) ↔ IsCopr
ime f g)
参数：IsCoprime ((Polynomial.expand R p) f) ((Polynomial.expand R p) g) ↔ IsCoprime
 f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.contract_mul_expand`：contract_mul_expand {p : Nat} (hp : p !=
 0) (f g : R[X]) : contract p (f * expand R p g) = contract p f * g
· 使用定理 `Polynomial.contract_add`：contract_add {p : Nat} (hp : p != 0) (f g : R[X
]) : contract p (f + g) = contract p f + contract p g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.contract_C`：∀ {R : Type u} [inst : CommSemiring R] (p : ℕ) (r
 : R), Polynomial.contract p (Polynomial.C r) = Polynomial.C r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoprime.map`：IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemir
ing S] (f : R ->+* S) : IsCoprime (f x) (f y)
-/
@[simp] theorem isCoprime_expand {f g : R[X]} {p : ℕ} (hp : p ≠ 0) :
    IsCoprime (expand R p f) (expand R p g) ↔ IsCoprime f g :=
  ⟨fun ⟨a, b, eq⟩ ↦ ⟨contract p a, contract p b, by
    simp_rw [← contract_mul_expand hp, ← contract_add hp, eq, ← C_1, contract_C]⟩, (·.map _)⟩

section ExpChar

/-
**Polynomial.expand_contract** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial
.derivative f = 0) (hp : p != 0) : expand R p (contract p f) = f
参数：hf : Polynomial.derivative f = 0；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Polynomial.coeff_contract`：coeff_contract {p : Nat} (hp : p != 0) (f : R
[X]) (n : Nat) : (contract p f).coeff n = f.coeff (n * p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Polynomial.coeff_derivative`：coeff_derivative (p : R[X]) (n : Nat) : coe
ff (derivative p) n = coeff p (n + 1) * (n + 1)
· 使用定理 `zero_eq_mul`：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
-/
theorem expand_contract [CharP R p] [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0)
    (hp : p ≠ 0) : expand R p (contract p f) = f := by
  ext n
  rw [coeff_expand hp.bot_lt, coeff_contract hp]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rcases n with - | n
    · exact absurd (dvd_zero p) h
    have := coeff_derivative f n
    rw [hf, coeff_zero, zero_eq_mul] at this
    rcases this with h' | _
    · rw [h']
    rename_i _ _ _ h'
    rw [← Nat.cast_succ, CharP.cast_eq_zero_iff R p] at h'
    exact absurd h' h

variable [ExpChar R p]
/-
**Polynomial.expand_contract'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative
 f = 0) : expand R p (contract p f) = f
参数：hf : Polynomial.derivative f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `Polynomial.contract_one`：contract_one {f : R[X]} : contract 1 f = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_contract`：expand_contract [CharP R p] [NoZeroDivisors 
R] {f : R[X]} (hf : Polynomial.derivative f = 0) (hp : p != 0) : expand R p (con
tract p f) = f
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
-/
theorem expand_contract' [NoZeroDivisors R] {f : R[X]} (hf : Polynomial.derivative f = 0) :
    expand R p (contract p f) = f := by
  obtain _ | @⟨_, hprime, hchar⟩ := ‹ExpChar R p›
  · rw [expand_one, contract_one]
  · have := Fact.mk hchar; exact expand_contract p hf hprime.ne_zero
/-
**Polynomial.map_frobenius_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_frobenius_expand (f : R[X]) : map (frobenius R p) (expand R p f) = f ^
 p
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用引理 `add_pow_expChar`：add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p
· 使用定理 `Polynomial.expand_monomial`：expand_monomial (r : R) : expand R p (monomi
al q r) = monomial (q * p) r
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
（共 34 条，此处仅展示前 30 条）
-/
theorem map_frobenius_expand (f : R[X]) : map (frobenius R p) (expand R p f) = f ^ p := by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← C.map_pow, frobenius_def]
    ring
/-
**Polynomial.map_iterateFrobenius_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_iterateFrobenius_expand (f : R[X]) (n : Nat) : map (iterateFrobenius R
 p n) (expand R (p ^ n) f) = f ^ p ^ n
参数：f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iterateFrobenius_zero`：iterateFrobenius_zero : iterateFrobenius R p 0 = 
RingHom.id R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Polynomial.map_frobenius_expand`：map_frobenius_expand (f : R[X]) : map (
frobenius R p) (expand R p f) = f ^ p
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `iterateFrobenius.congr_simp`：∀ (R : Type u_3) [inst : CommSemiring R] (p
 p_1 : ℕ) (e_p : p = p_1) (n n_1 : ℕ),   n = n_1 → ∀ [inst_1 : ExpChar R p], ite
rateFrobenius R p…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `iterateFrobenius_add`：iterateFrobenius_add : iterateFrobenius R p (m + n
) = (iterateFrobenius R p m).comp (iterateFrobenius R p n)
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
-/
theorem map_iterateFrobenius_expand (f : R[X]) (n : ℕ) :
    map (iterateFrobenius R p n) (expand R (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end ExpChar

end CommSemiring

section rootMultiplicity

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

/-
**Polynomial.rootMultiplicity_expand_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_expand_pow : (expand R (p ^ n) f).rootMultiplicity r = p 
^ n * f.rootMultiplicity (r ^ p ^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.rootMultiplicity_zero`：rootMultiplicity_zero {x : R} : rootMu
ltiplicity x 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
· 使用定理 `Polynomial.expand_C`：expand_C (r : R) : expand R p (C r) = C r
· 使用引理 `sub_pow_expChar_pow`：sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n -
 y ^ p ^ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.rootMultiplicity_mul_X_sub_C_pow`：rootMultiplicity_mul_X_sub_
C_pow {p : R[X]} {a : R} {n : Nat} (h : p != 0) : (p * (X - C a) ^ n).rootMultip
licity a = p.rootMultiplicity a +…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.expand_ne_zero`：expand_ne_zero {p : Nat} (hp : 0 < p) {f : R[
X]} : expand R p f != 0 ↔ f != 0
（共 39 条，此处仅展示前 30 条）
-/
theorem rootMultiplicity_expand_pow :
    (expand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n) := by
  obtain rfl | h0 := eq_or_ne f 0; · simp
  obtain ⟨g, hg, ndvd⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h0 (r ^ p ^ n)
  rw [dvd_iff_isRoot, ← eval_X (x := r), ← eval_pow, ← isRoot_comp, ← expand_eq_comp_X_pow] at ndvd
  conv_lhs => rw [hg, map_mul, map_pow, map_sub, expand_X, expand_C, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_comm, rootMultiplicity_mul_X_sub_C_pow (expand_ne_zero (expChar_pow_pos R p n)
      |>.mpr <| right_ne_zero_of_mul <| hg ▸ h0), rootMultiplicity_eq_zero ndvd, zero_add]
/-
**Polynomial.rootMultiplicity_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_expand : (expand R p f).rootMultiplicity r = p * f.rootMu
ltiplicity (r ^ p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.rootMultiplicity_expand_pow`：rootMultiplicity_expand_pow : (e
xpand R (p ^ n) f).rootMultiplicity r = p ^ n * f.rootMultiplicity (r ^ p ^ n)
-/
theorem rootMultiplicity_expand :
    (expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p, rootMultiplicity_expand_pow]

end rootMultiplicity

section IsDomain

variable (R : Type u) [CommRing R] [IsDomain R]

/-
**Polynomial.isLocalHom_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isLocalHom_expand {p : Nat} (hp : 0 < p) : IsLocalHom (expand R p)
参数：hp : 0 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_eq_C`：expand_eq_C {p : Nat} (hp : 0 < p) {f : R[X]} {r
 : R} : expand R p f = C r ↔ f = C r
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Polynomial.coeff_expand`：coeff_expand {p : Nat} (hp : 0 < p) (f : R[X]) 
(n : Nat) : (expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
-/
theorem isLocalHom_expand {p : ℕ} (hp : 0 < p) : IsLocalHom (expand R p) := by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2
  rw [hf2, isUnit_C] at hf1; rw [expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

variable {R}
/-
**Polynomial.of_irreducible_expand** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：of_irreducible_expand {p : Nat} (hp : p != 0) {f : R[X]} (hf : Irreducible
 (expand R p f)) : Irreducible f
参数：hp : p != 0；hf : Irreducible (expand R p f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isLocalHom_expand`：isLocalHom_expand {p : Nat} (hp : 0 < p) :
 IsLocalHom (expand R p)
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用引理 `Irreducible.of_map`：Irreducible.of_map [FunLike F M N] [MonoidHomClass F
 M N] [IsLocalHom f] (hfx : Irreducible (f x)) : Irreducible x where not_isUnit 
hu
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : R[X]} (hf : Irreducible (expand R p f)) :
    Irreducible f :=
  let _ := isLocalHom_expand R hp.bot_lt
  hf.of_map
/-
**Polynomial.of_irreducible_expand_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：of_irreducible_expand_pow {p : Nat} (hp : p != 0) {f : R[X]} {n : Nat} : I
rreducible (expand R (p ^ n) f) -> Irreducible f
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.of_irreducible_expand`：of_irreducible_expand {p : Nat} (hp : 
p != 0) {f : R[X]} (hf : Irreducible (expand R p f)) : Irreducible f
· 使用定理 `Polynomial.expand_expand`：expand_expand (f : R[X]) : expand R p (expand 
R q f) = expand R (p * q) f
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem of_irreducible_expand_pow {p : ℕ} (hp : p ≠ 0) {f : R[X]} {n : ℕ} :
    Irreducible (expand R (p ^ n) f) → Irreducible f :=
  Nat.recOn n (fun hf => by rwa [pow_zero, expand_one] at hf) fun n ih hf =>
    ih <| of_irreducible_expand hp <| by
      rw [pow_succ'] at hf
      rwa [expand_expand]

end IsDomain

end Polynomial

