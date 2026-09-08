/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.IdempotentFG

/-!

# Standard etale maps

## Main definitions
- `StandardEtalePair`:
  A pair `f g : R[X]` such that `f` is monic and `f'` is invertible in `R[X][1/g]`.
- `StandardEtalePair`: The standard etale algebra corresponding to a `StandardEtalePair`.
- `StandardEtalePair.equivPolynomialQuotient`   : `P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.equivAwayAdjoinRoot`       : `P.Ring ≃ (R[X]/f)[1/g]`
- `StandardEtalePair.equivAwayQuotient`         : `P.Ring ≃ R[X][1/g]/f`
- `StandardEtalePair.equivMvPolynomialQuotient` : `P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩`
- `StandardEtalePair.homEquiv`:
  Maps out of `P.Ring` corresponds to `x` such that `f(x) = 0` and `g(x)` is invertible.
- We also provide the instance that `P.Ring` is etale over `R`.

- `Algebra.IsStandardEtale`: The class of standard etale algebras.

-/

@[expose] public section

universe u

open Polynomial

open scoped Bivariate

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

variable (R) in
/-- A `StandardEtalePair R` is a pair `f g : R[X]` such that `f` is monic,
and `f'` is invertible in `R[X][1/g]/f`. -/
/-
**StandardEtalePair** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：StandardEtalePair : Type _ where /-- The monic polynomial to be quotiented
 out in a standard etale algebra. -/ f : R[X] monic_f : f.Monic /-- The polynomi
al to be localized away from in a standard etale algebra. -/ g : R[X] cond : exi
sts p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n  variable (P : StandardEtalePair
 R)  /-- The standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `Standar
dEtalePair R`. Also see `equivPolynomialQuotient : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩` `
equivAwayAdjoinRoot : P.Ri
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `StandardEtalePair R` is a pair `f g : R[X]` such that `f` is monic,
and `f'` is invertible in `R[X][1/g]/f`. -/
-/
structure StandardEtalePair : Type _ where
  /-- The monic polynomial to be quotiented out in a standard etale algebra. -/
  f : R[X]
  monic_f : f.Monic
  /-- The polynomial to be localized away from in a standard etale algebra. -/
  g : R[X]
  cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n

variable (P : StandardEtalePair R)

/-- The standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `StandardEtalePair R`.
Also see
`equivPolynomialQuotient   : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
`equivAwayAdjoinRoot       : P.Ring ≃ (R[X]/f)[1/g]`
`equivAwayQuotient         : P.Ring ≃ R[X][1/g]/f`
`equivMvPolynomialQuotient : P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩` -/
/-
**StandardEtalePair.Ring** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → StandardEtalePair R → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` associated to a `StandardEtalePai
r R`.
Also see
`equivPolynomialQuotient   : P.Ring ≃ R[X][Y]/⟨f, Yg-1⟩`
`equivAwayAdjoinRoot       : P.Ring ≃ (R[X]/f)[1/g]`
`equivAwayQuotient         : P.Ring ≃ R[X][1/g]/f`
`equivMvPolynomialQuotient : P.Ring ≃ R[X, Y]/⟨f, Yg-1⟩`
-/
protected def StandardEtalePair.Ring := R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1}
  deriving CommRing, Algebra R

namespace StandardEtalePair

/-- The `X` in the standard etale algebra `R[X][Y]/⟨f, Yg-1⟩`. -/
/-
**StandardEtalePair.X** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → (P : StandardEtalePair R) → P.Ring
参数：P : StandardEtalePair R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `X` in the standard etale algebra `R[X][Y]/⟨f, Yg-1⟩`.
-/
protected def X : P.Ring := Ideal.Quotient.mk _ (C .X)

/-- There is a map from a standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` to `S` sending `X` to `x` iff
`f(x) = 0` and `g(x)` is invertible. Also see `StandardEtalePair.homEquiv`. -/
/-
**StandardEtalePair.HasMap** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：HasMap (x : S) : Prop
参数：x : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a map from a standard etale algebra `R[X][Y]/⟨f, Yg-1⟩` to `S` sending 
`X` to `x` iff
`f(x) = 0` and `g(x)` is invertible. Also see `StandardEtalePair.homEquiv`.
-/
def HasMap (x : S) : Prop :=
  aeval x P.f = 0 ∧ IsUnit (aeval x P.g)

/-- The map `R[X][Y]/⟨f, Yg-1⟩ →ₐ[R] S` sending `X` to `x`, given `P.HasMap x`. -/
/-
**StandardEtalePair.lift** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：lift (x : S) (h : P.HasMap x) : P.Ring ->ₐ[R] S
参数：x : S；h : P.HasMap x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `R[X][Y]/⟨f, Yg-1⟩ →ₐ[R] S` sending `X` to `x`, given `P.HasMap x`.
-/
def lift (x : S) (h : P.HasMap x) : P.Ring →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAeval x ↑(h.2.unit⁻¹))
    (Ideal.span_le (I := RingHom.ker _).mpr (by simp [Set.pair_subset_iff, h.1]))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**StandardEtalePair.lift_X** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：lift_X (x : S) (h : P.HasMap x) : P.lift x h P.X = x
参数：x : S；h : P.HasMap x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aevalAevalEquiv_apply_apply`：∀ (R : Type u_1) (A : Type u_2) 
[inst : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A] (xy : A
 × A)   (x : Polynomial (Pol…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_X (x : S) (h : P.HasMap x) : P.lift x h P.X = x := by
  simp [lift, StandardEtalePair.Ring, StandardEtalePair.X]

variable {P} in
/-
**StandardEtalePair.HasMap.map** 是 Mathlib 中的一个定理，位于命名空间 `StandardEtalePair.HasM
ap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] {P : StandardEtalePair R} {x : S},   P.HasMap x → ∀ (f : S →ₐ[R] T), P.HasM
ap (f x)
参数：f : S →ₐ[R] T；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma HasMap.map {x : S} (h : P.HasMap x) (f : S →ₐ[R] T) : P.HasMap (f x) :=
  ⟨by simp [aeval_algHom, h.1], by simpa [aeval_algHom] using h.2.map f⟩
/-
**StandardEtalePair.HasMap.isUnit_derivative_f** 是 Mathlib 中的一个定理，位于命名空间 `Standa
rdEtalePair.HasMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   (P : StandardEtalePair R) {x : S}, P.HasMap x → IsUnit 
((Polynomial.aeval x) (Polynomial.derivative P.f))
参数：P : StandardEtalePair R；(Polynomial.aeval x) (Polynomial.derivative P.f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StandardEtalePair.cond`：∀ {R : Type u_1} [inst : CommRing R] (self : Sta
ndardEtalePair R),   ∃ p₁ p₂ n, Polynomial.derivative self.f * p₁ + self.f * p₂ 
= self.g ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma HasMap.isUnit_derivative_f {x : S} (h : P.HasMap x) :
    IsUnit (P.f.derivative.aeval x) := by
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  have : aeval x P.f.derivative ∣ aeval x P.g ^ n :=
    ⟨_, by simpa [h.1] using congr(aeval x $e.symm)⟩
  exact isUnit_of_dvd_unit this (.pow _ h.2)

set_option backward.isDefEq.respectTransparency false in
/-
**StandardEtalePair.aeval_X_g_mul_mk_X** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtaleP
air`。
形式化陈述：aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
-/
lemma aeval_X_g_mul_mk_X : aeval P.X P.g * Ideal.Quotient.mk _ .X = 1 := by
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  dsimp [StandardEtalePair.Ring]
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), ← sub_eq_zero, ← map_sub, mul_comm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-
**StandardEtalePair.hasMap_X** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：hasMap_X : P.HasMap P.X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `StandardEtalePair.aeval_X_g_mul_mk_X`：aeval_X_g_mul_mk_X : aeval P.X P.g
 * Ideal.Quotient.mk _ .X = 1
-/
lemma hasMap_X : P.HasMap P.X :=
  have : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  ⟨this ▸ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)),
    IsUnit.of_mul_eq_one _ P.aeval_X_g_mul_mk_X⟩

set_option backward.isDefEq.respectTransparency false in
variable {P} in
@[ext]
/-
**StandardEtalePair.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：hom_ext {f g : P.Ring ->ₐ[R] S} (H : f P.X = g P.X) : f = g
参数：H : f P.X = g P.X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.Quotient.algHom_ext`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : Comm
Semiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] {I : Ideal A}   [inst_3 :
 I.IsTwoSided] …
· 使用定理 `Polynomial.algHom_ext'`：algHom_ext' {f g : A[X] ->ₐ[R] B} (hC : f.comp C
AlgHom = g.comp CAlgHom) (hX : f X = g X) : f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `StandardEtalePair.hasMap_X`：hasMap_X : P.HasMap P.X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 
↔ ↑u⁻¹ = a
· 使用引理 `StandardEtalePair.aeval_X_g_mul_mk_X`：aeval_X_g_mul_mk_X : aeval P.X P.g
 * Ideal.Quotient.mk _ .X = 1
· 使用定理 `Units.coe_map_inv`：coe_map_inv (f : M ->* N) (u : Mˣ) : ↑(map f u)⁻¹ = f
 ↑u⁻¹
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
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
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
-/
lemma hom_ext {f g : P.Ring →ₐ[R] S} (H : f P.X = g P.X) : f = g := by
  have H : (f.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom =
    (g.comp (Ideal.Quotient.mkₐ R _)).comp CAlgHom := Polynomial.algHom_ext (by simpa)
  have H' : aeval (R := R) P.X = (Ideal.Quotient.mkₐ _ _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  refine Ideal.Quotient.algHom_ext _ (Polynomial.algHom_ext' H ?_)
  change f.toMonoidHom (Ideal.Quotient.mk _ .X) = g.toMonoidHom (Ideal.Quotient.mk _ .X)
  rw [← show (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X from
    Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X, ← Units.coe_map_inv, ← Units.coe_map_inv]
  congr 2
  ext
  simpa [H'] using! congr($H _)

@[simp]
/-
**StandardEtalePair.lift_X_left** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：lift_X_left : P.lift P.X P.hasMap_X = .id _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StandardEtalePair.hom_ext`：hom_ext {f g : P.Ring ->ₐ[R] S} (H : f P.X = 
g P.X) : f = g
· 使用引理 `StandardEtalePair.hasMap_X`：hasMap_X : P.HasMap P.X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StandardEtalePair.lift_X`：lift_X (x : S) (h : P.HasMap x) : P.lift x h P
.X = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_X_left : P.lift P.X P.hasMap_X = .id _ _ :=
  P.hom_ext (by simp)
/-
**StandardEtalePair.inv_aeval_X_g** 是 Mathlib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：inv_aeval_X_g : (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `StandardEtalePair.hasMap_X`：hasMap_X : P.HasMap P.X
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Units.mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 
↔ ↑u⁻¹ = a
· 使用引理 `StandardEtalePair.aeval_X_g_mul_mk_X`：aeval_X_g_mul_mk_X : aeval P.X P.g
 * Ideal.Quotient.mk _ .X = 1
-/
lemma inv_aeval_X_g :
    (↑P.hasMap_X.2.unit⁻¹ : P.Ring) = Ideal.Quotient.mk _ .X :=
  Units.mul_eq_one_iff_inv_eq.mp P.aeval_X_g_mul_mk_X

/-- Maps out of `R[X][Y]/⟨f, Yg-1⟩` corresponds bijectively with
`x` such that `f(x) = 0` and `g(x)` is invertible. -/
@[simps]
/-
**StandardEtalePair.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：homEquiv : (P.Ring ->ₐ[R] S) ≃ { x : S // P.HasMap x } where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps out of `R[X][Y]/⟨f, Yg-1⟩` corresponds bijectively with
`x` such that `f(x) = 0` and `g(x)` is invertible.
-/
def homEquiv : (P.Ring →ₐ[R] S) ≃ { x : S // P.HasMap x } where
  toFun f := ⟨f P.X, hasMap_X.map f⟩
  invFun x := P.lift x.1 x.2
  left_inv f := P.hom_ext (by simp)
  right_inv x := by simp
/-
**StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot** 是 Math
lib 中的一个引理，位于命名空间 `StandardEtalePair`。
形式化陈述：existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot (I : Ideal S) (hI : I 
^ 2 = ⊥) (x : S) (hx : P.HasMap (Ideal.Quotient.mk I x)) : exists! ε, ε in I ∧ P
.HasMap (x + ε)
参数：I : Ideal S；hI : I ^ 2 = ⊥；x : S；hx : P.HasMap (Ideal.Quotient.mk I x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `StandardEtalePair.cond`：∀ {R : Type u_1} [inst : CommRing R] (self : Sta
ndardEtalePair R),   ∃ p₁ p₂ n, Polynomial.derivative self.f * p₁ + self.f * p₂ 
= self.g ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 89 条，此处仅展示前 30 条）
-/
lemma existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
    (I : Ideal S) (hI : I ^ 2 = ⊥) (x : S) (hx : P.HasMap (Ideal.Quotient.mk I x)) :
    ∃! ε, ε ∈ I ∧ P.HasMap (x + ε) := by
  have hf := Ideal.Quotient.eq_zero_iff_mem.mp
    ((aeval_algHom_apply (Ideal.Quotient.mkₐ R I) _ _).symm.trans hx.1)
  obtain ⟨⟨_, a, ha, -⟩, rfl⟩ := hx.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, ← map_mul, ← map_one
    (Ideal.Quotient.mkₐ R I), Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  obtain ⟨p₁, p₂, n, e⟩ := P.cond
  apply_fun aeval x at e
  simp only [map_add, map_mul, map_pow] at e
  obtain ⟨ε, hεI, b, hb⟩ : ∃ ε ∈ I, ∃ b, aeval x (derivative P.f) * b = 1 + ε := by
    refine ⟨_, ?_, (a ^ n * aeval x p₁), sub_eq_iff_eq_add'.mp rfl⟩
    convert_to (aeval x P.g * a) ^ n - 1 - aeval x P.f * (a ^ n * aeval x p₂) ∈ I
    · linear_combination a ^ n * e
    · exact sub_mem (Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one _ _) ha) (I.mul_mem_right _ hf)
  have : aeval x P.f ^ 2 = 0 := hI.le (Ideal.pow_mem_pow hf 2)
  have : aeval x P.f * ε = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hf hεI)
  refine ⟨aeval x P.f * -b, ⟨I.mul_mem_right _ hf, ?_, ?_⟩, ?_⟩
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by grind)]; grind
  · rw [← IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩, ← Ideal.Quotient.mkₐ_eq_mk R,
      ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right _ hf), add_zero]
    exact hx.2
  · rintro ε' ⟨hε'I, hε', hε''⟩
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (hI.le (Ideal.pow_mem_pow hε'I 2))] at hε'
    have : ε * ε' = 0 := ((pow_two _).symm.trans hI).le (Ideal.mul_mem_mul hεI hε'I)
    grind

-- This works even if `f` is not monic. Generalize if we care.
/-
**StandardEtalePair.** 是 Mathlib 中的一个实例，位于命名空间 `StandardEtalePair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.FormallyEtale R P.Ring := by
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun S _ _ I hI ↦ ?_
  rw [← P.homEquiv.symm.bijective.of_comp_iff, ← P.homEquiv.bijective.of_comp_iff']
  suffices ∀ x, P.HasMap (Ideal.Quotient.mk I x) → ∃! a : { x : S // P.HasMap x }, a - x ∈ I by
    simpa [Function.bijective_iff_existsUnique, Ideal.Quotient.mk_surjective.forall,
      Subtype.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  intro x hx
  obtain ⟨ε, ⟨hεI, hε⟩, H⟩ := P.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot I hI _ hx
  exact ⟨⟨x + ε, hε⟩, by simpa, fun y hy ↦
    Subtype.ext (sub_eq_iff_eq_add'.mp (H _ ⟨hy, by simpa using y.2⟩))⟩
/-
**StandardEtalePair.** 是 Mathlib 中的一个实例，位于命名空间 `StandardEtalePair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.Etale R P.Ring where
  finitePresentation := .quotient (Submodule.fg_span (by simp))

/-- An `AlgEquiv` between `P.Ring` and `R[X][Y]/⟨f, Yg-1⟩`,
to not abuse the defeq between the two. -/
/-
**StandardEtalePair.equivPolynomialQuotient** 是 Mathlib 中的一个定义，位于命名空间 `StandardE
talePair`。
形式化陈述：equivPolynomialQuotient : P.Ring ≃ₐ[R] R[X][Y] ⧸ Ideal.span {C P.f, Y * C 
P.g - 1}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AlgEquiv` between `P.Ring` and `R[X][Y]/⟨f, Yg-1⟩`,
to not abuse the defeq between the two.
-/
def equivPolynomialQuotient :
    P.Ring ≃ₐ[R] R[X][Y] ⧸ Ideal.span {C P.f, Y * C P.g - 1} := .refl ..

set_option backward.isDefEq.respectTransparency.types false in
/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ (R[X]/f)[1/g]` -/
/-
**StandardEtalePair.equivAwayAdjoinRoot** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtale
Pair`。
形式化陈述：equivAwayAdjoinRoot : P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.
g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R[X][Y]/⟨f, Yg-1⟩ ≃ (R[X]/f)[1/g]`
-/
def equivAwayAdjoinRoot :
    P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := by
  refine .ofAlgHom (P.lift (algebraMap (AdjoinRoot P.f) _ (.root P.f)) ⟨?_, ?_⟩)
    (IsLocalization.Away.liftAlgHom (AdjoinRoot.mk P.f P.g)
      (f := AdjoinRoot.liftAlgHom _ _ P.X P.hasMap_X.1) P.hasMap_X.2) ?_ ?_
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
    exact IsLocalization.Away.algebraMap_isUnit ..
  · ext; simp [Algebra.algHom]
  · ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ R[X][1/g]/f` -/
/-
**StandardEtalePair.equivAwayQuotient** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePa
ir`。
形式化陈述：equivAwayQuotient : P.Ring ≃ₐ[R] Localization.Away P.g ⧸ Ideal.span {algeb
raMap _ (Localization.Away P.g) P.f}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R[X][Y]/⟨f, Yg-1⟩ ≃ R[X][1/g]/f`
-/
def equivAwayQuotient :
    P.Ring ≃ₐ[R] Localization.Away P.g ⧸ Ideal.span {algebraMap _ (Localization.Away P.g) P.f} := by
  refine .ofAlgHom (P.lift (algebraMap R[X] _ .X) ⟨?_, ?_⟩)
    (Ideal.Quotient.liftₐ _ (IsLocalization.Away.liftAlgHom (P.g) P.hasMap_X.2) ?_) ?_ ?_
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      Ideal.Quotient.algebraMap_eq, aeval_X_left_apply, Ideal.Quotient.mk_singleton_self]
  · rw [aeval_algebraMap_apply, IsScalarTower.algebraMap_apply _ (Localization.Away P.g) (_ ⧸ _),
      aeval_X_left_apply]
    exact (IsLocalization.Away.algebraMap_isUnit ..).map _
  · change Ideal.span _ ≤ RingHom.ker _
    simpa [Ideal.span_le] using P.hasMap_X.1
  · apply Ideal.Quotient.algHom_ext
    ext
    simp [Algebra.algHom, IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]
  · ext; simp [IsScalarTower.algebraMap_apply R[X] (Localization.Away P.g) (_ ⧸ _),
      -Ideal.Quotient.mk_algebraMap]

/-- `R[X][Y]/⟨f, Yg-1⟩ ≃ R[X, Y]/⟨f, Yg-1⟩` -/
/-
**StandardEtalePair.equivMvPolynomialQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Standar
dEtalePair`。
形式化陈述：equivMvPolynomialQuotient : P.Ring ≃ₐ[R] MvPolynomial (Fin 2) R ⧸ Ideal.sp
an {Bivariate.equivMvPolynomial R (C P.f), Bivariate.equivMvPolynomial R (.X * C
 P.g - 1)}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R[X][Y]/⟨f, Yg-1⟩ ≃ R[X, Y]/⟨f, Yg-1⟩`
-/
def equivMvPolynomialQuotient :
    P.Ring ≃ₐ[R] MvPolynomial (Fin 2) R ⧸ Ideal.span
      {Bivariate.equivMvPolynomial R (C P.f), Bivariate.equivMvPolynomial R (.X * C P.g - 1)} :=
  Ideal.quotientEquivAlg _ _ (Bivariate.equivMvPolynomial R)
    (by simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]; rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**StandardEtalePair.equivMvPolynomialQuotient_symm_apply** 是 Mathlib 中的一个引理，位于命名
空间 `StandardEtalePair`。
形式化陈述：equivMvPolynomialQuotient_symm_apply : P.equivMvPolynomialQuotient.symm (I
deal.Quotient.mk _ (.X 0)) = P.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_symm_X_0`：equivMvPolynomial_symm_
X_0 : (equivMvPolynomial R).symm (.X 0) = C X
-/
lemma equivMvPolynomialQuotient_symm_apply :
    P.equivMvPolynomialQuotient.symm (Ideal.Quotient.mk _ (.X 0)) = P.X := by
  simp [equivMvPolynomialQuotient, StandardEtalePair.Ring]; rfl

/-- Mapping a standard etale pair under a ring homomorphism. -/
/-
**StandardEtalePair.map** 是 Mathlib 中的一个定义，位于命名空间 `StandardEtalePair`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} → [inst : CommRing R] → [inst_1 : CommRi
ng S] → StandardEtalePair R → (R →+* S) → StandardEtalePair S
参数：R →+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping a standard etale pair under a ring homomorphism.
-/
@[simps] protected noncomputable def map (f : R →+* S) : StandardEtalePair S where
  f := P.f.map f
  monic_f := P.monic_f.map _
  g := P.g.map f
  cond := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    refine ⟨p₁.map f, p₂.map f, n, ?_⟩
    simp [← Polynomial.map_mul, ← Polynomial.map_add, e]
/-
**StandardEtalePair.HasMap.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `StandardEta
lePair.HasMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (P : StandardEtalePair R) [inst_5 : Algebra S T] [IsScalarTower R S T]   {x
 : T}, P.HasMap x → (P.map (algebraMap R S)).HasMap x
参数：P : StandardEtalePair R；P.map (algebraMap R S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StandardEtalePair.map_f`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : CommRing S] (P : StandardEtalePair R) (f : R →+* S),   (P.map f).
f = Polynomia…
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `StandardEtalePair.map_g`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : CommRing S] (P : StandardEtalePair R) (f : R →+* S),   (P.map f).
g = Polynomia…
-/
lemma HasMap.map_algebraMap [Algebra S T] [IsScalarTower R S T] {x : T} (H : P.HasMap x) :
    (P.map (algebraMap R S)).HasMap x := by
  simpa [HasMap]

end StandardEtalePair

/-- An isomorphism to the standard etale algebra of a standard etale pair. -/
/-
**StandardEtalePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_4) → (S : Type u_5) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Type (max u_4 u_5)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism to the standard etale algebra of a standard etale pair.
-/
structure StandardEtalePresentation (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] extends
    P : StandardEtalePair R where
  /-- The image of X in a `StandardEtalePresentation`. -/
  x : S
  hasMap : P.HasMap x
  lift_bijective : Function.Bijective (P.lift x hasMap)

variable (P : StandardEtalePresentation R S)

/-- The isomorphism to the standard etale algebra given a `StandardEtalePresentation`. -/
/-
**StandardEtalePresentation.equivRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.equivRing : S ≃ₐ[R] P.Ring
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StandardEtalePresentation.hasMap`：∀ {R : Type u_4} {S : Type u_5} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : StandardEta
lePresentation R S), s…
· 使用定理 `StandardEtalePresentation.lift_bijective`：∀ {R : Type u_4} {S : Type u_5
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Sta
ndardEtalePresentation R S), F…

--- 原说明 ---
The isomorphism to the standard etale algebra given a `StandardEtalePresentation
`.
-/
def StandardEtalePresentation.equivRing : S ≃ₐ[R] P.Ring :=
  .symm <| .ofBijective _ P.lift_bijective

@[simp]
/-
**StandardEtalePresentation.equivRing_symm_X** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.equivRing_symm_X : P.equivRing.symm P.X = P.x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StandardEtalePair.lift_X`：lift_X (x : S) (h : P.HasMap x) : P.lift x h P
.X = x
· 使用定理 `StandardEtalePresentation.hasMap`：∀ {R : Type u_4} {S : Type u_5} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : StandardEta
lePresentation R S), s…
-/
lemma StandardEtalePresentation.equivRing_symm_X : P.equivRing.symm P.X = P.x :=
  P.lift_X _ P.hasMap

@[simp]
/-
**StandardEtalePresentation.equivRing_x** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.equivRing_x : P.equivRing P.x = P.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用引理 `StandardEtalePresentation.equivRing_symm_X`：StandardEtalePresentation.eq
uivRing_symm_X : P.equivRing.symm P.X = P.x
-/
lemma StandardEtalePresentation.equivRing_x : P.equivRing P.x = P.X :=
  (P.equivRing.symm_apply_eq.mp P.equivRing_symm_X).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.Presentation` associated to a standard etale presentation. -/
@[simps! relation val]
/-
**StandardEtalePresentation.toPresentation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.toPresentation : Algebra.Presentation R S (Fin 2
) (Fin 2) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StandardEtalePresentation.hasMap`：∀ {R : Type u_4} {S : Type u_5} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : StandardEta
lePresentation R S), s…

--- 原说明 ---
The `Algebra.Presentation` associated to a standard etale presentation.
-/
def StandardEtalePresentation.toPresentation : Algebra.Presentation R S (Fin 2) (Fin 2) where
  __ := Algebra.Generators.ofAlgHom ((P.lift _ P.hasMap).comp
      (P.equivMvPolynomialQuotient.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))
    (P.lift_bijective.surjective.comp
      (P.equivMvPolynomialQuotient.symm.surjective.comp Ideal.Quotient.mk_surjective))
  relation := ![Bivariate.equivMvPolynomial R (C P.f),
    Bivariate.equivMvPolynomial R (.X * C P.g - 1)]
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      AlgHom.comp_toRingHom,
      RingHom.ker_comp_of_injective _ (by exact P.lift_bijective.injective),
      RingHom.ker_comp_of_injective _ (by exact P.equivMvPolynomialQuotient.symm.injective)]
    simp [Set.pair_comm]

set_option backward.isDefEq.respectTransparency.types false in
/-
**StandardEtalePresentation.aeval_val_equivMvPolynomial** 是 Mathlib 中的一个定理，位于命名空
间 `StandardEtalePresentation`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   (P : StandardEtalePresentation R S) (p : Polynomial R),
   (MvPolynomial.aeval P.toPresentation.val) ((Polynomial.Bivariate.equivMvPolyn
omial R) (Polynomial.C p)) =     (Polynomial.aeval P.x) p
参数：P : StandardEtalePresentation R S；p : Polynomial R；MvPolynomial.aeval P.toPre
sentation.val；(Polynomial.Bivariate.equivMvPolynomial R) (Polynomial.C p)；Polyno
mial.aeval P.x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Polynomial.Bivariate.equivMvPolynomial_C_X`：equivMvPolynomial_C_X : equi
vMvPolynomial R (C X) = .X 0
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `StandardEtalePresentation.hasMap`：∀ {R : Type u_4} {S : Type u_5} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : StandardEta
lePresentation R S), s…
· 使用定理 `StandardEtalePresentation.toPresentation_val`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : St
andardEtalePresentation R S) (a : …
· 使用引理 `StandardEtalePair.equivMvPolynomialQuotient_symm_apply`：equivMvPolynomia
lQuotient_symm_apply : P.equivMvPolynomialQuotient.symm (Ideal.Quotient.mk _ (.X
 0)) = P.X
· 使用引理 `StandardEtalePair.lift_X`：lift_X (x : S) (h : P.HasMap x) : P.lift x h P
.X = x
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma StandardEtalePresentation.aeval_val_equivMvPolynomial (p : R[X]) :
    MvPolynomial.aeval P.toPresentation.val
    (Bivariate.equivMvPolynomial R (.C p)) = p.aeval P.x := by
  change (((MvPolynomial.aeval _).comp (Bivariate.equivMvPolynomial R).toAlgHom).comp CAlgHom) _ = _
  congr 1
  ext
  simp

attribute [local simp] Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det
  Matrix.det_fin_two Algebra.PreSubmersivePresentation.jacobiMatrix_apply
  Polynomial.Bivariate.pderiv_zero_equivMvPolynomial
  Polynomial.Bivariate.pderiv_one_equivMvPolynomial

set_option backward.isDefEq.respectTransparency.types false in
/-- The `Algebra.SubmersivePresentation` associated to a standard etale presentation. -/
@[simps map toPreSubmersivePresentation_toPresentation]
/-
**StandardEtalePresentation.toSubmersivePresentation** 是 Mathlib 中的一个定义，位于命名空间 `
`。
形式化陈述：StandardEtalePresentation.toSubmersivePresentation : Algebra.SubmersivePre
sentation R S (Fin 2) (Fin 2) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Algebra.SubmersivePresentation` associated to a standard etale presentation
.
-/
def StandardEtalePresentation.toSubmersivePresentation :
    Algebra.SubmersivePresentation R S (Fin 2) (Fin 2) where
  __ := P.toPresentation
  map := id
  map_inj := Function.injective_id
  jacobian_isUnit := by simp [P.hasMap.2, P.hasMap.isUnit_derivative_f]

set_option backward.isDefEq.respectTransparency.types false in
/-
**StandardEtalePresentation.toSubmersivePresentation_jacobian** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.toSubmersivePresentation_jacobian : P.toSubmersi
vePresentation.jacobian = aeval P.x P.f.derivative * aeval P.x P.g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
· 使用定理 `StandardEtalePresentation.toPresentation_relation`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : StandardEtalePresentation R S) (a : …
· 使用引理 `Polynomial.Bivariate.pderiv_zero_equivMvPolynomial`：pderiv_zero_equivMvP
olynomial {R : Type*} [CommRing R] (p : R[X][Y]) : (equivMvPolynomial R p).pderi
v 0 = equivMvPolynomial R (PolynomialMod…
· 使用引理 `Derivation.mapCoeffs_C`：mapCoeffs_C (x : A) : d.mapCoeffs (C x) = .singl
e A 0 (d x)
· 使用定理 `Polynomial.derivative'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] (
a : Polynomial R), Polynomial.derivative' a = Polynomial.derivative a
· 使用定理 `StandardEtalePresentation.hasMap`：∀ {R : Type u_4} {S : Type u_5} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : StandardEta
lePresentation R S), s…
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `MvPolynomial.pderiv_X`：pderiv_X [DecidableEq σ] (i j : σ) : pderiv i (X 
j : MvPolynomial σ R) = Pi.single (M
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Polynomial.Bivariate.pderiv_one_equivMvPolynomial`：pderiv_one_equivMvPol
ynomial (p : R[X][Y]) : (equivMvPolynomial R p).pderiv 1 = equivMvPolynomial R (
derivative p)
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
（共 44 条，此处仅展示前 30 条）
-/
lemma StandardEtalePresentation.toSubmersivePresentation_jacobian :
    P.toSubmersivePresentation.jacobian = aeval P.x P.f.derivative * aeval P.x P.g := by
  simp [StandardEtalePresentation.toSubmersivePresentation]

set_option backward.isDefEq.respectTransparency.types false in
/-
**StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x (x : S) : ex
ists p : R[X], exists n, x * P.g.aeval P.x ^ n = p.aeval P.x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `AdjoinRoot.mk_surjective`：mk_surjective : Function.Surjective (mk g)
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
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
· 使用引理 `StandardEtalePresentation.equivRing_x`：StandardEtalePresentation.equivRi
ng_x : P.equivRing P.x = P.X
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.Away.lift_eq`：lift_eq (hg : IsUnit (g x)) (a : R) : lift 
x hg (algebraMap R S a) = g a
· 使用定理 `AdjoinRoot.lift_mk`：lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i
 a
-/
lemma StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x (x : S) :
    ∃ p : R[X], ∃ n, x * P.g.aeval P.x ^ n = p.aeval P.x := by
  obtain ⟨x, rfl⟩ := (P.equivRing.trans P.P.equivAwayAdjoinRoot).symm.surjective x
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (.powers (AdjoinRoot.mk P.f P.g)) x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  refine ⟨p, n, P.equivRing.injective ?_⟩
  simpa [← aeval_algHom_apply, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def] using
    congr(P.equivAwayAdjoinRoot.symm $e)

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping `StandardEtalePresentation` under `AlgEquiv`s. -/
/-
**StandardEtalePresentation.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.mapEquiv (e : S ≃ₐ[R] T) : StandardEtalePresenta
tion R T where P
参数：e : S ≃ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping `StandardEtalePresentation` under `AlgEquiv`s.
-/
def StandardEtalePresentation.mapEquiv (e : S ≃ₐ[R] T) : StandardEtalePresentation R T where
  P := P.P
  x := e P.x
  hasMap := P.hasMap.map e.toAlgHom
  lift_bijective := (show P.lift (e P.x) (P.hasMap.map e.toAlgHom) = e.toAlgHom.comp
    (P.lift _ P.hasMap) from P.hom_ext (by simp)) ▸ e.bijective.comp P.lift_bijective
/-
**StandardEtalePresentation.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.hom_ext {f₁ f₂ : S ->ₐ[R] T} (h : f₁ P.x = f₂ P.
x) : f₁ = f₂
参数：h : f₁ P.x = f₂ P.x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StandardEtalePair.hom_ext`：hom_ext {f g : P.Ring ->ₐ[R] S} (H : f P.X = 
g P.X) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StandardEtalePresentation.equivRing_symm_X`：StandardEtalePresentation.eq
uivRing_symm_X : P.equivRing.symm P.X = P.x
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma StandardEtalePresentation.hom_ext {f₁ f₂ : S →ₐ[R] T} (h : f₁ P.x = f₂ P.x) : f₁ = f₂ := by
  have : f₁.comp P.equivRing.symm.toAlgHom = f₂.comp P.equivRing.symm.toAlgHom :=
    P.P.hom_ext (by simpa)
  ext x
  obtain ⟨x, rfl⟩ := P.equivRing.symm.surjective x
  exact congr($this x)

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false in
/-- The base change of a standard etale algebra is standard etale. -/
noncomputable
/-
**StandardEtalePresentation.baseChange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StandardEtalePresentation.baseChange : StandardEtalePresentation T (T otim
es[R] S) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def StandardEtalePresentation.baseChange :
    StandardEtalePresentation T (T ⊗[R] S) where
  __ := P.map (algebraMap R T)
  x := 1 ⊗ₜ P.x
  hasMap := (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap
  lift_bijective := by
    algebraize [(algebraMap T (P.map (algebraMap R T)).Ring).comp (algebraMap R T)]
    have H : P.HasMap (P.map (algebraMap R T)).X := by
      simpa [StandardEtalePair.HasMap] using (P.map (algebraMap R T)).hasMap_X
    let f : T ⊗[R] S →ₐ[T] (P.map (algebraMap R T)).Ring :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ((P.lift (P.map _).X H).comp P.equivRing)
        fun _ _ ↦ .all _ _
    let α : T ⊗[R] S ≃ₐ[T] (P.map (algebraMap R T)).Ring :=
      .ofAlgHom f ((P.map (algebraMap R T)).lift (1 ⊗ₜ[R] P.x)
        (P.hasMap.map (Algebra.TensorProduct.includeRight (R := R) (A := T))).map_algebraMap) (by
        ext; simp [f]) (by ext1; apply P.hom_ext; simp [f])
    exact α.symm.bijective

namespace Algebra

/-- The class of standard etale algebras,
defined to be the existence of a `StandardEtalePresentation`. -/
/-
**Algebra.IsStandardEtale** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_4) → (S : Type u_5) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of standard etale algebras,
defined to be the existence of a `StandardEtalePresentation`.
-/
class IsStandardEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  nonempty_standardEtalePresentation : Nonempty (StandardEtalePresentation R S)

attribute [instance] IsStandardEtale.nonempty_standardEtalePresentation
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : StandardEtalePair R) : IsStandardEtale R P.Ring :=
  ⟨⟨P, P.X, P.hasMap_X, by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsStandardEtale R S] : Algebra.Etale R S :=
  .of_equiv IsStandardEtale.nonempty_standardEtalePresentation.some.equivRing.symm
/-
**Algebra.IsStandardEtale.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsStandard
Etale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (e : S ≃ₐ[R] T) [Algebra.IsStandardEtale R S],   Algebra.IsStandardEtale R 
T
参数：e : S ≃ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardEtale.nonempty_standardEtalePresentation`：∀ {R : Type 
u_4} {S : Type u_5} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra 
R S}   [self : Algebra.IsStandardEtale R S], Non…
-/
lemma IsStandardEtale.of_equiv (e : S ≃ₐ[R] T) [IsStandardEtale R S] : IsStandardEtale R T :=
  ⟨⟨IsStandardEtale.nonempty_standardEtalePresentation.some.mapEquiv e⟩⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStandardEtale R R :=
  ⟨⟨⟨⟨.X, by simp, 1, 1, 0, 0, by simp⟩, 0, ⟨by simp, by simp⟩, by
    set P : StandardEtalePair R := ⟨.X, by simp, 1, 1, 0, 0, by simp⟩
    have : P.X = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    let e := AlgEquiv.ofAlgHom (P.lift (0 : R) ⟨by simp [P], by simp [P]⟩) (Algebra.ofId _ _)
      (by ext) (by ext; simp [this])
    exact e.bijective⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.IsStandardEtale.of_isLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.IsStandardEtale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.IsStandardEtale R S] {Sₛ : Type u_4} [inst_4 :
 CommRing Sₛ] [inst_5 : Algebra S Sₛ] [inst_6 : Algebra R Sₛ]   [IsScalarTower R
 S Sₛ] (s : S) [IsLocalization.Away s Sₛ], Algebra.IsStandardEtale R Sₛ
参数：s : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsStandardEtale.nonempty_standardEtalePresentation`：∀ {R : Type 
u_4} {S : Type u_5} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra 
R S}   [self : Algebra.IsStandardEtale R S], Non…
· 使用引理 `StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x`：StandardE
talePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x (x : S) : exists p : R[X], 
exists n, x * P.g.aeval P.x ^ n = p.aeval P.x
· 使用定理 `StandardEtalePair.monic_f`：∀ {R : Type u_1} [inst : CommRing R] (self : 
StandardEtalePair R), self.f.Monic
· 使用定理 `StandardEtalePair.cond`：∀ {R : Type u_1} [inst : CommRing R] (self : Sta
ndardEtalePair R),   ∃ p₁ p₂ n, Polynomial.derivative self.f * p₁ + self.f * p₂ 
= self.g ^ n
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_eq_const`：mul_eq_const [Mul α] (p :
 a = b) (c : α) : a * c = b * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 85 条，此处仅展示前 30 条）
-/
lemma IsStandardEtale.of_isLocalizationAway [IsStandardEtale R S]
    {Sₛ : Type*} [CommRing Sₛ] [Algebra S Sₛ]
    [Algebra R Sₛ] [IsScalarTower R S Sₛ] (s : S) [IsLocalization.Away s Sₛ] :
    IsStandardEtale R Sₛ := by
  have P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let P' : StandardEtalePair R := ⟨P.f, P.monic_f, p * P.g, have ⟨p₁, p₂, m, e⟩ := P.cond;
    ⟨p₁ * p ^ m, p₂ * p ^ m, m, by linear_combination e * p ^ m⟩⟩
  let S' := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] S' := P.equivRing.trans P.P.equivAwayAdjoinRoot
  have := IsLocalization.Away.mul S' (Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)))
    (AdjoinRoot.mk P.f P.g) (.mk _ p)
  rw [← map_mul] at this
  have H : Submonoid.map e.symm.toRingEquiv.toMonoidHom (.powers
      (algebraMap _ S' (AdjoinRoot.mk P.f p))) = .powers (aeval P.x p) := by
    have : ((e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R _ S')).comp (AdjoinRoot.mkₐ P.f)) =
      aeval P.x := by ext; simp [e, StandardEtalePair.equivAwayAdjoinRoot]
    rw [Submonoid.map_powers]
    exact congr(Submonoid.powers ($this p))
  have : IsLocalization.Away (aeval P.x p) Sₛ :=
    IsLocalization.Away.of_associated (r := s) ⟨(P.hasMap.2.pow n).unit, hp⟩
  let e₁ : P'.Ring ≃ₐ[R]
      Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) :=
    P'.equivAwayAdjoinRoot.trans ((IsLocalization.algEquiv (.powers (AdjoinRoot.mk P.f (p * P.g)))
      (Localization.Away (AdjoinRoot.mk P.f (p * P.g))) _).restrictScalars R)
  let e₂ : Localization.Away (algebraMap _ S' (AdjoinRoot.mk P.f p)) ≃ₐ[R] Sₛ :=
    { __ := IsLocalization.ringEquivOfRingEquiv _ _ _ H,
      commutes' r := by
        simp [IsScalarTower.algebraMap_apply R S' (Localization.Away _),
          - AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_eq R S Sₛ] }
  exact .of_equiv (e₁.trans e₂)

/-- If `T` is an etale algebra, and a standard etale algebra surjects onto `T`, then
  `T` is also standard etale. -/
/-
**Algebra.IsStandardEtale.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsSta
ndardEtale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [Algebra.IsStandardEtale R S] [Algebra.Etale R T] (f : S →ₐ[R] T),   Functi
on.Surjective ⇑f → Algebra.IsStandardEtale R T
参数：f : S →ₐ[R] T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.isIdempotentElem_iff_of_fg`：isIdempotentElem_iff_of_fg {R : Type*}
 [CommRing R] (I : Ideal R) (h : I.FG) : IsIdempotentElem I ↔ exists e : R, IsId
empotentElem e ∧ I = R…
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.instEtaleOfIsStandardEtale`：∀ {R : Type u_1} {S : Type u_2} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.IsStanda
rdEtale R S], Algebra.Et…
· 使用引理 `Algebra.FormallyEtale.iff_of_surjective`：iff_of_surjective {R S : Type*}
 [CommRing R] [CommRing S] [Algebra R S] (h : Function.Surjective (algebraMap R 
S)) : Algebra.FormallyEtale R…
· 使用引理 `Algebra.FormallyEtale.of_restrictScalars`：of_restrictScalars [FormallyUn
ramified R A] [FormallyEtale R B] : FormallyEtale A B
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用引理 `IsLocalization.away_of_isIdempotentElem`：away_of_isIdempotentElem {R S} 
[CommRing R] [CommRing S] [Algebra R S] {e : R} (he : IsIdempotentElem e) (H : R
ingHom.ker (algebraMap R S) =…
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.IsStandardEtale.of_isLocalizationAway`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algeb
ra.IsStandardEtale R S] {Sₛ : Type …

--- 原说明 ---
If `T` is an etale algebra, and a standard etale algebra surjects onto `T`, then
  `T` is also standard etale.
-/
lemma IsStandardEtale.of_surjective
    [IsStandardEtale R S] [Algebra.Etale R T] (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    IsStandardEtale R T := by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨e, he, hfe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (Algebra.FinitePresentation.ker_fG_of_surjective f hf)).mp
      ((Algebra.FormallyEtale.iff_of_surjective hf).mp (.of_restrictScalars (R := R)))
  have := IsLocalization.away_of_isIdempotentElem he.one_sub (hfe.trans (by simp)) hf
  exact .of_isLocalizationAway (1 - e)
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsStandardEtale R S] :
    Algebra.IsStandardEtale T (T ⊗[R] S) :=
  ⟨⟨Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some.baseChange⟩⟩

end Algebra

