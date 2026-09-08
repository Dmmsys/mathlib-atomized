/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Algebras over Artinian rings

In this file we collect results about algebras over Artinian rings.
-/

public section

namespace IsArtinianRing

variable {R A : Type*}
variable [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]

open nonZeroDivisors

/-- In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit. -/
/-
**IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor** 是 Mathlib 中的一个定理，位于命名空
间 `IsArtinianRing`。
形式化陈述：isUnit_of_isIntegral_of_nonZeroDivisor {a : A} (hi : IsIntegral R a) (ha :
 a in A⁰) : IsUnit a
参数：hi : IsIntegral R a；ha : a in A⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `comap_nonZeroDivisors_le_of_injective`：comap_nonZeroDivisors_le_of_injec
tive [MonoidWithZeroHomClass F M₀ M₀'] {f : F} (hf : Injective f) : M₀'⁰.comap f
 <= M₀⁰
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsArtinianRing.isUnit_of_mem_nonZeroDivisors`：isUnit_of_mem_nonZeroDivis
ors [IsArtinianRing R] {a : R} (ha : a in R⁰) : IsUnit a
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.finite_adjoin_simple_of_isIntegral`：Algebra.finite_adjoin_simple
_of_isIntegral {x : B} (hi : IsIntegral R x) : Module.Finite R (adjoin R {x})

--- 原说明 ---
In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit.
-/
theorem isUnit_of_isIntegral_of_nonZeroDivisor {a : A}
    (hi : IsIntegral R a) (ha : a ∈ A⁰) : IsUnit a :=
  let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective B.subtype := Subtype.val_injective
  have hb : b ∈ B⁰ := comap_nonZeroDivisors_le_of_injective hinj ha
  (isUnit_of_mem_nonZeroDivisors hb).map B.subtype

/-- Integral element of an algebra over Artinian ring `R` is either a zero divisor or a unit. -/
/-
**IsArtinianRing.isUnit_iff_nonZeroDivisor_of_isIntegral** 是 Mathlib 中的一个定理，位于命名
空间 `IsArtinianRing`。
形式化陈述：isUnit_iff_nonZeroDivisor_of_isIntegral {a : A} (hi : IsIntegral R a) : Is
Unit a ↔ a in A⁰
参数：hi : IsIntegral R a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
· 使用定理 `IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor`：isUnit_of_isInteg
ral_of_nonZeroDivisor {a : A} (hi : IsIntegral R a) (ha : a in A⁰) : IsUnit a

--- 原说明 ---
Integral element of an algebra over Artinian ring `R` is either a zero divisor o
r a unit.
-/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral {a : A}
    (hi : IsIntegral R a) : IsUnit a ↔ a ∈ A⁰ :=
  ⟨IsUnit.mem_nonZeroDivisors, isUnit_of_isIntegral_of_nonZeroDivisor hi⟩

/-- In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit. -/
/-
**IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral'** 是 Mathlib 中的一个定理，位于命名
空间 `IsArtinianRing`。
形式化陈述：isUnit_of_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} (
ha : a in A⁰) : IsUnit a
参数：ha : a in A⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor`：isUnit_of_isInteg
ral_of_nonZeroDivisor {a : A} (hi : IsIntegral R a) (ha : a in A⁰) : IsUnit a
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
In an `R`-algebra over an Artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit.
-/
theorem isUnit_of_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A}
    (ha : a ∈ A⁰) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor (R := R) (Algebra.IsIntegral.isIntegral a) ha

/-- Integral element of an algebra over Artinian ring `R` is either a zero divisor or a unit. -/
/-
**IsArtinianRing.isUnit_iff_nonZeroDivisor_of_isIntegral'** 是 Mathlib 中的一个定理，位于命
名空间 `IsArtinianRing`。
形式化陈述：isUnit_iff_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} 
: IsUnit a ↔ a in A⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArtinianRing.isUnit_iff_nonZeroDivisor_of_isIntegral`：isUnit_iff_nonZe
roDivisor_of_isIntegral {a : A} (hi : IsIntegral R a) : IsUnit a ↔ a in A⁰
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
Integral element of an algebra over Artinian ring `R` is either a zero divisor o
r a unit.
-/
theorem isUnit_iff_nonZeroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} :
    IsUnit a ↔ a ∈ A⁰ :=
  isUnit_iff_nonZeroDivisor_of_isIntegral (R := R) (Algebra.IsIntegral.isIntegral a)
/-
**IsArtinianRing.isUnit_submonoid_eq_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Is
ArtinianRing`。
形式化陈述：isUnit_submonoid_eq_of_isIntegral [Algebra.IsIntegral R A] : IsUnit.submon
oid A = A⁰
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsArtinianRing.isUnit_iff_nonZeroDivisor_of_isIntegral'`：isUnit_iff_nonZ
eroDivisor_of_isIntegral' [Algebra.IsIntegral R A] {a : A} : IsUnit a ↔ a in A⁰
-/
theorem isUnit_submonoid_eq_of_isIntegral [Algebra.IsIntegral R A] : IsUnit.submonoid A = A⁰ := by
  ext; simpa [IsUnit.mem_submonoid_iff] using isUnit_iff_nonZeroDivisor_of_isIntegral' (R := R)

end IsArtinianRing

