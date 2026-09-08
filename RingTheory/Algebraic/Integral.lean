/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Algebraic elements and integral elements

This file relates algebraic and integral elements of an algebra, by proving every integral element
is algebraic and that every algebraic element over a field is integral.

## Main results

* `IsIntegral.isAlgebraic`, `Algebra.IsIntegral.isAlgebraic`: integral implies algebraic.
* `isAlgebraic_iff_isIntegral`, `Algebra.isAlgebraic_iff_isIntegral`: integral iff algebraic
  over a field.
* `IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.of_finite`: finite-dimensional (as module) implies
  algebraic.
* `IsAlgebraic.exists_integral_multiple`: an algebraic element has a multiple which is integral
* `IsAlgebraic.iff_exists_smul_integral`: If `R` is reduced and `S` is an `R`-algebra with
  injective `algebraMap`, then an element of `S` is algebraic over `R` iff some `R`-multiple
  is integral over `R`.
* `Algebra.IsAlgebraic.trans`: If `A/S/R` is a tower of algebras and both `A/S` and `S/R` are
  algebraic, then `A/R` is also algebraic, provided that `S` has no zero divisors.
* `Subalgebra.algebraicClosure`: If `R` is a domain and `S` is an arbitrary `R`-algebra,
  then the elements of `S` that are algebraic over `R` form a subalgebra.
* `Transcendental.extendScalars`: an element of an `R`-algebra that is transcendental over `R`
  remains transcendental over any algebraic `R`-subalgebra that has no zero divisors.
-/

@[expose] public section

assert_not_exists IsLocalRing

universe u v w

open Polynomial

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic. -/
/-
**IsIntegral.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x -> IsAlgebr
aic R x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0

--- 原说明 ---
An integral element of an algebra is algebraic.
-/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩
/-
**Algebra.IsIntegral.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] : A
lgebra.IsAlgebraic R A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a ↦ (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral. -/
/-
**isAlgebraic_iff_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
An element of an algebra over a field is algebraic if and only if it is integral
.
-/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def, map_mul, hpx, zero_mul]
/-
**Algebra.isAlgebraic_iff_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {K : Type u} {A : Type v} [inst : Field K] [inst_1 : Ring A] [inst_2 : A
lgebra K A],   Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isAlgebraic_def`：Algebra.isAlgebraic_def : Algebra.IsAlgebraic R
 A ↔ forall x : A, IsAlgebraic R x
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def, Algebra.isIntegral_def,
      forall_congr' fun _ ↦ isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/-- This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that would make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit. -/
/-
**Algebra.IsAlgebraic.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlgebraic`
。
形式化陈述：∀ {K : Type u} {A : Type v} [inst : Field K] [inst_1 : Ring A] [inst_2 : A
lgebra K A] [Algebra.IsAlgebraic K A],   Algebra.IsIntegral K A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.isAlgebraic_iff_isIntegral`：∀ {K : Type u} {A : Type v} [inst : 
Field K] [inst_1 : Ring A] [inst_2 : Algebra K A],   Algebra.IsAlgebraic K A ↔ A
lgebra.IsIntegral K A

--- 原说明 ---
This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that woul
d make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit.
-/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›
/-
**Algebra.IsAlgebraic.of_isIntegralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.of_isIntegralClosure (R B C : Type*) [CommRing R] [Non
trivial R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C] [
IsScalarTower R B C] [IsIntegralClosure B R C] : Algebra.IsAlgebraic R B
参数：R B C : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
-/
theorem Algebra.IsAlgebraic.of_isIntegralClosure (R B C : Type*) [CommRing R] [Nontrivial R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [IsIntegralClosure B R C] : Algebra.IsAlgebraic R B :=
  have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

end Field

section

variable (K L R : Type*) {A : Type*}

section Ring

variable [CommRing R] [Nontrivial R] [Ring A] [Algebra R A]

/-
**IsAlgebraic.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_finite (e : A) [Module.Finite R A] : IsAlgebraic R e
参数：e : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
-/
theorem IsAlgebraic.of_finite (e : A) [Module.Finite R A] : IsAlgebraic R e :=
  (IsIntegral.of_finite R e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
/-
**Algebra.IsAlgebraic.of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.of_finite [Module.Finite R A] : Algebra.IsAlgebraic R 
A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field extension is algebraic if it is finite.
-/
instance Algebra.IsAlgebraic.of_finite [Module.Finite R A] : Algebra.IsAlgebraic R A :=
  (IsIntegral.of_finite R A).isAlgebraic

end Ring

section Field

variable {K L} [Field K] [Ring A] [Algebra K A]

/-- If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over `K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`. -/
@[simp]
/-
**transcendental_aeval_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_aeval_iff {r : A} {f : K[X]} : Transcendental K (Polynomial
.aeval r f) ↔ Transcendental K r ∧ Transcendental K f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `Transcendental.of_aeval`：Transcendental.of_aeval {r : A} {f : R[X]} (H :
 Transcendental R (Polynomial.aeval r f)) : Transcendental R f
· 使用定理 `Transcendental.aeval_of_transcendental`：Transcendental.aeval_of_transcen
dental {r : A} (H : Transcendental R r) {f : R[X]} (hf : Transcendental R f) : T
ranscendental R (Polynomial.…

--- 原说明 ---
If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over 
`K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`.
-/
theorem transcendental_aeval_iff {r : A} {f : K[X]} :
    Transcendental K (Polynomial.aeval r f) ↔ Transcendental K r ∧ Transcendental K f := by
  refine ⟨fun h ↦ ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ ↦ h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

variable [Field L] [Algebra K L]

variable (K L) in
/-- Bijection between algebra equivalences and algebra homomorphisms -/
/-
**algEquivEquivAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：algEquivEquivAlgHom [FiniteDimensional K L] : (L ≃ₐ[K] L) ≃* (L ->ₐ[K] L)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between algebra equivalences and algebra homomorphisms
-/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {z : A} {z' : S}

namespace IsAlgebraic

/-
**IsAlgebraic.exists_integral_multiple** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：exists_integral_multiple (hz : IsAlgebraic R z) : exists y != (0 : R), IsI
ntegral R (y • z)
参数：hz : IsAlgebraic R z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.monic_integralNormalization`：monic_integralNormalization (hp 
: p != 0) : Monic (integralNormalization p)
· 使用定理 `Polynomial.integralNormalization_aeval_eq_zero`：integralNormalization_ae
val_eq_zero [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0) (inj : forall 
x : S, algebraMap S A x = 0 -> x = 0…
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `isIntegral_zero`：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
-/
theorem exists_integral_multiple (hz : IsAlgebraic R z) : ∃ y ≠ (0 : R), IsIntegral R (y • z) := by
  by_cases inj : Function.Injective (algebraMap R A); swap
  · rw [injective_iff_map_eq_zero] at inj; push Not at inj
    have ⟨r, eq, ne⟩ := inj
    exact ⟨r, ne, by simpa [← algebraMap_smul A, eq, zero_smul] using isIntegral_zero⟩
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (algebraMap R A a * z) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px fun _ ↦ (map_eq_zero_iff _ inj).mp⟩
  exact ⟨_, a_ne_zero, Algebra.smul_def a z ▸ x_integral⟩

variable (R) in
/-
**IsAlgebraic._root_.Algebra.IsAlgebraic.exists_integral_multiples** 是 Mathlib 中
的一个定理，位于命名空间 `IsAlgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.IsAlgebraic.exists_integral_multiples [NoZeroDivisors R]
    [alg : Algebra.IsAlgebraic R A] (s : Finset A) :
    ∃ y ≠ (0 : R), ∀ z ∈ s, IsIntegral R (y • z) := by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x ↦ (alg.1 x).exists_integral_multiple
  refine ⟨∏ x ∈ s, r x, Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hr _, fun _ h ↦ ?_⟩
  classical rw [← Finset.prod_erase_mul _ _ h, mul_smul]
  exact (int _).smul _
/-
**IsAlgebraic.of_smul_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：of_smul_isIntegral {y : R} (hy : ¬ IsNilpotent y) (h : IsIntegral R (y • z
)) : IsAlgebraic R z
参数：hy : ¬ IsNilpotent y；h : IsIntegral R (y • z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNilpotent.zero`：∀ {R : Type u_3} [inst : MonoidWithZero R], IsNilpoten
t 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_C_mul_X`：leadingCoeff_C_mul_X (a : R) : leadingC
oeff (C a * X) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
· 使用定理 `Polynomial.natDegree_C_mul_X`：natDegree_C_mul_X (a : R) (ha : a != 0) : 
natDegree (C a * X) = 1
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem of_smul_isIntegral {y : R} (hy : ¬ IsNilpotent y)
    (h : IsIntegral R (y • z)) : IsAlgebraic R z := by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h ↦ ?_, by simpa [aeval_comp, Algebra.smul_def] using! eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y ≠ 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero, ← mul_one p.natDegree, ← natDegree_C_mul_X y hy0,
    coeff_comp_degree_mul_degree, monic, one_mul, leadingCoeff_C_mul_X] at h
  · exact hy ⟨_, h⟩
  · rw [natDegree_C_mul_X _ hy0]; rintro ⟨⟩
/-
**IsAlgebraic.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：of_smul {y : R} (hy : y in nonZeroDivisors R) (h : IsAlgebraic R (y • z)) 
: IsAlgebraic R z
参数：hy : y in nonZeroDivisors R；h : IsAlgebraic R (y • z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.comp_C_mul_X_eq_zero_iff`：comp_C_mul_X_eq_zero_iff {r : R} (h
r : r in nonZeroDivisors R) : p.comp (C r * X) = 0 ↔ p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem of_smul {y : R} (hy : y ∈ nonZeroDivisors R)
    (h : IsAlgebraic R (y • z)) : IsAlgebraic R z :=
  have ⟨p, hp, eval0⟩ := h
  ⟨_, mt (comp_C_mul_X_eq_zero_iff hy).mp hp, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩
/-
**IsAlgebraic.iff_exists_smul_integral** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：iff_exists_smul_integral [IsReduced R] : IsAlgebraic R z ↔ exists y != (0 
: R), IsIntegral R (y • z)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `IsAlgebraic.of_smul_isIntegral`：of_smul_isIntegral {y : R} (hy : ¬ IsNil
potent y) (h : IsIntegral R (y • z)) : IsAlgebraic R z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
-/
theorem iff_exists_smul_integral [IsReduced R] :
    IsAlgebraic R z ↔ ∃ y ≠ (0 : R), IsIntegral R (y • z) :=
  ⟨(exists_integral_multiple ·), fun ⟨_, hy, int⟩ ↦
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

section integralClosure

variable {K : Type*} [CommRing K] [Algebra S K] [Algebra R K] [IsIntegralClosure S R K]

variable (S)

omit [Algebra R S] in
/-- If `x : K` is algebraic over some ring `R`, then a nonzero `R`-multiple of it is contained
in the integral closure of `R` in `K`. -/
/-
**IsAlgebraic.exists_smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsAlgebraic`。
形式化陈述：exists_smul_eq {x : K} (hx : IsAlgebraic R x) : exists (r : R) (s : S), r 
!= 0 ∧ r • x = algebraMap S K s
参数：hx : IsAlgebraic R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `x : K` is algebraic over some ring `R`, then a nonzero `R`-multiple of it is
 contained
in the integral closure of `R` in `K`.
-/
lemma exists_smul_eq {x : K} (hx : IsAlgebraic R x) :
    ∃ (r : R) (s : S), r ≠ 0 ∧ r • x = algebraMap S K s := by
  obtain ⟨r, hr, h⟩ := hx.exists_integral_multiple
  obtain ⟨s, hs⟩ := IsIntegralClosure.isIntegral_iff (A := S) |>.mp h
  exact ⟨r, s, hr, hs.symm⟩

/-- If `x : K` is algebraic over `ℤ`, then a nonzero `ℕ`-multiple of it is contained in the
integral closure of `ℤ` in `K`. -/
/-
**IsAlgebraic.exists_nsmul_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsAlgebraic`。
形式化陈述：exists_nsmul_eq [IsIntegralClosure S Int K] {x : K} (hx : IsAlgebraic Int 
x) : exists (m : Nat) (s : S), m != 0 ∧ m • x = algebraMap S K s
参数：hx : IsAlgebraic Int x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAlgebraic.exists_smul_eq`：exists_smul_eq {x : K} (hx : IsAlgebraic R x
) : exists (r : R) (s : S), r != 0 ∧ r • x = algebraMap S K s
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `x : K` is algebraic over `ℤ`, then a nonzero `ℕ`-multiple of it is contained
 in the
integral closure of `ℤ` in `K`.
-/
lemma exists_nsmul_eq [IsIntegralClosure S ℤ K] {x : K} (hx : IsAlgebraic ℤ x) :
    ∃ (m : ℕ) (s : S), m ≠ 0 ∧ m • x = algebraMap S K s := by
  obtain ⟨a, s, ha, h⟩ := hx.exists_smul_eq S
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · exact ⟨n, s, mod_cast ha, mod_cast h⟩
  · exact ⟨n, -s, by simpa using ha, by simp [← h]⟩

end integralClosure

section restrictScalars

variable (R) [NoZeroDivisors S]

/-!
The next theorem may fail if only `R` is assumed to be a domain but `S` is not: for example, let
`S = R[X] ⧸ (X² - X)` and let `A` be the subalgebra of `S[Y]` generated by `XY`.
`A` is algebraic over `S` because any element `∑ᵢ sᵢ(XY)ⁱ` is a root of the polynomial
`(X - 1)(Z - s₀)` in `S[Z]`, because `X(X - 1) = X² - X = 0` in `S`.
However, `XY` is a transcendental element in `A` over `R`, because `∑ᵢ rᵢ(XY)ⁱ = 0` in `S[Y]`
implies all `rᵢXⁱ = 0` (i.e., `r₀ = 0` and `rᵢX = 0` for `i > 0`) in `S`,
which implies `rᵢ = 0` in `R`. This example is inspired by the comment
https://mathoverflow.net/questions/482944/when-do-algebraic-elements-form-a-subalgebra#comment1257632_482944. -/

/-
**IsAlgebraic.restrictScalars_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebra
ic`。
形式化陈述：restrictScalars_of_isIntegral [int : Algebra.IsIntegral R S] {a : A} (h : 
IsAlgebraic S a) : IsAlgebraic R a
参数：h : IsAlgebraic S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `is_transcendental_of_subsingleton`：is_transcendental_of_subsingleton [Su
bsingleton R] (x : A) : Transcendental R x
· 使用定理 `IsAlgebraic.exists_nonzero_dvd`：IsAlgebraic.exists_nonzero_dvd {s : S} (
hRs : IsAlgebraic R s) (hs : s in S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R 
S r
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsAlgebraic.of_smul_isIntegral`：of_smul_isIntegral {y : R} (hy : ¬ IsNil
potent y) (h : IsIntegral R (y • z)) : IsAlgebraic R z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Algebra.isAlgebraic_of_not_injective`：Algebra.isAlgebraic_of_not_injecti
ve (h : ¬ Function.Injective (algebraMap R A)) : Algebra.IsAlgebraic R A where i
sAlgebraic a
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)

--- 原说明 ---
The next theorem may fail if only `R` is assumed to be a domain but `S` is not: 
for example, let
`S = R[X] ⧸ (X² - X)` and let `A` be the subalgebra of `S[Y]` generated by `XY`.
`A` is algebraic over `S` because any element `∑ᵢ sᵢ(XY)ⁱ` is a root of the poly
nomial
`(X - 1)(Z - s₀)` in `S[Z]`, because `X(X - 1) = X² - X = 0` in `S`.
However, `XY` is a transcendental element in `A` over `R`, because `∑ᵢ rᵢ(XY)ⁱ =
 0` in `S[Y]`
implies all `rᵢXⁱ = 0` (i.e., `r₀ = 0` and `rᵢX = 0` for `i > 0`) in `S`,
which implies `rᵢ = 0` in `R`. This example is inspired by the comment
https://mathoverflow.net/questions/482944/when-do-algebraic-elements-form-a-suba
lgebra#comment1257632_482944.
-/
theorem restrictScalars_of_isIntegral [int : Algebra.IsIntegral R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
    fun h ↦ hRS <| .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R S
    exact (is_transcendental_of_subsingleton _ _ h).elim
  have ⟨r, hr, _, e⟩ := (int.1 s).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hs)
  refine .of_smul_isIntegral (y := r) (by rwa [isNilpotent_iff_eq_zero]) ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S,
    e, ← Algebra.smul_def, mul_comm, mul_smul]
  exact isIntegral_trans _ (int_s.smul _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsAlgebraic.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：restrictScalars [Algebra.IsAlgebraic R S] {a : A} (h : IsAlgebraic S a) : 
IsAlgebraic R a
参数：h : IsAlgebraic S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.of_faithfulSMul`：NoZeroDivisors.of_faithfulSMul [NoZeroDi
visors A] : NoZeroDivisors R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用引理 `Algebra.nontrivial_of_isAlgebraic`：Algebra.nontrivial_of_isAlgebraic [Al
gebra.IsAlgebraic R A] : Nontrivial R
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `Algebra.IsAlgebraic.exists_integral_multiples`：∀ (R : Type u_1) {A : Typ
e u_3} [inst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [NoZeroDivis
ors R]   [alg : Algebra.IsAlgebraic…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_coeffs_iff`：mem_coeffs_iff {p : R[X]} {c : R} : c in p.co
effs ↔ exists n in p.support, c = p.coeff n
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Polynomial.support_smul`：support_smul [SMulZeroClass S R] (r : S) (p : R
[X]) : support (r • p) subseteq support p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用定理 `Polynomial.instIsTorsionFree`：∀ {R : Type u} [inst : Semiring R] {S : Ty
pe u_1} [inst_1 : Semiring S] [inst_2 : _root_.Module S R]   [Module.IsTorsionFr
ee S R], Module.Is…
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Subalgebra.algebraMap_eq`：algebraMap_eq {R A : Type*} [CommSemiring R] [
CommSemiring A] [Semiring α] [Algebra R A] [Algebra A α] (S : Subalgebra R A) : 
algebraMap S α…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subalgebra.toSubring_subtype`：toSubring_subtype {R A : Type*} [CommRing 
R] [Ring A] [Algebra R A] (S : Subalgebra R A) : S.toSubring.subtype = (S.val : 
S ->+* A)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.restrictScalars_apply`：restrictScalars_apply (f : A ->ₐ[S] B) (x 
: A) : f.restrictScalars R x = f x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 38 条，此处仅展示前 30 条）
-/
theorem restrictScalars [Algebra.IsAlgebraic R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  have ⟨p, hp, eval0⟩ := h
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
    fun h ↦ hRS <| .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  rw [← faithfulSMul_iff_algebraMap_injective] at hRS
  have := NoZeroDivisors.of_faithfulSMul R S
  have := Algebra.nontrivial_of_isAlgebraic R S
  have : IsDomain R := NoZeroDivisors.to_isDomain _
  classical
  have ⟨r, hr, int⟩ := Algebra.IsAlgebraic.exists_integral_multiples R (p.support.image (coeff p))
  let p := (r • p).toSubring (integralClosure R S).toSubring fun s hs ↦ by
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hs
    exact int _ (Finset.mem_image_of_mem _ <| support_smul _ _ hn)
  have : IsAlgebraic (integralClosure R S) a := by
    refine ⟨p, ?_, ?_⟩
    · simpa only [← Polynomial.map_ne_zero_iff (f := Subring.subtype _) (p := p)
        Subtype.val_injective, p, map_toSubring, smul_ne_zero_iff] using And.intro hr hp
    rw [← eval_map_algebraMap, Subalgebra.algebraMap_eq, ← map_map, ← Subalgebra.toSubring_subtype,
      map_toSubring, eval_map_algebraMap, ← AlgHom.restrictScalars_apply R,
      map_smul, AlgHom.restrictScalars_apply, eval0, smul_zero]
  exact restrictScalars_of_isIntegral _ this
/-
**IsAlgebraic._root_.IsIntegral.trans_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `IsA
lgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsIntegral.trans_isAlgebraic [alg : Algebra.IsAlgebraic R S]
    {a : A} (h : IsIntegral S a) : IsAlgebraic R a := by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _

end restrictScalars

section Ring

variable (s : S) {a : A} (ha : IsAlgebraic R a)
include ha

/-
**IsAlgebraic.neg** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {a : A},   IsAlgebraic R a → IsAlgebraic R (-a)
参数：-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EmbeddingLike.map_ne_zero_iff`：∀ {F : Type u_1} {M : Type u_4} {N : Type
 u_5} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [EmbeddingLik
e F M N] [ZeroHomCl…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.algEquivAevalNegX_apply`：∀ {R : Type u_3} [inst : CommRing R]
 (a : Polynomial R),   Polynomial.algEquivAevalNegX a = (Polynomial.aeval (-Poly
nomial.X)) a
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.aeval_neg`：aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A
) : aeval x (-p) = -aeval x p
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected lemma neg : IsAlgebraic R (-a) :=
  have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩
/-
**IsAlgebraic.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (r : R), IsAlgebraic R (r • a)
参数：r : R；r • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.scaleRoots_ne_zero`：scaleRoots_ne_zero {p : R[X]} (hp : p != 
0) (s : R) : scaleRoots p s != 0
· 使用定理 `Polynomial.scaleRoots_aeval_eq_zero`：scaleRoots_aeval_eq_zero [Algebra R
 A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) : aeval (algebraMap R A r * 
a) (scaleRoots p r) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
protected lemma smul (r : R) : IsAlgebraic R (r • a) :=
  have ⟨_, hp, eval0⟩ := ha
  ⟨_, scaleRoots_ne_zero hp r, Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩
/-
**IsAlgebraic.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (n : ℕ), IsAlgebraic R (n • a)
参数：n : ℕ；n • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.smul`：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [i
nst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (r : R), I
sAlgeb…
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
-/
protected lemma nsmul (n : ℕ) : IsAlgebraic R (n • a) :=
  Nat.cast_smul_eq_nsmul R n a ▸ ha.smul _
/-
**IsAlgebraic.zsmul** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (n : ℤ), IsAlgebraic R (n • a)
参数：n : ℤ；n • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.smul`：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [i
nst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (r : R), I
sAlgeb…
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
-/
protected lemma zsmul (n : ℤ) : IsAlgebraic R (n • a) :=
  Int.cast_smul_eq_zsmul R n a ▸ ha.smul _

omit [Algebra S A] [IsScalarTower R S A] in
/-
**IsAlgebraic.tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsAlgebraic`。
形式化陈述：tmul [FaithfulSMul R S] : IsAlgebraic S (s otimesₜ[R] a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `IsAlgebraic.smul`：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [i
nst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsAlgebraic R a → ∀ (r : R), I
sAlgeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Algebra.TensorProduct.includeRight_apply`：includeRight_apply (b : B) : (
includeRight : B ->ₐ[R] A otimes[R] B) b = 1 otimesₜ b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma tmul [FaithfulSMul R S] : IsAlgebraic S (s ⊗ₜ[R] a) := by
  rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul']
  have ⟨p, h, eval0⟩ := ha
  refine .smul ⟨p.map (algebraMap R S),
    (Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective ..).mpr h, ?_⟩ _
  rw [← Algebra.TensorProduct.includeRight_apply, ← AlgHom.coe_toRingHom (A := A),
    ← map_aeval_eq_aeval_map (by ext; simp), eval0, map_zero]

end Ring

section CommRing

variable [NoZeroDivisors R] {a b : S} (ha : IsAlgebraic R a) (hb : IsAlgebraic R b)
include ha hb

/-
**IsAlgebraic.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlgebraic R a → IsAlgeb
raic R b → IsAlgebraic R (a * b)
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAlgebraic.iff_exists_smul_integral`：iff_exists_smul_integral [IsReduce
d R] : IsAlgebraic R z ↔ exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
-/
protected lemma mul : IsAlgebraic R (a * b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b
/-
**IsAlgebraic.add** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlgebraic R a → IsAlgeb
raic R b → IsAlgebraic R (a + b)
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_integral_multiple`：exists_integral_multiple (hz : IsA
lgebraic R z) : exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAlgebraic.iff_exists_smul_integral`：iff_exists_smul_integral [IsReduce
d R] : IsAlgebraic R z ↔ exists y != (0 : R), IsIntegral R (y • z)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
-/
protected lemma add : IsAlgebraic R (a + b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add, mul_smul, mul_comm, mul_smul]
  exact (int_a.smul _).add (int_b.smul _)
/-
**IsAlgebraic.sub** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlgebraic R a → IsAlgeb
raic R b → IsAlgebraic R (a - b)
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.add`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlge
braic…
· 使用定理 `IsAlgebraic.neg`：∀ {R : Type u_1} {A : Type u_3} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsAlgebraic R a → IsAlgebraic R
 (-a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
protected lemma sub : IsAlgebraic R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
/-
**IsAlgebraic.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [NoZeroDivisors R]   {a : S}, IsAlgebraic R a → ∀ (n : ℕ)
, IsAlgebraic R (a ^ n)
参数：n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.nontrivial`：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic 
R a) : Nontrivial R
· 使用定理 `isAlgebraic_one`：isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IsAlgebraic.mul`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlge
braic…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
protected lemma pow (n : ℕ) : IsAlgebraic R (a ^ n) :=
  have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h ↦ pow_succ a _ ▸ h.mul ha

end CommRing

end IsAlgebraic

namespace Algebra

variable (R S A) [NoZeroDivisors S]

/-- Transitivity of algebraicity for algebras over domains. -/
/-
**Algebra.IsAlgebraic.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlgebraic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsAl
gebraic R S] [alg : Algebra.IsAlgebraic S A], Algebra.IsAlgebraic R A
参数：R : Type u_1；S : Type u_2；A : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.restrictScalars`：restrictScalars [Algebra.IsAlgebraic R S] {
a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…

--- 原说明 ---
Transitivity of algebraicity for algebras over domains.
-/
@[stacks 09GJ] theorem IsAlgebraic.trans [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars _⟩
/-
**Algebra.IsIntegral.trans_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsInte
gral`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsIn
tegral R S] [alg : Algebra.IsAlgebraic S A], Algebra.IsAlgebraic R A
参数：R : Type u_1；S : Type u_2；A : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.restrictScalars_of_isIntegral`：restrictScalars_of_isIntegral
 [int : Algebra.IsIntegral R S] {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem IsIntegral.trans_isAlgebraic [Algebra.IsIntegral R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars_of_isIntegral _⟩
/-
**Algebra.IsAlgebraic.trans_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlge
braic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsAl
gebraic R S] [int : Algebra.IsIntegral S A], Algebra.IsAlgebraic R A
参数：R : Type u_1；S : Type u_2；A : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.trans_isAlgebraic`：IsIntegral.trans_isAlgebraic [Algebra.IsIn
tegral R S] [alg : Algebra.IsAlgebraic S A] : Algebra.IsAlgebraic R A
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem IsAlgebraic.trans_isIntegral [Algebra.IsAlgebraic R S] [int : Algebra.IsIntegral S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (int.1 _).trans_isAlgebraic _⟩

variable {A}
/-
**Algebra.IsIntegral.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsIntegr
al`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsIn
tegral R S] [FaithfulSMul R S] {a : A}, IsAlgebraic R a ↔ IsAlgebraic S a
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsAlgebraic.restrictScalars_of_isIntegral`：restrictScalars_of_isIntegral
 [int : Algebra.IsIntegral R S] {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
-/
protected theorem IsIntegral.isAlgebraic_iff [Algebra.IsIntegral R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars_of_isIntegral _⟩
/-
**Algebra.IsIntegral.isAlgebraic_iff_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsIn
tegral`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsIn
tegral R S] [FaithfulSMul R S], Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S 
A
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Algebra.IsIntegral.isAlgebraic_iff`：∀ (R : Type u_1) (S : Type u_2) {A :
 Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3
 : Algebra R S] [inst_4 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsIntegral.isAlgebraic_iff_top [Algebra.IsIntegral R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsIntegral.isAlgebraic_iff R S]
/-
**Algebra.IsAlgebraic.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlgeb
raic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsAl
gebraic R S] [FaithfulSMul R S] {a : A}, IsAlgebraic R a ↔ IsAlgebraic S a
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsAlgebraic.restrictScalars`：restrictScalars [Algebra.IsAlgebraic R S] {
a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
-/
protected theorem IsAlgebraic.isAlgebraic_iff [Algebra.IsAlgebraic R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars _⟩
/-
**Algebra.IsAlgebraic.isAlgebraic_iff_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsA
lgebraic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsAl
gebraic R S] [FaithfulSMul R S], Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S
 A
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic_iff`：∀ (R : Type u_1) (S : Type u_2) {A 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_
3 : Algebra R S] [inst_4 …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsAlgebraic.isAlgebraic_iff_top [Algebra.IsAlgebraic R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsAlgebraic.isAlgebraic_iff R S]
/-
**Algebra.IsAlgebraic.isAlgebraic_iff_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsA
lgebraic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [Algebra.IsAl
gebraic S A] [FaithfulSMul S A], Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R
 S
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.tower_bot_of_injective`：Algebra.IsAlgebraic.tower_bo
t_of_injective [Algebra.IsAlgebraic R A] (hinj : Function.Injective (algebraMap 
S A)) : Algebra.IsAlgebraic R S …
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
-/
theorem IsAlgebraic.isAlgebraic_iff_bot [Algebra.IsAlgebraic S A] [FaithfulSMul S A] :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R S :=
  ⟨fun _ ↦ .tower_bot_of_injective (FaithfulSMul.algebraMap_injective S A), fun _ ↦ .trans R S A⟩

end Algebra

variable (R S)
/-- If `R` is a domain and `S` is an arbitrary `R`-algebra, then the elements of `S`
that are algebraic over `R` form a subalgebra. -/
/-
**Subalgebra.algebraicClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a domain and `S` is an arbitrary `R`-algebra, then the elements of `S`
that are algebraic over `R` form a subalgebra.
-/
def Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where
  carrier := {s | IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap
/-
**Subalgebra.mem_algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.mem_algebraicClosure [IsDomain R] {x : S} : x in algebraicClosu
re R S ↔ IsAlgebraic R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Subalgebra.mem_algebraicClosure [IsDomain R] {x : S} :
    x ∈ algebraicClosure R S ↔ IsAlgebraic R x := Iff.rfl
/-
**integralClosure_le_algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure_le_algebraicClosure [IsDomain R] : integralClosure R S <= 
Subalgebra.algebraicClosure R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem integralClosure_le_algebraicClosure [IsDomain R] :
    integralClosure R S ≤ Subalgebra.algebraicClosure R S :=
  fun _ ↦ IsIntegral.isAlgebraic
/-
**Subalgebra.algebraicClosure_eq_integralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.algebraicClosure_eq_integralClosure {K} [Field K] [Algebra K S]
 : algebraicClosure K S = integralClosure K S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
-/
theorem Subalgebra.algebraicClosure_eq_integralClosure {K} [Field K] [Algebra K S] :
    algebraicClosure K S = integralClosure K S :=
  SetLike.ext fun _ ↦ isAlgebraic_iff_isIntegral
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] : Algebra.IsAlgebraic R (Subalgebra.algebraicClosure R S) :=
  (Subalgebra.isAlgebraic_iff _).mp fun _ ↦ id

variable {R S}
/-
**Algebra.isAlgebraic_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_adjoin_iff [IsDomain R] {s : Set S} : (adjoin R s).IsA
lgebraic ↔ forall x in s, IsAlgebraic R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
-/
theorem Algebra.isAlgebraic_adjoin_iff [IsDomain R] {s : Set S} :
    (adjoin R s).IsAlgebraic ↔ ∀ x ∈ s, IsAlgebraic R x :=
  Algebra.adjoin_le_iff (S := Subalgebra.algebraicClosure R S)
/-
**Algebra.isAlgebraic_adjoin_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_adjoin_of_nonempty [NoZeroDivisors R] {s : Set S} (hs 
: s.Nonempty) : (adjoin R s).IsAlgebraic ↔ forall x in s, IsAlgebraic R x
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `IsAlgebraic.nontrivial`：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic 
R a) : Nontrivial R
· 使用定理 `Algebra.isAlgebraic_adjoin_iff`：Algebra.isAlgebraic_adjoin_iff [IsDomain
 R] {s : Set S} : (adjoin R s).IsAlgebraic ↔ forall x in s, IsAlgebraic R x
-/
theorem Algebra.isAlgebraic_adjoin_of_nonempty [NoZeroDivisors R] {s : Set S} (hs : s.Nonempty) :
    (adjoin R s).IsAlgebraic ↔ ∀ x ∈ s, IsAlgebraic R x :=
  ⟨fun h x hx ↦ h _ (subset_adjoin hx), fun h ↦
    have ⟨x, hx⟩ := hs
    have := (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨‹_›, (h x hx).nontrivial⟩
    isAlgebraic_adjoin_iff.mpr h⟩

/-- In an algebra generated by a single algebraic element over a domain `R`, every element is
algebraic. This may fail when `R` is not a domain: see https://mathoverflow.net/a/132192/ for
an example. -/
/-
**Algebra.isAlgebraic_adjoin_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_adjoin_singleton_iff [NoZeroDivisors R] {s : S} : (adj
oin R {s}).IsAlgebraic ↔ IsAlgebraic R s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.isAlgebraic_adjoin_of_nonempty`：Algebra.isAlgebraic_adjoin_of_no
nempty [NoZeroDivisors R] {s : Set S} (hs : s.Nonempty) : (adjoin R s).IsAlgebra
ic ↔ forall x in s, IsAlgebr…
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `forall_eq`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a = a' 
→ p a) ↔ p a'

--- 原说明 ---
In an algebra generated by a single algebraic element over a domain `R`, every e
lement is
algebraic. This may fail when `R` is not a domain: see https://mathoverflow.net/
a/132192/ for
an example.
-/
theorem Algebra.isAlgebraic_adjoin_singleton_iff [NoZeroDivisors R] {s : S} :
    (adjoin R {s}).IsAlgebraic ↔ IsAlgebraic R s :=
  (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq
/-
**IsAlgebraic.of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy : y in nonZeroDivisors
 S) (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z
参数：hy : y in nonZeroDivisors S；alg_y : IsAlgebraic R y；alg_yz : IsAlgebraic R (y
 * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_eq_adjoin_mul`：IsAlgebraic.exists_nonzero_eq_
adjoin_mul {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) : existsᵉ (t in R[s]) 
(r != (0 : R)), s * t = algebr…
· 使用定理 `IsAlgebraic.mul`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlge
braic…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.isAlgebraic_adjoin_singleton_iff`：Algebra.isAlgebraic_adjoin_sin
gleton_iff [NoZeroDivisors R] {s : S} : (adjoin R {s}).IsAlgebraic ↔ IsAlgebraic
 R s
· 使用定理 `IsAlgebraic.of_smul`：of_smul {y : R} (hy : y in nonZeroDivisors R) (h : 
IsAlgebraic R (y • z)) : IsAlgebraic R z
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
-/
theorem IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy : y ∈ nonZeroDivisors S)
    (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z := by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm, eq, ← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

open Algebra in
omit [Algebra R A] [IsScalarTower R S A] in
/-
**IsAlgebraic.adjoin_of_forall_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.adjoin_of_forall_isAlgebraic [NoZeroDivisors S] {s t : Set S} 
(alg : forall x in s \ t, IsAlgebraic (adjoin R t) x) {a : A} (ha : IsAlgebraic 
(adjoin R s) a) : IsAlgebraic (adjoin R t) a
参数：alg : forall x in s \ t, IsAlgebraic (adjoin R t) x；ha : IsAlgebraic (adjoin 
R s) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsAlgebraic.nontrivial`：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic 
R a) : Nontrivial R
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDomain_iff_noZeroDivisors_and_nontrivial`：isDomain_iff_noZeroDivisors_
and_nontrivial [Ring α] : IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.isAlgebraic_iff`：Subalgebra.isAlgebraic_iff (S : Subalgebra R
 A) : S.IsAlgebraic ↔ Algebra.IsAlgebraic R S
· 使用定理 `Algebra.isAlgebraic_adjoin_iff`：Algebra.isAlgebraic_adjoin_iff [IsDomain
 R] {s : Set S} : (adjoin R s).IsAlgebraic ↔ forall x in s, IsAlgebraic R x
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
· 使用定理 `IsAlgebraic.restrictScalars`：restrictScalars [Algebra.IsAlgebraic R S] {
a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
-/
theorem IsAlgebraic.adjoin_of_forall_isAlgebraic [NoZeroDivisors S] {s t : Set S}
    (alg : ∀ x ∈ s \ t, IsAlgebraic (adjoin R t) x) {a : A}
    (ha : IsAlgebraic (adjoin R s) a) : IsAlgebraic (adjoin R t) a := by
  set Rs := adjoin R s
  set Rt := adjoin R t
  let Rts := adjoin Rt s
  let _ : Algebra Rs Rts := (Subalgebra.inclusion
    (T := Rts.restrictScalars R) <| adjoin_le <| by apply subset_adjoin).toAlgebra
  have : IsScalarTower Rs Rts A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ rfl
  have : Algebra.IsAlgebraic Rt Rts := by
    have := ha.nontrivial
    have := Subtype.val_injective (p := (· ∈ Rs)).nontrivial
    have := (isDomain_iff_noZeroDivisors_and_nontrivial Rt).mpr ⟨inferInstance, inferInstance⟩
    rw [← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
    intro x hs
    by_cases ht : x ∈ t
    · exact isAlgebraic_algebraMap (⟨x, subset_adjoin ht⟩ : Rt)
    exact alg _ ⟨hs, ht⟩
  have : IsAlgebraic Rts a := ha.extendScalars (by apply Subalgebra.inclusion_injective)
  exact this.restrictScalars Rt

namespace Transcendental

section

variable (S) [NoZeroDivisors S] {a : A} (ha : Transcendental R a)
include ha

/-
**Transcendental.extendScalars_of_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 `Transcen
dental`。
形式化陈述：extendScalars_of_isIntegral [Algebra.IsIntegral R S] : Transcendental S a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `IsAlgebraic.restrictScalars_of_isIntegral`：restrictScalars_of_isIntegral
 [int : Algebra.IsIntegral R S] {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
-/
lemma extendScalars_of_isIntegral [Algebra.IsIntegral R S] :
    Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _
/-
**Transcendental.extendScalars** 是 Mathlib 中的一个引理，位于命名空间 `Transcendental`。
形式化陈述：extendScalars [Algebra.IsAlgebraic R S] : Transcendental S a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `IsAlgebraic.restrictScalars`：restrictScalars [Algebra.IsAlgebraic R S] {
a : A} (h : IsAlgebraic S a) : IsAlgebraic R a
-/
lemma extendScalars [Algebra.IsAlgebraic R S] : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars _

end

variable [NoZeroDivisors S] {a : S} (ha : Transcendental R a)
include ha

/-
**Transcendental.integralClosure** 是 Mathlib 中的一个定理，位于命名空间 `Transcendental`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [NoZeroDivisors S]   {a : S}, Transcendental R a → Transc
endental (↥(integralClosure R S)) a
参数：↥(integralClosure R S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Transcendental.extendScalars_of_isIntegral`：extendScalars_of_isIntegral 
[Algebra.IsIntegral R S] : Transcendental S a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
protected lemma integralClosure : Transcendental (integralClosure R S) a :=
  ha.extendScalars_of_isIntegral _
/-
**Transcendental.subalgebraAlgebraicClosure** 是 Mathlib 中的一个引理，位于命名空间 `Transcend
ental`。
形式化陈述：subalgebraAlgebraicClosure [IsDomain R] : Transcendental (Subalgebra.algeb
raicClosure R S) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Transcendental.extendScalars`：extendScalars [Algebra.IsAlgebraic R S] : 
Transcendental S a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsAlgebraicSubtypeMemSubalgebraAlgebraicClosure`：∀ (R : Type u_1) (S
 : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [i
nst_3 : IsDomain R],   Algebra.IsAlgebrai…
-/
lemma subalgebraAlgebraicClosure [IsDomain R] :
    Transcendental (Subalgebra.algebraicClosure R S) a := ha.extendScalars _

end Transcendental

namespace Algebra

variable (R S) [NoZeroDivisors S] [FaithfulSMul R S] {a : A}

/-
**Algebra.IsIntegral.transcendental_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsInt
egral`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [FaithfulSMul
 R S] {a : A} [Algebra.IsIntegral R S], Transcendental R a ↔ Transcendental S a
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Transcendental.extendScalars_of_isIntegral`：extendScalars_of_isIntegral 
[Algebra.IsIntegral R S] : Transcendental S a
· 使用定理 `Transcendental.restrictScalars`：Transcendental.restrictScalars (hinj : F
unction.Injective (algebraMap R S)) {x : A} (h : Transcendental S x) : Transcend
ental R x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
protected theorem IsIntegral.transcendental_iff [Algebra.IsIntegral R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars_of_isIntegral _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
/-
**Algebra.IsAlgebraic.transcendental_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAl
gebraic`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) {A : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R S] [inst_4 : Algebra R A]
 [inst_5 : Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S]   [FaithfulSMul
 R S] {a : A} [Algebra.IsAlgebraic R S], Transcendental R a ↔ Transcendental S a
参数：R : Type u_1；S : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Transcendental.extendScalars`：extendScalars [Algebra.IsAlgebraic R S] : 
Transcendental S a
· 使用定理 `Transcendental.restrictScalars`：Transcendental.restrictScalars (hinj : F
unction.Injective (algebraMap R S)) {x : A} (h : Transcendental S x) : Transcend
ental R x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
protected theorem IsAlgebraic.transcendental_iff [Algebra.IsAlgebraic R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

end Algebra

open scoped nonZeroDivisors

namespace Algebra.IsAlgebraic

section IsFractionRing

variable (R S) (R' S' : Type*) [CommRing S'] [FaithfulSMul R S] [alg : Algebra.IsAlgebraic R S]
  [NoZeroDivisors S] [Algebra S S'] [IsFractionRing S S']

/-
**Algebra.IsAlgebraic.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsAlgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalization (algebraMapSubmonoid S R⁰) S' :=
  have := (FaithfulSMul.algebraMap_injective R S).noZeroDivisors _ (map_zero _) (map_mul _)
  (IsLocalization.iff_of_le_of_exists_dvd _ S⁰
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ..) le_rfl)
    fun s hs ↦ have ⟨r, ne, eq⟩ := (alg.1 s).exists_nonzero_dvd hs
    ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

variable [Algebra R S'] [IsScalarTower R S S']
/-
**Algebra.IsAlgebraic.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsAlgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalizedModule R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

variable [CommRing R'] [Algebra R R'] [IsFractionRing R R']
/-
**Algebra.IsAlgebraic.isBaseChange_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.IsAlgebraic`。
形式化陈述：isBaseChange_of_isFractionRing [Module R' S'] [IsScalarTower R R' S'] : Is
BaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizedModuleNonZeroDivisorsToLinearMapToAlg
Hom`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [
inst_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
-/
theorem isBaseChange_of_isFractionRing [Module R' S'] [IsScalarTower R R' S'] :
    IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap :=
  (isLocalizedModule_iff_isBaseChange R⁰ ..).mp inferInstance

variable [Algebra R' S'] [IsScalarTower R R' S']
/-
**Algebra.IsAlgebraic.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsAlgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPushout R R' S S' := (isPushout_iff ..).mpr <| isBaseChange_of_isFractionRing ..
/-
**Algebra.IsAlgebraic.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsAlgebraic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPushout R S R' S' := .symm inferInstance

end IsFractionRing

variable (R) (R' : Type*) (S : Type u) [CommRing R'] [CommRing S] [Algebra R S]
  [Algebra R R'] [IsFractionRing R R'] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]

section

variable [NoZeroDivisors S] (S' : Type v) [CommRing S'] [Algebra R S'] [Algebra S S'] [Module R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S']

/-
**Algebra.IsAlgebraic.lift_rank_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.IsAlgebraic`。
形式化陈述：lift_rank_of_isFractionRing : Cardinal.lift.{u} (Module.rank R' S') = Card
inal.lift.{v} (Module.rank R S)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.rank_eq`：IsLocalization.rank_eq : Module.rank S N = Modul
e.rank R N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `IsLocalizedModule.lift_rank_eq`：IsLocalizedModule.lift_rank_eq : Cardina
l.lift.{uM} (Module.rank R N) = Cardinal.lift.{uN} (Module.rank R M)
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizedModuleNonZeroDivisorsToLinearMapToAlg
Hom`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [
inst_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
-/
theorem lift_rank_of_isFractionRing :
    Cardinal.lift.{u} (Module.rank R' S') = Cardinal.lift.{v} (Module.rank R S) := by
  rw [IsLocalization.rank_eq R' R⁰ le_rfl,
    IsLocalizedModule.lift_rank_eq R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap le_rfl]

@[deprecated (since := "2026-07-13")] alias finrank_of_isFractionRing := IsFractionRing.finrank_eq
/-
**Algebra.IsAlgebraic.rank_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsAlgebraic`。
形式化陈述：rank_of_isFractionRing (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra
 S S'] [Module R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFraction
Ring S S'] : Module.rank R' S' = Module.rank R S
参数：S' : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebra.IsAlgebraic.lift_rank_of_isFractionRing`：lift_rank_of_isFraction
Ring : Cardinal.lift.{u} (Module.rank R' S') = Cardinal.lift.{v} (Module.rank R 
S)
-/
theorem rank_of_isFractionRing (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [Module R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S'] :
    Module.rank R' S' = Module.rank R S := by
  simpa using lift_rank_of_isFractionRing R R' S S'

end

attribute [local instance] FractionRing.liftAlgebra in
/-
**Algebra.IsAlgebraic.rank_fractionRing** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlg
ebraic`。
形式化陈述：rank_fractionRing [IsDomain S] : Module.rank (FractionRing R) (FractionRin
g S) = Module.rank R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.rank_of_isFractionRing`：rank_of_isFractionRing (S' :
 Type u) [CommRing S'] [Algebra R S'] [Algebra S S'] [Module R' S'] [IsScalarTow
er R R' S'] [IsScalarTower R S S…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
theorem rank_fractionRing [IsDomain S] :
    Module.rank (FractionRing R) (FractionRing S) = Module.rank R S :=
  rank_of_isFractionRing ..

end Algebra.IsAlgebraic

attribute [local instance] FractionRing.liftAlgebra in
/-- Tower law for `Module.finrank` in a tower of domains `R → S → T`. This is a variant of
`Module.finrank_mul_finrank` that assumes the rings are domains instead of the modules being
free. -/
/-
**Module.finrank_mul_finrank'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_mul_finrank' (T : Type*) [CommRing T] [IsDomain T] [Algebra
 S T] [Algebra R T] [IsScalarTower R S T] [FaithfulSMul S T] : Module.finrank R 
S * Module.finrank S T = Module.finrank R T
参数：T : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.trans`：FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOn
eClass T] [SMul R S] [IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T]
 [SMul R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.finrank_eq`：∀ (A : Type u_1) (K : Type u_2) (B : Type u_3
) (L : Type u_4) [inst : CommRing A] [inst_1 : CommRing K]   [inst_2 : CommRing 
B] [inst_3 : Co…
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `FractionRing.instIsScalarTower_1`：∀ (A : Type u_4) [inst : CommRing A] [
IsDomain A] (k : Type u_6) (K : Type u_7) [inst_2 : Field k] [inst_3 : Field K] 
  [inst_4 : Algebra A …
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.finrank_eq_zero_of_not_faithfulSMul`：Module.finrank_eq_zero_of_no
t_faithfulSMul (h : ¬ FaithfulSMul R M) : finrank R M = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `FaithfulSMul.tower_bot`：FaithfulSMul.tower_bot (R S T : Type*) [Monoid S
] [MulOneClass T] [SMul R S] [SMul R T] [MulAction S T] [IsScalarTower R S S] [I
sScalarTower…

--- 原说明 ---
Tower law for `Module.finrank` in a tower of domains `R → S → T`. This is a vari
ant of
`Module.finrank_mul_finrank` that assumes the rings are domains instead of the m
odules being
free.
-/
theorem Module.finrank_mul_finrank' (T : Type*) [CommRing T] [IsDomain T]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] [FaithfulSMul S T] :
    Module.finrank R S * Module.finrank S T = Module.finrank R T := by
  by_cases h : FaithfulSMul R S
  · have : FaithfulSMul R T := .trans R S T
    have : IsDomain R := (FaithfulSMul.algebraMap_injective R T).isDomain
    have : IsDomain S := (FaithfulSMul.algebraMap_injective S T).isDomain
    rw [← IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S),
      ← IsFractionRing.finrank_eq S (FractionRing S) T (FractionRing T),
      ← IsFractionRing.finrank_eq R (FractionRing R) T (FractionRing T),
      Module.finrank_mul_finrank (FractionRing R) (FractionRing S) (FractionRing T)]
  · rw [Module.finrank_eq_zero_of_not_faithfulSMul h, zero_mul,
      Module.finrank_eq_zero_of_not_faithfulSMul]
    exact fun _ ↦ h (FaithfulSMul.tower_bot R S T)

section Polynomial

attribute [local instance] Polynomial.algebra MvPolynomial.algebraMvPolynomial

section

variable (R S) [NoZeroDivisors R]

-- TODO: `PolynomialModule` version
/-
**rank_polynomial_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_polynomial_polynomial : Module.rank R[X] S[X] = Module.rank R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.rank_eq`：rank_eq {P : Type uM} [AddCommGroup P] [Module R P
] [Module T P] [IsScalarTower R T P] {g : M ->ₗ[R] P} (bc : IsBaseChange T g) : 
Module.ran…
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.isPushout_iff`：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiri
ng R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (R' : Type u_6)   (S' : T
ype u_7) [i…
· 使用定理 `instIsPushoutPolynomial_1`：∀ (R : Type u_1) [inst : CommSemiring R] {S :
 Type u_4} [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   Algebra.IsPushout
 R (Polynomial …
-/
theorem rank_polynomial_polynomial : Module.rank R[X] S[X] = Module.rank R S :=
  ((Algebra.isPushout_iff ..).mp inferInstance).rank_eq
/-
**rank_mvPolynomial_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_mvPolynomial_mvPolynomial (σ : Type u) : Module.rank (MvPolynomial σ 
R) (MvPolynomial σ S) = Cardinal.lift.{u} (Module.rank R S)
参数：σ : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.lift_rank_eq`：lift_rank_eq : Cardinal.lift.{uM} (Module.ran
k T P) = Cardinal.lift.{uP} (Module.rank R M)
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `AddMonoidAlgebra.faithfulSMul`：∀ {R : Type u_1} {S : Type u_2} {M : Type
 u_3} [inst : Semiring S] [inst_1 : SMulZeroClass R S] [FaithfulSMul R S]   [Non
empty M], FaithfulS…
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MvPolynomial.instIsScalarTower`：∀ {R : Type u_2} {S : Type u_3} {σ : Typ
e u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],
   IsScalarTower R (…
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.isPushout_iff`：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiri
ng R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (R' : Type u_6)   (S' : T
ype u_7) [i…
· 使用定理 `MvPolynomial.instIsPushout_1`：∀ {R : Type u} [inst : CommSemiring R] {σ 
: Type u_1} {S : Type u_3} [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   A
lgebra.IsPushout R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem rank_mvPolynomial_mvPolynomial (σ : Type u) :
    Module.rank (MvPolynomial σ R) (MvPolynomial σ S) = Cardinal.lift.{u} (Module.rank R S) := by
  have := Algebra.isPushout_iff R (MvPolynomial σ R) S (MvPolynomial σ S)
    |>.mp inferInstance |>.lift_rank_eq
  rwa [Cardinal.lift_id', Cardinal.lift_umax] at this

end

variable [alg : Algebra.IsAlgebraic R S]

section Pushout

variable (R S) (R' : Type*) [CommRing R'] [Algebra R R'] [NoZeroDivisors R'] [FaithfulSMul R R']

open TensorProduct in
/-
**Algebra.IsAlgebraic.tensorProduct** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.tensorProduct : Algebra.IsAlgebraic R' (R' otimes[R] S
) where isAlgebraic p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsAlgebraic.nontrivial`：Algebra.IsAlgebraic.nontrivial [alg : Al
gebra.IsAlgebraic R A] : Nontrivial R
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `isAlgebraic_zero`：isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A
)
· 使用引理 `IsAlgebraic.tmul`：tmul [FaithfulSMul R S] : IsAlgebraic S (s otimesₜ[R] 
a)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `IsAlgebraic.add`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlge
braic…
-/
instance Algebra.IsAlgebraic.tensorProduct : Algebra.IsAlgebraic R' (R' ⊗[R] S) where
  isAlgebraic p :=
    have := IsAlgebraic.nontrivial R S
    have := (FaithfulSMul.algebraMap_injective R R').nontrivial
    p.induction_on isAlgebraic_zero (fun _ s ↦ .tmul _ <| alg.1 s) (fun _ _ ↦ .add)

variable (S' : Type*) [CommRing S'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S']
/-
**Algebra.IsPushout.isAlgebraic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.isAlgebraic' [IsPushout R R' S S'] : Algebra.IsAlgebraic
 R' S'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Algebra.IsPushout.isAlgebraic' [IsPushout R R' S S'] : Algebra.IsAlgebraic R' S' :=
  (equiv R R' S S').isAlgebraic
/-
**Algebra.IsPushout.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.isAlgebraic [h : IsPushout R S R' S'] : Algebra.IsAlgebr
aic R' S'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Algebra.IsPushout.isAlgebraic [h : IsPushout R S R' S'] : Algebra.IsAlgebraic R' S' :=
  have := h.symm; (equiv R R' S S').isAlgebraic

end Pushout

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors R] : Algebra.IsAlgebraic R[X] S[X] := Algebra.IsPushout.isAlgebraic R S ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors S] : Algebra.IsAlgebraic R[X] S[X] := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← Polynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h
/-
**Polynomial.exists_dvd_map_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.exists_dvd_map_of_isAlgebraic [NoZeroDivisors S] {f : S[X]} (hf
 : f != 0) : exists g : R[X], g != 0 ∧ f ∣ g.map (algebraMap R S)
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_dvd`：IsAlgebraic.exists_nonzero_dvd {s : S} (
hRs : IsAlgebraic R s) (hs : s in S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R 
S r
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `instIsAlgebraicPolynomialOfNoZeroDivisors_1`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [alg : A
lgebra.IsAlgebraic R S] [NoZeroDi…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
-/
theorem Polynomial.exists_dvd_map_of_isAlgebraic [NoZeroDivisors S] {f : S[X]} (hf : f ≠ 0) :
    ∃ g : R[X], g ≠ 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ} [NoZeroDivisors R] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isAlgebraic R S ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ} [NoZeroDivisors S] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← MvPolynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h
/-
**MvPolynomial.exists_dvd_map_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.exists_dvd_map_of_isAlgebraic {σ} [NoZeroDivisors S] {f : MvP
olynomial σ S} (hf : f != 0) : exists g : MvPolynomial σ R, g != 0 ∧ f ∣ g.map (
algebraMap R S)
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_dvd`：IsAlgebraic.exists_nonzero_dvd {s : S} (
hRs : IsAlgebraic R s) (hs : s in S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R 
S r
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `instIsAlgebraicMvPolynomialOfNoZeroDivisors_1`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [alg :
 Algebra.IsAlgebraic R S] {σ : Type…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
-/
theorem MvPolynomial.exists_dvd_map_of_isAlgebraic {σ}
    [NoZeroDivisors S] {f : MvPolynomial σ S} (hf : f ≠ 0) :
    ∃ g : MvPolynomial σ R, g ≠ 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

variable [IsDomain S] [FaithfulSMul R S]

attribute [local instance] FractionRing.liftAlgebra
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R (FractionRing R[X]) S (FractionRing S[X]) :=
  (Algebra.IsPushout.comp_iff _ R[X] _ S[X]).mpr inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R S (FractionRing R[X]) (FractionRing S[X]) := .symm inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type*} :
    Algebra.IsPushout R (FractionRing (MvPolynomial σ R)) S (FractionRing (MvPolynomial σ S)) :=
  (Algebra.IsPushout.comp_iff _ (MvPolynomial σ R) _ (MvPolynomial σ S)).mpr inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type*} :
    Algebra.IsPushout R S (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) :=
  .symm inferInstance

namespace Algebra.IsAlgebraic

/-
**Algebra.IsAlgebraic.rank_fractionRing_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebra.IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [alg : Algebra.IsAlgebraic R S] [inst_3 : IsDomain S] [
inst_4 : FaithfulSMul R S],   Module.rank (FractionRing (Polynomial R)) (Fractio
nRing (Polynomial S)) = Module.rank R S
参数：FractionRing (Polynomial R)；FractionRing (Polynomial S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `instFaithfulSMulPolynomial`：∀ (R : Type u_1) (A : Type u_3) [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A],   F
aithfulSMul (Pol…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsAlgebraic.rank_fractionRing`：rank_fractionRing [IsDomain S] : 
Module.rank (FractionRing R) (FractionRing S) = Module.rank R S
· 使用定理 `instIsAlgebraicPolynomialOfNoZeroDivisors_1`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [alg : A
lgebra.IsAlgebraic R S] [NoZeroDi…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `rank_polynomial_polynomial`：rank_polynomial_polynomial : Module.rank R[X
] S[X] = Module.rank R S
-/
@[stacks 0G1M] theorem rank_fractionRing_polynomial :
    Module.rank (FractionRing R[X]) (FractionRing S[X]) = Module.rank R S := by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing, rank_polynomial_polynomial]

open Cardinal in
/-
**Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.IsAlgebraic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [alg : Algebra.IsAlgebraic R S] [inst_3 : IsDomain S] [
inst_4 : FaithfulSMul R S] (σ : Type u),   Module.rank (FractionRing (MvPolynomi
al σ R)) (FractionRing (MvPolynomial σ S)) =     Cardinal.lift.{u, u_2} (Module.
rank R S)
参数：σ : Type u；FractionRing (MvPolynomial σ R)；FractionRing (MvPolynomial σ S)；Mo
dule.rank R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `MvPolynomial.instFaithfulSMul`：∀ {R : Type u_2} {S : Type u_3} {σ : Type
 u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]  
 [FaithfulSMul R S]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsAlgebraic.rank_fractionRing`：rank_fractionRing [IsDomain S] : 
Module.rank (FractionRing R) (FractionRing S) = Module.rank R S
· 使用定理 `instIsAlgebraicMvPolynomialOfNoZeroDivisors_1`：∀ {R : Type u_1} {S : Typ
e u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [alg :
 Algebra.IsAlgebraic R S] {σ : Type…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `rank_mvPolynomial_mvPolynomial`：rank_mvPolynomial_mvPolynomial (σ : Type
 u) : Module.rank (MvPolynomial σ R) (MvPolynomial σ S) = Cardinal.lift.{u} (Mod
ule.rank R S)
-/
@[stacks 0G1M] theorem rank_fractionRing_mvPolynomial (σ : Type u) :
    Module.rank (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) =
    lift.{u} (Module.rank R S) := by
  have := IsDomain.of_faithfulSMul R S
  rw [rank_fractionRing, rank_mvPolynomial_mvPolynomial]

end Algebra.IsAlgebraic

end Polynomial

section FractionRing

open Algebra Module
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] [IsDomain S] [IsTorsionFree R S] [Module.Finite R S] :
    FiniteDimensional (FractionRing R) (FractionRing S) := by
  obtain ⟨_, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  exact Module.finite_def.mpr <|
    (span_eq_top_localization_localization (FractionRing R) R⁰ (FractionRing S) hs) ▸
      Submodule.fg_span (Set.toFinite _)

end FractionRing

