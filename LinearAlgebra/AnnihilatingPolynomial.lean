/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`,
every element `a : A` defines
an ideal `Polynomial.annIdeal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ Polynomial.annIdeal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `FieldTheory.Minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[AddCommGroup M] [Module R M]`)
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/

@[expose] public section


open Polynomial

namespace Polynomial

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R) in
/-- `annIdeal R a` is the *annihilating ideal* of all `p : R[X]` such that `p(a) = 0`.

The informal notation `p(a)` stands for `Polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map. -/
/-
**Polynomial.annIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：annIdeal (a : A) : Ideal R[X]
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`annIdeal R a` is the *annihilating ideal* of all `p : R[X]` such that `p(a) = 0
`.

The informal notation `p(a)` stands for `Polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map.
-/
noncomputable def annIdeal (a : A) : Ideal R[X] :=
  RingHom.ker ((aeval a).toRingHom : R[X] →+* A)

/-- It is useful to refer to ideal membership sometimes
and the annihilation condition other times. -/
/-
**Polynomial.mem_annIdeal_iff_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：mem_annIdeal_iff_aeval_eq_zero {a : A} {p : R[X]} : p in annIdeal R a ↔ ae
val a p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
It is useful to refer to ideal membership sometimes
and the annihilation condition other times.
-/
theorem mem_annIdeal_iff_aeval_eq_zero {a : A} {p : R[X]} : p ∈ annIdeal R a ↔ aeval a p = 0 :=
  Iff.rfl

end Semiring

section Field

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
variable (𝕜)

open Submodule

/-- `annIdealGenerator 𝕜 a` is the monic generator of `annIdeal 𝕜 a`
if one exists, otherwise `0`.

Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
`span 𝕜 {g} = annIdeal a`. This picks some generator.
We prefer the monic generator of the ideal. -/
/-
**Polynomial.annIdealGenerator** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：annIdealGenerator (a : A) : 𝕜[X]
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`annIdealGenerator 𝕜 a` is the monic generator of `annIdeal 𝕜 a`
if one exists, otherwise `0`.

Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
`span 𝕜 {g} = annIdeal a`. This picks some generator.
We prefer the monic generator of the ideal.
-/
noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
  let g := IsPrincipal.generator <| annIdeal 𝕜 a
  g * C g.leadingCoeff⁻¹

section

variable {𝕜}

@[simp]
/-
**Polynomial.annIdealGenerator_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：annIdealGenerator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIde
al 𝕜 a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem annIdealGenerator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥ := by
  simp only [annIdealGenerator, mul_eq_zero, IsPrincipal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leadingCoeff_eq_zero, or_self_iff]

end

/-- `annIdealGenerator 𝕜 a` is indeed a generator. -/
@[simp]
/-
**Polynomial.span_singleton_annIdealGenerator** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：span_singleton_annIdealGenerator (a : A) : Ideal.span {annIdealGenerator 𝕜
 a} = annIdeal 𝕜 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.annIdealGenerator_eq_zero_iff`：annIdealGenerator_eq_zero_iff 
{a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥
· 使用定理 `Set.singleton_zero`：∀ {α : Type u_2} [inst : Zero α], {0} = 0
· 使用定理 `Ideal.span_zero`：span_zero : span (0 : Set α) = ⊥
· 使用定理 `Polynomial.annIdealGenerator.eq_1`：∀ (𝕜 : Type u_1) {A : Type u_2} [inst
 : Field 𝕜] [inst_1 : Ring A] [inst_2 : Algebra 𝕜 A] (a : A),   Polynomial.annId
ealGenerator 𝕜 a =     …
· 使用定理 `Ideal.span_singleton_mul_right_unit`：span_singleton_mul_right_unit {a : 
α} (h2 : IsUnit a) (x : α) : span ({x * a} : Set α) = span {x}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I

--- 原说明 ---
`annIdealGenerator 𝕜 a` is indeed a generator.
-/
theorem span_singleton_annIdealGenerator (a : A) :
    Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, annIdealGenerator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [annIdealGenerator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply Polynomial.isUnit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero.not.mpr
    apply Polynomial.leadingCoeff_eq_zero.not.mpr
    apply (mul_ne_zero_iff.mp h).1

/-- The annihilating ideal generator is a member of the annihilating ideal. -/
/-
**Polynomial.annIdealGenerator_mem** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：annIdealGenerator_mem (a : A) : annIdealGenerator 𝕜 a in annIdeal 𝕜 a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S

--- 原说明 ---
The annihilating ideal generator is a member of the annihilating ideal.
-/
theorem annIdealGenerator_mem (a : A) : annIdealGenerator 𝕜 a ∈ annIdeal 𝕜 a :=
  Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)
/-
**Polynomial.mem_iff_eq_smul_annIdealGenerator** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：mem_iff_eq_smul_annIdealGenerator {p : 𝕜[X]} (a : A) : p in annIdeal 𝕜 a ↔
 exists s : 𝕜[X], p = s • annIdealGenerator 𝕜 a
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.span_singleton_annIdealGenerator`：span_singleton_annIdealGene
rator (a : A) : Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iff_eq_smul_annIdealGenerator {p : 𝕜[X]} (a : A) :
    p ∈ annIdeal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • annIdealGenerator 𝕜 a := by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_annIdealGenerator 𝕜 a]

/-- The generator we chose for the annihilating ideal is monic when the ideal is non-zero. -/
/-
**Polynomial.monic_annIdealGenerator** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_annIdealGenerator (a : A) (hg : annIdealGenerator 𝕜 a != 0) : Monic 
(annIdealGenerator 𝕜 a)
参数：a : A；hg : annIdealGenerator 𝕜 a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
The generator we chose for the annihilating ideal is monic when the ideal is non
-zero.
-/
theorem monic_annIdealGenerator (a : A) (hg : annIdealGenerator 𝕜 a ≠ 0) :
    Monic (annIdealGenerator 𝕜 a) :=
  monic_mul_leadingCoeff_inv (mul_ne_zero_iff.mp hg).1

/-! We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial.

This is the first condition: it must annihilate the original element `a : A`. -/


/-
**Polynomial.annIdealGenerator_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：annIdealGenerator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) 
= 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_annIdeal_iff_aeval_eq_zero`：mem_annIdeal_iff_aeval_eq_zer
o {a : A} {p : R[X]} : p in annIdeal R a ↔ aeval a p = 0
· 使用定理 `Polynomial.annIdealGenerator_mem`：annIdealGenerator_mem (a : A) : annIde
alGenerator 𝕜 a in annIdeal 𝕜 a

--- 原说明 ---
We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial.

This is the first condition: it must annihilate the original element `a : A`.
-/
theorem annIdealGenerator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0 :=
  mem_annIdeal_iff_aeval_eq_zero.mp (annIdealGenerator_mem 𝕜 a)

variable {𝕜}
/-
**Polynomial.mem_iff_annIdealGenerator_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：mem_iff_annIdealGenerator_dvd {p : 𝕜[X]} {a : A} : p in annIdeal 𝕜 a ↔ ann
IdealGenerator 𝕜 a ∣ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Polynomial.span_singleton_annIdealGenerator`：span_singleton_annIdealGene
rator (a : A) : Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff_annIdealGenerator_dvd {p : 𝕜[X]} {a : A} :
    p ∈ annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p := by
  rw [← Ideal.mem_span_singleton, span_singleton_annIdealGenerator]

/-- The generator of the annihilating ideal has minimal degree among
the non-zero members of the annihilating ideal -/
/-
**Polynomial.degree_annIdealGenerator_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：degree_annIdealGenerator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p in annIdeal 
𝕜 a) (hpn0 : p != 0) : degree (annIdealGenerator 𝕜 a) <= degree p
参数：a : A；p : 𝕜[X]；hp : p in annIdeal 𝕜 a；hpn0 : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.degree_le_of_dvd`：degree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0)
 : degree p <= degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_iff_annIdealGenerator_dvd`：mem_iff_annIdealGenerator_dvd 
{p : 𝕜[X]} {a : A} : p in annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p

--- 原说明 ---
The generator of the annihilating ideal has minimal degree among
the non-zero members of the annihilating ideal
-/
theorem degree_annIdealGenerator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p ∈ annIdeal 𝕜 a)
    (hpn0 : p ≠ 0) : degree (annIdealGenerator 𝕜 a) ≤ degree p :=
  degree_le_of_dvd (mem_iff_annIdealGenerator_dvd.1 hp) hpn0

variable (𝕜)

/-- The generator of the annihilating ideal is the minimal polynomial. -/
/-
**Polynomial.annIdealGenerator_eq_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：annIdealGenerator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.annIdealGenerator_eq_zero_iff`：annIdealGenerator_eq_zero_iff 
{a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_annIdeal_iff_aeval_eq_zero`：mem_annIdeal_iff_aeval_eq_zer
o {a : A} {p : R[X]} : p in annIdeal R a ↔ aeval a p = 0
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `Polynomial.monic_annIdealGenerator`：monic_annIdealGenerator (a : A) (hg 
: annIdealGenerator 𝕜 a != 0) : Monic (annIdealGenerator 𝕜 a)
· 使用定理 `Polynomial.annIdealGenerator_aeval_eq_zero`：annIdealGenerator_aeval_eq_z
ero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0
· 使用定理 `Polynomial.degree_annIdealGenerator_le_of_mem`：degree_annIdealGenerator_
le_of_mem (a : A) (p : 𝕜[X]) (hp : p in annIdeal 𝕜 a) (hpn0 : p != 0) : degree (
annIdealGenerator 𝕜 a) <= degree p

--- 原说明 ---
The generator of the annihilating ideal is the minimal polynomial.
-/
theorem annIdealGenerator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a := by
  by_cases h : annIdealGenerator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine p_monic.ne_zero (Ideal.mem_bot.mp ?_)
    simpa only [annIdealGenerator_eq_zero_iff.mp h] using mem_annIdeal_iff_aeval_eq_zero.mpr hp
  · exact minpoly.unique _ _ (monic_annIdealGenerator _ _ h) (annIdealGenerator_aeval_eq_zero _ _)
      fun q q_monic hq =>
        degree_annIdealGenerator_le_of_mem a q (mem_annIdeal_iff_aeval_eq_zero.mpr hq)
          q_monic.ne_zero

/-- If a monic generates the annihilating ideal, it must match our choice
of the annihilating ideal generator. -/
/-
**Polynomial.monic_generator_eq_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic) (p_gen :
 Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p
参数：a : A；p : 𝕜[X]；p_monic : p.Monic；p_gen : Ideal.span {p} = annIdeal 𝕜 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.annIdealGenerator_eq_zero_iff`：annIdealGenerator_eq_zero_iff 
{a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `Polynomial.monic_annIdealGenerator`：monic_annIdealGenerator (a : A) (hg 
: annIdealGenerator 𝕜 a != 0) : Monic (annIdealGenerator 𝕜 a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associated.ne_zero_iff`：Associated.ne_zero_iff [MonoidWithZero M] {a b :
 M} (h : a ~ᵤ b) : a != 0 ↔ b != 0
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.span_singleton_annIdealGenerator`：span_singleton_annIdealGene
rator (a : A) : Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a

--- 原说明 ---
If a monic generates the annihilating ideal, it must match our choice
of the annihilating ideal generator.
-/
theorem monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
    (p_gen : Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p := by
  by_cases h : p = 0
  · rwa [h, annIdealGenerator_eq_zero_iff, ← p_gen, Ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_annIdealGenerator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    apply monic_annIdealGenerator _ _ ((Associated.ne_zero_iff p_gen).mp h)
/-
**Polynomial.span_minpoly_eq_annihilator** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：span_minpoly_eq_annihilator {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.
End 𝕜 M) : Ideal.span {minpoly 𝕜 f} = Module.annihilator 𝕜[X] (Module.AEval' f)
参数：f : Module.End 𝕜 M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.annIdealGenerator_eq_minpoly`：annIdealGenerator_eq_minpoly (a
 : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a
· 使用定理 `Polynomial.span_singleton_annIdealGenerator`：span_singleton_annIdealGene
rator (a : A) : Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Polynomial.mem_annIdeal_iff_aeval_eq_zero`：mem_annIdeal_iff_aeval_eq_zer
o {a : A} {p : R[X]} : p in annIdeal R a ↔ aeval a p = 0
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Module.mem_annihilator`：Module.mem_annihilator {r} : r in Module.annihil
ator R M ↔ forall m : M, r • m = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem span_minpoly_eq_annihilator {M} [AddCommGroup M] [Module 𝕜 M] (f : Module.End 𝕜 M) :
    Ideal.span {minpoly 𝕜 f} = Module.annihilator 𝕜[X] (Module.AEval' f) := by
  rw [← annIdealGenerator_eq_minpoly, span_singleton_annIdealGenerator]; ext
  rw [mem_annIdeal_iff_aeval_eq_zero, DFunLike.ext_iff, Module.mem_annihilator]; rfl

end Field

end Polynomial

