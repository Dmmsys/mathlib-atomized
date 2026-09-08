/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Integrally closed rings

An integrally closed ring `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed rings are the Dedekind domains.

## Main definitions

* `IsIntegrallyClosedIn R A` states `R` contains all integral elements of `A`
* `IsIntegrallyClosed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `isIntegrallyClosed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`

## TODO Related notions

The following definitions are closely related, especially in their applications in Mathlib.

A *normal domain* is a domain that is integrally closed in its field of fractions.
[Stacks: normal domain](https://stacks.math.columbia.edu/tag/037B#0309)
Normal domains are the major use case of `IsIntegrallyClosed` at the time of writing, and we have
quite a few results that can be moved wholesale to a new `NormalDomain` definition.
In fact, before PR https://github.com/leanprover-community/mathlib4/pull/6126 `IsIntegrallyClosed` was exactly defined to be a normal domain.
(So you might want to copy some of its API when you define normal domains.)

A normal ring means that localizations at all prime ideals are normal domains.
[Stacks: normal ring](https://stacks.math.columbia.edu/tag/037B#00GV)
This implies `IsIntegrallyClosed`,
[Stacks: Tag 034M](https://stacks.math.columbia.edu/tag/037B#034M)
but is equivalent to it only under some conditions (reduced + finitely many minimal primes),
[Stacks: Tag 030C](https://stacks.math.columbia.edu/tag/037B#030C)
in which case it's also equivalent to being a finite product of normal domains.

We'd need to add these conditions if we want exactly the products of Dedekind domains.

In fact Noetherianity is sufficient to guarantee finitely many minimal primes, so `IsDedekindRing`
could be defined as `IsReduced`, `IsNoetherian`, `Ring.DimensionLEOne`, and either
`IsIntegrallyClosed` or `NormalDomain`. If we use `NormalDomain` then `IsReduced` is automatic,
but we could also consider a version of `NormalDomain` that only requires the localizations are
`IsIntegrallyClosed` but may not be domains, and that may not equivalent to the ring itself being
`IsIntegrallyClosed` (even for Noetherian rings?).
-/

public section


open scoped nonZeroDivisors Polynomial

open Polynomial

/-- `R` is integrally closed in `A` if all integral elements of `A` are also elements of `R`.
-/
/-
**IsIntegrallyClosedIn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsIntegrallyClosedIn (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
参数：R A : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R` is integrally closed in `A` if all integral elements of `A` are also element
s of `R`.
-/
abbrev IsIntegrallyClosedIn (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :=
  IsIntegralClosure R R A

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `FractionRing R` to denote `Frac(R)`. See `isIntegrallyClosed_iff`
if you want to choose another field of fractions for `R`.
-/
/-
**IsIntegrallyClosed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed (R : Type*) [CommRing R]
参数：R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R` is integrally closed if all integral elements of `Frac(R)` are also elements
 of `R`.

This definition uses `FractionRing R` to denote `Frac(R)`. See `isIntegrallyClos
ed_iff`
if you want to choose another field of fractions for `R`.
-/
abbrev IsIntegrallyClosed (R : Type*) [CommRing R] := IsIntegrallyClosedIn R (FractionRing R)

section Iff

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Being integrally closed is preserved under injective algebra homomorphisms. -/
/-
**AlgHom.isIntegrallyClosedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.isIntegrallyClosedIn (f : A ->ₐ[R] B) (hf : Function.Injective f) :
 IsIntegrallyClosedIn R B -> IsIntegrallyClosedIn R A
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x

--- 原说明 ---
Being integrally closed is preserved under injective algebra homomorphisms.
-/
theorem AlgHom.isIntegrallyClosedIn (f : A →ₐ[R] B) (hf : Function.Injective f) :
    IsIntegrallyClosedIn R B → IsIntegrallyClosedIn R A := by
  rintro ⟨inj, cl⟩
  refine ⟨Function.Injective.of_comp (f := f) ?_, fun hx => ?_, ?_⟩
  · convert! inj
    aesop
  · obtain ⟨y, fx_eq⟩ := cl.mp ((isIntegral_algHom_iff f hf).mpr hx)
    aesop
  · rintro ⟨y, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    simp_all

/-- Being integrally closed is preserved under algebra isomorphisms. -/
/-
**AlgEquiv.isIntegrallyClosedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isIntegrallyClosedIn (e : A ≃ₐ[R] B) : IsIntegrallyClosedIn R A ↔
 IsIntegrallyClosedIn R B
参数：e : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.isIntegrallyClosedIn`：AlgHom.isIntegrallyClosedIn (f : A ->ₐ[R] B
) (hf : Function.Injective f) : IsIntegrallyClosedIn R B -> IsIntegrallyClosedIn
 R A
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
Being integrally closed is preserved under algebra isomorphisms.
-/
theorem AlgEquiv.isIntegrallyClosedIn (e : A ≃ₐ[R] B) :
    IsIntegrallyClosedIn R A ↔ IsIntegrallyClosedIn R B :=
  ⟨AlgHom.isIntegrallyClosedIn e.symm e.symm.injective, AlgHom.isIntegrallyClosedIn e e.injective⟩

variable (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
/-
**isIntegrallyClosed_iff_isIntegrallyClosedIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegrallyClosed_iff_isIntegrallyClosedIn : IsIntegrallyClosed R ↔ IsInt
egrallyClosedIn R K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isIntegrallyClosedIn`：AlgEquiv.isIntegrallyClosedIn (e : A ≃ₐ[R
] B) : IsIntegrallyClosedIn R A ↔ IsIntegrallyClosedIn R B

--- 原说明 ---
`R` is integrally closed iff it is the integral closure of itself in its field o
f fractions.
-/
theorem isIntegrallyClosed_iff_isIntegrallyClosedIn :
    IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K :=
  (IsLocalization.algEquiv R⁰ _ _).isIntegrallyClosedIn

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
/-
**isIntegrallyClosed_iff_isIntegralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegr
alClosure R R K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegrallyClosed_iff_isIntegrallyClosedIn`：isIntegrallyClosed_iff_isIn
tegrallyClosedIn : IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K

--- 原说明 ---
`R` is integrally closed iff it is the integral closure of itself in its field o
f fractions.
-/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  isIntegrallyClosed_iff_isIntegrallyClosedIn K

/-- `R` is integrally closed in `A` iff all integral elements of `A` are also elements of `R`. -/
/-
**isIntegrallyClosedIn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegrallyClosedIn_iff : IsIntegrallyClosedIn R A ↔ Function.Injective (
algebraMap R A) ∧ forall {x : A}, IsIntegral R x -> exists y, algebraMap R A y =
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)

--- 原说明 ---
`R` is integrally closed in `A` iff all integral elements of `A` are also elemen
ts of `R`.
-/
theorem isIntegrallyClosedIn_iff :
    IsIntegrallyClosedIn R A ↔
      Function.Injective (algebraMap R A) ∧
        ∀ {x : A}, IsIntegral R x → ∃ y, algebraMap R A y = x := by
  constructor
  · rintro ⟨_, cl⟩
    simp_all
  · rintro ⟨inj, cl⟩
    refine ⟨inj, by simp_all, ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
/-
**isIntegrallyClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ forall {x : K}, IsIntegral
 R x -> exists y, algebraMap R K y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isIntegrallyClosed_iff_isIntegrallyClosedIn`：isIntegrallyClosed_iff_isIn
tegrallyClosedIn : IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`.
-/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x := by
  simp [isIntegrallyClosed_iff_isIntegrallyClosedIn K, isIntegrallyClosedIn_iff,
        IsFractionRing.injective R K]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegrallyClosedIn (integralClosure R A) A :=
  isIntegrallyClosedIn_iff.mpr
    ⟨FaithfulSMul.algebraMap_injective _ _, fun h ↦ ⟨⟨_, isIntegral_trans _ h⟩, rfl⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegrallyClosedIn (integralClosure R A).toSubring A :=
  inferInstanceAs (IsIntegrallyClosedIn (integralClosure R A) A)

namespace Subring

variable {C : Type*} [SetLike C A] [SubringClass C A] {S : C}

/-
**Subring.isIntegrallyClosedIn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {A : Type u_2} [inst : CommRing A] {C : Type u_5} [inst_1 : SetLike C A]
 [inst_2 : SubringClass C A] {S : C},   IsIntegrallyClosedIn (↥S) A ↔ ∀ ⦃x : A⦄,
 IsIntegral (↥S) x → x ∈ S
参数：↥S。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isIntegrallyClosedIn_iff`：isIntegrallyClosedIn_iff : IsIntegrallyClosedI
n R A ↔ Function.Injective (algebraMap R A) ∧ forall {x : A}, IsIntegral R x -> 
exists y, alge…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Subsemiring.instFaithfulSMulSubtypeMem`：∀ {M' : Type u_5} {α : Type u_6}
 [inst : SMul M' α] {S' : Type u_7} [inst_1 : SetLike S' M'] (s : S')   [Faithfu
lSMul M' α], FaithfulSMul (↥…
· 使用定理 `instFaithfulSMul`：∀ (R : Type u_4) [inst : MulOneClass R], FaithfulSMul 
R R
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
protected theorem isIntegrallyClosedIn_iff :
    IsIntegrallyClosedIn S A ↔ ∀ ⦃x : A⦄, IsIntegral S x → x ∈ S := by
  rw [isIntegrallyClosedIn_iff, and_iff_right (FaithfulSMul.algebraMap_injective _ _)]
  exact congr(∀ _ _, _ ∈ $Subtype.range_val)
/-
**Subring.isIntegrallyClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {A : Type u_2} [inst : CommRing A] {C : Type u_5} [inst_1 : SetLike C A]
 [inst_2 : SubringClass C A] {S : C}   [IsFractionRing (↥S) A], IsIntegrallyClos
ed ↥S ↔ ∀ ⦃x : A⦄, IsIntegral (↥S) x → x ∈ S
参数：↥S。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
protected theorem isIntegrallyClosed_iff [IsFractionRing S A] :
    IsIntegrallyClosed S ↔ ∀ ⦃x : A⦄, IsIntegral S x → x ∈ S := by
  rw [isIntegrallyClosed_iff A]; exact congr(∀ _ _, _ ∈ $Subtype.range_val)
/-
**Subring.integralClosure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：integralClosure_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] : (integ
ralClosure R A).toSubring <= T ↔ forall r, algebraMap R A r in T where mp h r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.isIntegrallyClosedIn_iff`：∀ {A : Type u_2} [inst : CommRing A] {
C : Type u_5} [inst_1 : SetLike C A] [inst_2 : SubringClass C A] {S : C},   IsIn
tegrallyClosedIn (↥S) …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
-/
theorem integralClosure_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] :
    (integralClosure R A).toSubring ≤ T ↔ ∀ r, algebraMap R A r ∈ T where
  mp h r := h (algebraMap_mem (integralClosure R A) r)
  mpr h a ha := Subring.isIntegrallyClosedIn_iff.mp ‹_› <|
    let : Algebra R T := RingHom.toAlgebra <| .codRestrict _ _ h
    have : IsScalarTower R T A := .of_algebraMap_eq fun _ ↦ rfl
    ha.tower_top
/-
**Subring.integralClosure_subring_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：integralClosure_subring_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] 
: (integralClosure S A).toSubring <= T ↔ .ofClass S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.integralClosure_le_iff`：integralClosure_le_iff {T : Subring A} [
IsIntegrallyClosedIn T A] : (integralClosure R A).toSubring <= T ↔ forall r, alg
ebraMap R A r in T w…
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integralClosure_subring_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] :
    (integralClosure S A).toSubring ≤ T ↔ .ofClass S ≤ T := by
  rw [integralClosure_le_iff, Subtype.forall, SetLike.le_def]; rfl

end Subring

end Iff

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-
**IsIntegrallyClosedIn.** 是 Mathlib 中的一个实例，位于命名空间 `IsIntegrallyClosedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIntegrallyClosedIn R R :=
  ⟨Function.injective_id, by simp [Algebra.IsIntegral.isIntegral]⟩
/-
**IsIntegrallyClosedIn.algebraMap_eq_of_integral** 是 Mathlib 中的一个定理，位于命名空间 `IsIn
tegrallyClosedIn`。
形式化陈述：algebraMap_eq_of_integral [IsIntegrallyClosedIn R A] {x : A} : IsIntegral 
R x -> exists y : R, algebraMap R A y = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
-/
theorem algebraMap_eq_of_integral [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x → ∃ y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff.mp
/-
**IsIntegrallyClosedIn.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegrallyClo
sedIn`。
形式化陈述：isIntegral_iff [IsIntegrallyClosedIn R A] {x : A} : IsIntegral R x ↔ exist
s y : R, algebraMap R A y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
-/
theorem isIntegral_iff [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x ↔ ∃ y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff
/-
**IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow** 是 Mathlib 中的一个定理
，位于命名空间 `IsIntegrallyClosedIn`。
形式化陈述：exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A] {x : A} 
{n : Nat} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) : exists y : R, algebraMap R
 A y = x
参数：hn : 0 < n；hx : IsIntegral R <| x ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosedIn.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosedI
n R A] {x : A} : IsIntegral R x ↔ exists y : R, algebraMap R A y = x
· 使用定理 `IsIntegral.of_pow`：IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn
 : 0 < n) (hx : IsIntegral R <| x ^ n) : IsIntegral R x
-/
theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A]
    {x : A} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R A y = x :=
  isIntegral_iff.mp <| hx.of_pow hn
/-
**IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra** 是 Mathlib 中的
一个定理，位于命名空间 `IsIntegrallyClosedIn`。
形式化陈述：exists_algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algeb
ra R A] {S : Subalgebra R A} [IsIntegrallyClosedIn S A] {x : A} {n : Nat} (hn : 
0 < n) (hx : x ^ n in S) : exists y : S, algebraMap S A y = x
参数：hn : 0 < n；hx : x ^ n in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow`：exists_alge
braMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A] {x : A} {n : Nat} (hn : 0
 < n) (hx : IsIntegral R <| x ^ n) : exists y : R…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsIntegrallyClosedIn.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosedI
n R A] {x : A} : IsIntegral R x ↔ exists y : R, algebraMap R A y = x
-/
theorem exists_algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algebra R A]
    {S : Subalgebra R A} [IsIntegrallyClosedIn S A] {x : A} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S A y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

variable (A)
/-
**IsIntegrallyClosedIn.integralClosure_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsI
ntegrallyClosedIn`。
形式化陈述：integralClosure_eq_bot_iff (hRA : Function.Injective (algebraMap R A)) : i
ntegralClosure R A = ⊥ ↔ IsIntegrallyClosedIn R A
参数：hRA : Function.Injective (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegrallyClosedIn.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosedI
n R A] {x : A} : IsIntegral R x ↔ exists y : R, algebraMap R A y = x
-/
theorem integralClosure_eq_bot_iff (hRA : Function.Injective (algebraMap R A)) :
    integralClosure R A = ⊥ ↔ IsIntegrallyClosedIn R A := by
  refine eq_bot_iff.trans ?_
  constructor
  · intro h
    refine ⟨ hRA, fun hx => Set.mem_range.mp (Algebra.mem_bot.mp (h hx)), ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact isIntegral_iff.mp hx

variable (R)

@[simp]
/-
**IsIntegrallyClosedIn.integralClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsInteg
rallyClosedIn`。
形式化陈述：integralClosure_eq_bot [IsIntegrallyClosedIn R A] [IsDomain R] [Module.IsT
orsionFree R A] [Nontrivial A] : integralClosure R A = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsIntegrallyClosedIn.integralClosure_eq_bot_iff`：integralClosure_eq_bot_
iff (hRA : Function.Injective (algebraMap R A)) : integralClosure R A = ⊥ ↔ IsIn
tegrallyClosedIn R A
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem integralClosure_eq_bot [IsIntegrallyClosedIn R A] [IsDomain R] [Module.IsTorsionFree R A]
    [Nontrivial A] : integralClosure R A = ⊥ :=
  (integralClosure_eq_bot_iff A (FaithfulSMul.algebraMap_injective _ _)).mpr ‹_›

variable {A} {B : Type*} [CommRing B]

/-- If `R` is the integral closure of `S` in `A`, then it is integrally closed in `A`. -/
/-
**IsIntegrallyClosedIn.of_isIntegralClosure** 是 Mathlib 中的一个引理，位于命名空间 `IsIntegra
llyClosedIn`。
形式化陈述：of_isIntegralClosure [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Is
IntegralClosure A R B] : IsIntegrallyClosedIn A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用引理 `IsIntegralClosure.tower_top`：IsIntegralClosure.tower_top {B C : Type*} [
CommSemiring C] [CommRing B] [Algebra R B] [Algebra A B] [Algebra C B] [IsScalar
Tower R A B] [IsI…

--- 原说明 ---
If `R` is the integral closure of `S` in `A`, then it is integrally closed in `A
`.
-/
lemma of_isIntegralClosure [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegralClosure A R B] :
    IsIntegrallyClosedIn A B :=
  have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R B
  IsIntegralClosure.tower_top (R := R)

variable {R}
/-
**IsIntegrallyClosedIn._root_.IsIntegralClosure.of_isIntegrallyClosedIn** 是 Math
lib 中的一个引理，位于命名空间 `IsIntegrallyClosedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsIntegralClosure.of_isIntegrallyClosedIn
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegrallyClosedIn A B] [Algebra.IsIntegral R A] :
    IsIntegralClosure A R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective _ A _, fun {x} ↦
    ⟨fun hx ↦ IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := A) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom A A B) (Algebra.IsIntegral.isIntegral y)

end IsIntegrallyClosedIn

namespace IsIntegrallyClosed

variable {R S : Type*} [CommRing R] [CommRing S]
variable {K : Type*} [CommRing K] [Algebra R K] [ifr : IsFractionRing R K]

/-- Note that this is not a duplicate instance, since `IsIntegrallyClosed R` is instead defined
as `IsIntegrallyClosed R R (FractionRing R)`. -/
/-
**IsIntegrallyClosed.** 是 Mathlib 中的一个实例，位于命名空间 `IsIntegrallyClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this is not a duplicate instance, since `IsIntegrallyClosed R` is inst
ead defined
as `IsIntegrallyClosed R R (FractionRing R)`.
-/
instance [iic : IsIntegrallyClosed R] : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic
/-
**IsIntegrallyClosed.algebraMap_eq_of_integral** 是 Mathlib 中的一个定理，位于命名空间 `IsInte
grallyClosed`。
形式化陈述：algebraMap_eq_of_integral [IsIntegrallyClosed R] {x : K} : IsIntegral R x 
-> exists y : R, algebraMap R K y = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `IsIntegrallyClosed.instIsIntegralClosure`：∀ {R : Type u_1} [inst : CommR
ing R] {K : Type u_3} [inst_1 : CommRing K] [inst_2 : Algebra R K]   [ifr : IsFr
actionRing R K] [iic : IsInteg…
-/
theorem algebraMap_eq_of_integral [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x → ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff.mp
/-
**IsIntegrallyClosed.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegrallyClose
d`。
形式化陈述：isIntegral_iff [IsIntegrallyClosed R] {x : K} : IsIntegral R x ↔ exists y 
: R, algebraMap R K y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosedIn.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosedI
n R A] {x : A} : IsIntegral R x ↔ exists y : R, algebraMap R A y = x
· 使用定理 `IsIntegrallyClosed.instIsIntegralClosure`：∀ {R : Type u_1} [inst : CommR
ing R] {K : Type u_3} [inst_1 : CommRing K] [inst_2 : Algebra R K]   [ifr : IsFr
actionRing R K] [iic : IsInteg…
-/
theorem isIntegral_iff [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.isIntegral_iff
/-
**IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow** 是 Mathlib 中的一个定理，位
于命名空间 `IsIntegrallyClosed`。
形式化陈述：exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosed R] {x : K} {n :
 Nat} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) : exists y : R, algebraMap R K y
 = x
参数：hn : 0 < n；hx : IsIntegral R <| x ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow`：exists_alge
braMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A] {x : A} {n : Nat} (hn : 0
 < n) (hx : IsIntegral R <| x ^ n) : exists y : R…
· 使用定理 `IsIntegrallyClosed.instIsIntegralClosure`：∀ {R : Type u_1} [inst : CommR
ing R] {K : Type u_3} [inst_1 : CommRing K] [inst_2 : Algebra R K]   [ifr : IsFr
actionRing R K] [iic : IsInteg…
-/
theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosed R] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hx
/-
**IsIntegrallyClosed.exists_algebraMap_eq_of_pow_mem_subalgebra** 是 Mathlib 中的一个
定理，位于命名空间 `IsIntegrallyClosed`。
形式化陈述：exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [CommRing K] [Algeb
ra R K] {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K}
 {n : Nat} (hn : 0 < n) (hx : x ^ n in S) : exists y : S, algebraMap S K y = x
参数：hn : 0 < n；hx : x ^ n in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra`：exists_
algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algebra R A] {S : 
Subalgebra R A} [IsIntegrallyClosedIn S A] {x : A} {n…
· 使用定理 `IsIntegrallyClosed.instIsIntegralClosure`：∀ {R : Type u_1} [inst : CommR
ing R] {K : Type u_3} [inst_1 : CommRing K] [inst_2 : Algebra R K]   [ifr : IsFr
actionRing R K] [iic : IsInteg…
-/
theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [CommRing K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra hn hx
/-
**IsIntegrallyClosed.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegrallyClosed`。
形式化陈述：of_equiv (f : R ≃+* S) [h : IsIntegrallyClosed R] : IsIntegrallyClosed S
参数：f : R ≃+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `isIntegral_algEquiv`：isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B]
 [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIn
tegral R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsFractionRing.algEquivOfAlgEquiv_algebraMap`：algEquivOfAlgEquiv_algebra
Map (a : A) : algEquivOfAlgEquiv h (algebraMap A K a) = algebraMap B L (h a)
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
-/
theorem of_equiv (f : R ≃+* S) [h : IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ ↦ rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx ↦ ?_)
  rcases (isIntegrallyClosed_iff _).mp h ((isIntegral_algEquiv g).mpr hx).tower_top with ⟨z, hz⟩
  exact ⟨f.symm z, (IsFractionRing.algEquivOfAlgEquiv_algebraMap f.symm z).symm.trans <|
    (AlgEquiv.symm_apply_eq g).mpr hz⟩

variable (R S K)
/-
**IsIntegrallyClosed._root_.IsIntegralClosure.of_isIntegrallyClosed** 是 Mathlib 
中的一个实例，位于命名空间 `IsIntegrallyClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.IsIntegralClosure.of_isIntegrallyClosed [IsIntegrallyClosed R]
    [Algebra S R] [Algebra S K] [IsScalarTower S R K] [Algebra.IsIntegral S R] :
    IsIntegralClosure R S K :=
  IsIntegralClosure.of_isIntegrallyClosedIn
/-
**IsIntegrallyClosed.of_isIntegrallyClosedIn** 是 Mathlib 中的一个引理，位于命名空间 `IsIntegr
allyClosed`。
形式化陈述：of_isIntegrallyClosedIn (R K : Type*) [CommRing R] [Field K] [Algebra R K]
 [FaithfulSMul R K] [IsIntegrallyClosedIn R K] : IsIntegrallyClosed R
参数：R K : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
-/
lemma of_isIntegrallyClosedIn
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
    [IsIntegrallyClosedIn R K] : IsIntegrallyClosed R := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R K).isDomain _
  let f : FractionRing R →ₐ[R] K := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _)
    (FaithfulSMul.algebraMap_injective R K)
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  convert! (IsIntegralClosure.isIntegral_iff (A := R)).mp (hx.map f)
  simp [← f.toRingHom.injective.eq_iff]
/-
**IsIntegrallyClosed._root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegral
lyClosedIn** 是 Mathlib 中的一个引理，位于命名空间 `IsIntegrallyClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower S T U] [IsScalarTower R T U]
    [IsIntegralClosure S R T] [IsIntegrallyClosedIn T U] : IsIntegralClosure S R U := by
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq S T U]
    exact (IsIntegralClosure.algebraMap_injective T T U).comp
      (IsIntegralClosure.algebraMap_injective S R T)
  · intro x
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := T) (A := T)).mp h.tower_top
      rw [isIntegral_algebraMap_iff (IsIntegralClosure.algebraMap_injective T T U)] at h
      obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := S)).mp h
      exact ⟨x, IsScalarTower.algebraMap_apply ..⟩
    · rintro ⟨x, rfl⟩
      rw [IsScalarTower.algebraMap_apply S T U]
      exact ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := T)).mpr ⟨x, rfl⟩).map
        (IsScalarTower.toAlgHom R T U)
/-
**IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn** 是 Mathlib 中
的一个引理，位于命名空间 `IsIntegrallyClosed`。
形式化陈述：of_isIntegrallyClosed_of_isIntegrallyClosedIn [Algebra R S] [IsDomain S] [
FaithfulSMul R S] [IsIntegrallyClosed S] [IsIntegrallyClosedIn R S] : IsIntegral
lyClosed R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn`：∀ (R : T
ype u_4) (S : Type u_5) (T : Type u_6) (U : Type u_7) [inst : CommRing R] [inst_
1 : CommRing S]   [inst_2 : CommRing T] [inst_3 : Co…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsIntegrallyClosed.of_isIntegrallyClosedIn`：of_isIntegrallyClosedIn (R K
 : Type*) [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [IsIntegrallyC
losedIn R K] : IsIntegrallyClose…
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
-/
lemma of_isIntegrallyClosed_of_isIntegrallyClosedIn
    [Algebra R S] [IsDomain S] [FaithfulSMul R S]
    [IsIntegrallyClosed S] [IsIntegrallyClosedIn R S] : IsIntegrallyClosed R :=
  have : IsIntegrallyClosedIn R (FractionRing S) :=
    .of_isIntegralClosure_of_isIntegrallyClosedIn _ _ S _
  .of_isIntegrallyClosedIn R (FractionRing S)

variable {R}
/-
**IsIntegrallyClosed.integralClosure_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsInt
egrallyClosed`。
形式化陈述：integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed 
R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsIntegrallyClosedIn.integralClosure_eq_bot_iff`：integralClosure_eq_bot_
iff (hRA : Function.Injective (algebraMap R A)) : integralClosure R A = ⊥ ↔ IsIn
tegrallyClosedIn R A
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isIntegrallyClosed_iff_isIntegrallyClosedIn`：isIntegrallyClosed_iff_isIn
tegrallyClosedIn : IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K
-/
theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ (IsFractionRing.injective _ _)).trans
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).symm

@[simp]
/-
**IsIntegrallyClosed.pow_dvd_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegrallyClos
ed`。
形式化陈述：pow_dvd_pow_iff [IsDomain R] [IsIntegrallyClosed R] {n : Nat} (hn : n != 0
) {a b : R} : a ^ n ∣ b ^ n ↔ a ∣ b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
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
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
（共 38 条，此处仅展示前 30 条）
-/
theorem pow_dvd_pow_iff [IsDomain R] [IsIntegrallyClosed R]
    {n : ℕ} (hn : n ≠ 0) {a b : R} : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  by_cases ha : a = 0
  · simpa [ha, hn] using hx
  let K := FractionRing R
  replace ha : algebraMap R K a ≠ 0 := fun h ↦
    ha <| (injective_iff_map_eq_zero _).1 (IsFractionRing.injective R K) _ h
  let y := (algebraMap R K b) / (algebraMap R K a)
  have hy : IsIntegral R y := by
    refine ⟨X ^ n - C x, monic_X_pow_sub_C _ hn, ?_⟩
    simp only [y, eval₂_sub, eval₂_X_pow, div_pow, eval₂_C]
    replace hx := congr_arg (algebraMap R K) hx
    rw [map_pow] at hx
    simp [hx, ha]
  obtain ⟨k, hk⟩ := algebraMap_eq_of_integral hy
  refine ⟨k, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hk, mul_div_cancel₀ _ ha]

@[simp]
/-
**IsIntegrallyClosed._root_.Associated.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsInte
grallyClosed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Associated.pow_iff [IsDomain R] [IsIntegrallyClosed R] {n : ℕ} (hn : n ≠ 0)
    {a b : R} :
    Associated (a ^ n) (b ^ n) ↔ Associated a b := by
  simp_rw [← dvd_dvd_iff_associated, pow_dvd_pow_iff hn]

variable (R)

/-- This is almost a duplicate of `IsIntegrallyClosedIn.integralClosure_eq_bot`,
except the `Module.IsTorsionFree` hypothesis isn't inferred automatically from `IsFractionRing`. -/
@[simp]
/-
**IsIntegrallyClosed.integralClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegra
llyClosed`。
形式化陈述：integralClosure_eq_bot [IsIntegrallyClosed R] : integralClosure R K = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsIntegrallyClosed.integralClosure_eq_bot_iff`：integralClosure_eq_bot_if
f : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R

--- 原说明 ---
This is almost a duplicate of `IsIntegrallyClosedIn.integralClosure_eq_bot`,
except the `Module.IsTorsionFree` hypothesis isn't inferred automatically from `
IsFractionRing`.
-/
theorem integralClosure_eq_bot [IsIntegrallyClosed R] : integralClosure R K = ⊥ :=
  (integralClosure_eq_bot_iff K).mpr ‹_›

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type*} [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable [IsFractionRing R K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
/-
**integralClosure.isIntegrallyClosedOfFiniteExtension** 是 Mathlib 中的一个定理，位于命名空间 
`integralClosure`。
形式化陈述：isIntegrallyClosedOfFiniteExtension [IsDomain R] [FiniteDimensional K L] :
 IsIntegrallyClosed (integralClosure R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.integralClosure_eq_bot_iff`：integralClosure_eq_bot_if
f : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R
· 使用定理 `integralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_fi
nite_extension [IsDomain A] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [F
initeDimensional K L] : IsFractionRing (…
· 使用定理 `integralClosure_idem`：integralClosure_idem {R A : Type*} [CommRing R] [C
ommRing A] [Algebra R A] : integralClosure (integralClosure R A) A = ⊥
-/
theorem isIntegrallyClosedOfFiniteExtension [IsDomain R] [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem

end integralClosure

section localization

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/-
**isIntegrallyClosed_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegrallyClosed_of_isLocalization [IsIntegrallyClosed R] [IsDomain R] (
M : Submonoid R) (hM : M <= R⁰) [IsLocalization M S] : IsIntegrallyClosed S
参数：M : Submonoid R；hM : M <= R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`：isFractionR
ing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S] [CommR
ing T] [Algebra R S] [Algebra R T] [Algebra S T] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff_isIntegralClosure`：isIntegrallyClosed_iff_isInteg
ralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `IsIntegral.exists_multiple_integral_of_isLocalization`：IsIntegral.exists
_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : 
S) (hx : IsIntegral Rₘ x) : exists m : M, I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.lift_mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] {P : Type u_3} …
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma isIntegrallyClosed_of_isLocalization [IsIntegrallyClosed R] [IsDomain R] (M : Submonoid R)
    (hM : M ≤ R⁰) [IsLocalization M S] : IsIntegrallyClosed S := by
  let K := FractionRing R
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp ‹_› hy
  refine ⟨IsLocalization.mk' S z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id, hz, ← Algebra.smul_def, Submonoid.mk_smul]

end localization

/-- Any field is integral closed. -/
/- Although `infer_instance` can find this if you import Mathlib, in this file they have not been
  proven yet. However, it is used to prove a fundamental property of `IsIntegrallyClosed`,
  and it is not desirable to involve more content from other files. -/
/-
**Field.instIsIntegrallyClosed** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Field.instIsIntegrallyClosed (K : Type*) [Field K] : IsIntegrallyClosed K
参数：K : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `instIsFractionRing`：∀ {R : Type u_6} [inst : Field R], IsFractionRing R 
R

--- 原说明 ---
Although `infer_instance` can find this if you import Mathlib, in this file they
 have not been
  proven yet. However, it is used to prove a fundamental property of `IsIntegral
lyClosed`,
  and it is not desirable to involve more content from other files.
-/
instance Field.instIsIntegrallyClosed (K : Type*) [Field K] : IsIntegrallyClosed K :=
  (isIntegrallyClosed_iff K).mpr fun {x} _ ↦ ⟨x, rfl⟩
