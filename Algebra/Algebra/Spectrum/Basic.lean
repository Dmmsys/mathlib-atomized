/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra

This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ (↑ₐ r - a)⁻¹ʳ`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐ r - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_comm` and `spectrum.preimage_units_mul_comm`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.resolvent_sub_resolvent`: the second resolvent identity.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

@[expose] public section

open Set

open scoped Pointwise Ring

universe u v

section Defs

variable (R : Type u) {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

-- definition and basic properties
/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`. -/
/-
**resolventSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：resolventSet (a : A) : Set R
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a :
 A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.
-/
def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set. -/
/-
**spectrum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectrum (a : A) : Set R
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is not a unit of 
the
algebra `A`.

The spectrum is simply the complement of the resolvent set.
-/
def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebraMap R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
/-
**resolvent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：resolvent (a : A) (r : R) : A
参数：a : A；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebraMap R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`.
-/
noncomputable def resolvent (a : A) (r : R) : A := (↑ₐ r - a)⁻¹ʳ

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
/-
**IsUnit.subInvSMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : 
Aˣ where val
参数：h : IsUnit <| r • ↑ₐ s - a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit.
-/
noncomputable def IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]

end Defs

namespace spectrum

section ScalarSemiring

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/-
**spectrum.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
/-
**spectrum.resolvent_zero_of_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolvent_zero_of_mem_spectrum {r : R} {a : A} (hr : r in σ a) : resolvent
 a r = 0
参数：hr : r in σ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
-/
theorem resolvent_zero_of_mem_spectrum {r : R} {a : A} (hr : r ∈ σ a) :
    resolvent a r = 0 := Ring.inverse_non_unit _ (mem_iff.mp hr)
/-
**spectrum.mem_spectrum_iff_resolvent_zero** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：mem_spectrum_iff_resolvent_zero [Nontrivial A] {r : R} {a : A} : r in σ a 
↔ resolvent a r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.resolvent_zero_of_mem_spectrum`：resolvent_zero_of_mem_spectrum 
{r : R} {a : A} (hr : r in σ a) : resolvent a r = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mem_spectrum_iff_resolvent_zero [Nontrivial A] {r : R} {a : A} :
    r ∈ σ a ↔ resolvent a r = 0 := by
  refine ⟨resolvent_zero_of_mem_spectrum, fun hr ↦ ?_⟩
  simpa [mem_iff, Ring.not_isUnit_iff_inverse_eq_zero]
/-
**spectrum.notMem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by
  simp [mem_iff]

variable (R)
/-
**spectrum.zero_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：zero_mem_iff {a : A} : (0 : R) in σ a ↔ ¬IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬IsUnit a := by
  rw [mem_iff, map_zero, zero_sub, IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff
/-
**spectrum.zero_notMem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.zero_mem_iff`：zero_mem_iff {a : A} : (0 : R) in σ a ↔ ¬IsUnit a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [zero_mem_iff, Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

@[simp]
/-
**spectrum._root_.Units.zero_notMem_spectrum** 是 Mathlib 中的一个引理，位于命名空间 `spectrum
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.zero_notMem_spectrum (a : Aˣ) : 0 ∉ spectrum R (a : A) :=
  spectrum.zero_notMem R a.isUnit
/-
**spectrum.subset_singleton_zero_compl** 是 Mathlib 中的一个引理，位于命名空间 `spectrum`。
形式化陈述：subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a subsete
q {0}ᶜ
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_compl_singleton_iff`：subset_compl_singleton_iff : s subseteq 
{a}ᶜ ↔ a ∉ s
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
-/
lemma subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ :=
  Set.subset_compl_singleton_iff.mpr <| spectrum.zero_notMem R ha

variable {R}
/-
**spectrum.mem_resolventSet_of_left_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `spe
ctrum`。
形式化陈述：mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a
) * b = 1) (h₂ : c * (↑ₐ r - a) = 1) : r in resolventSet R a
参数：h₁ : (↑ₐ r - a) * b = 1；h₂ : c * (↑ₐ r - a) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
-/
theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ resolventSet R a :=
  Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩
/-
**spectrum.mem_resolventSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：mem_resolventSet_iff {r : R} {a : A} : r in resolventSet R a ↔ IsUnit (↑ₐ 
r - a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_resolventSet_iff {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
/-
**spectrum.algebraMap_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemirin
g S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a
 : A} {r : R} : algebraMap R S r in spectrum S a ↔ r in spectrum R a
参数：S : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ spectrum S a ↔ r ∈ spectrum R a := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

@[simp]
/-
**spectrum.preimage_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiri
ng S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {
a : A} : algebraMap R S ⁻¹' spectrum S a = spectrum R a
参数：S : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `spectrum.algebraMap_mem_iff`：algebraMap_mem_iff (S : Type*) {R A : Type*
} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebr
a S A] [IsScalarT…
-/
theorem preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a :=
  Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]
/-
**spectrum.resolventSet_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a =
 Set.univ
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.ofPred_true]

@[simp]
/-
**spectrum.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [inst
_1 : Ring A] [inst_2 : Algebra R A] (a : A),   spectrum R a = (resolventSet R a)
ᶜ
· 使用定理 `spectrum.resolventSet_of_subsingleton`：resolventSet_of_subsingleton [Sub
singleton A] (a : A) : resolventSet R a = Set.univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, resolventSet_of_subsingleton, Set.compl_univ]
/-
**spectrum.resolvent_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolvent_eq {a : A} {r : R} (h : r in resolventSet R a) : resolvent a r =
 ↑h.unit⁻¹
参数：h : r in resolventSet R a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit

/-- The second resolvent identity: for `r` in the resolvent set of both
`a` and `b`,
`resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r`. -/
/-
**spectrum.resolvent_sub_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolvent_sub_resolvent {a b : A} {r : R} (ha : r in resolventSet R a) (hb
 : r in resolventSet R b) : resolvent a r - resolvent b r = resolvent a r * (a -
 b) * resolvent b r
参数：ha : r in resolventSet R a；hb : r in resolventSet R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.resolvent_eq`：resolvent_eq {a : A} {r : R} (h : r in resolventS
et R a) : resolvent a r = ↑h.unit⁻¹
· 使用定理 `Units.eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑
c⁻¹ ↔ a * c = b
· 使用定理 `Units.eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ 
* c ↔ ↑b * a = c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Basic.0.spectrum.resolvent_sub
_resolvent._abel_1_1`：∀ {R : Type u_2} {A : Type u_1} [inst : CommSemiring R] [i
nst_1 : Ring A] [inst_2 : Algebra R A] {a b : A} {r : R},   (algebraMap R A) r -
 b…

--- 原说明 ---
The second resolvent identity: for `r` in the resolvent set of both
`a` and `b`,
`resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r`.
-/
theorem resolvent_sub_resolvent {a b : A} {r : R}
    (ha : r ∈ resolventSet R a) (hb : r ∈ resolventSet R b) :
    resolvent a r - resolvent b r = resolvent a r * (a - b) * resolvent b r := by
  rw [resolvent_eq ha, resolvent_eq hb, Units.eq_mul_inv_iff_mul_eq, Units.eq_inv_mul_iff_mul_eq,
    sub_mul, Units.inv_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one,
    hb.unit_spec, ha.unit_spec]
  abel
/-
**spectrum.units_smul_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：units_smul_resolvent {r : Rˣ} {s : R} {a : A} : r • resolvent a (s : R) = 
resolvent (r⁻¹ • a) (r⁻¹ • s : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `IsUnit.smul`：IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommC
lass G M M] [IsScalarTower G M M] {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m
)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `spectrum.notMem_iff`：notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r
 - a)
· 使用定理 `IsUnit.val_subInvSMul`：∀ {R : Type u} {A : Type v} [inst : CommSemiring 
R] [inst_1 : Ring A] [inst_2 : Algebra R A] {r : Rˣ} {s : R} {a : A}   (h : IsUn
it (r • (al…
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `IsUnit.val_inv_subInvSMul`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Ring A] [inst_2 : Algebra R A] {r : Rˣ} {s : R} {a : A}   (h : 
IsUnit (r • (al…
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
-/
theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s ∈ spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using notMem_iff.mp h
    rw [← h'.val_subInvSMul, ← (notMem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]
/-
**spectrum.units_smul_resolvent_self** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：units_smul_resolvent_self {r : Rˣ} {a : A} : r • resolvent a (r : R) = res
olvent (r⁻¹ • a) (1 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `spectrum.units_smul_resolvent`：units_smul_resolvent {r : Rˣ} {s : R} {a 
: A} : r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R)
-/
theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

/-- The resolvent is a unit when the argument is in the resolvent set. -/
/-
**spectrum.isUnit_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：isUnit_resolvent {r : R} {a : A} : r in resolventSet R a ↔ IsUnit (resolve
nt a r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isUnit_ringInverse`：isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a

--- 原说明 ---
The resolvent is a unit when the argument is in the resolvent set.
-/
theorem isUnit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ringInverse.symm
/-
**spectrum.inv_mem_resolventSet** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) in resolventSet R (a :
 A)) : (↑r⁻¹ : R) in resolventSet R (↑a⁻¹ : A)
参数：h : (r : R) in resolventSet R (a : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.mem_resolventSet_iff`：mem_resolventSet_iff {r : R} {a : A} : r 
in resolventSet R a ↔ IsUnit (↑ₐ r - a)
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用引理 `IsUnit.smul_sub_iff_sub_inv_smul`：IsUnit.smul_sub_iff_sub_inv_smul [Grou
p G] [Monoid R] [AddGroup R] [DistribMulAction G R] [IsScalarTower G R R] [SMulC
ommClass G R R] (r : G…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `IsUnit.sub_iff`：IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsU
nit (y - x)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
-/
theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by
  rw [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv, IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • (1 : A) - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  exact (hcomm.isUnit_mul_iff.mp (h₁.symm ▸ h)).2
/-
**spectrum.inv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) in σ (a : A) ↔ (↑r⁻¹ : R) in σ (↑a
⁻¹ : A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `spectrum.inv_mem_resolventSet`：inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h
 : (r : R) in resolventSet R (a : A)) : (↑r⁻¹ : R) in resolventSet R (↑a⁻¹ : A)
-/
theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) :=
  not_iff_not.2 <| ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩
/-
**spectrum.zero_mem_resolventSet_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：zero_mem_resolventSet_of_unit (a : Aˣ) : 0 in resolventSet R (a : A)
参数：a : Aˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [mem_resolventSet_iff, ← notMem_iff, zero_notMem_iff] using a.isUnit
/-
**spectrum.ne_zero_of_mem_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r in σ (a : A)) : r != 0
参数：hr : r in σ (a : A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.zero_mem_resolventSet_of_unit`：zero_mem_resolventSet_of_unit (a
 : Aˣ) : 0 in resolventSet R (a : A)
-/
theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)
/-
**spectrum.add_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：add_mem_iff {a : A} {r s : R} : r + s in σ a ↔ r in σ (-↑ₐ s + a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_mem_iff {a : A} {r s : R} : r + s ∈ σ a ↔ r ∈ σ (-↑ₐ s + a) := by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]
/-
**spectrum.add_mem_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：add_mem_add_iff {a : A} {r s : R} : r + s in σ (↑ₐ s + a) ↔ r in σ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.add_mem_iff`：add_mem_iff {a : A} {r s : R} : r + s in σ a ↔ r i
n σ (-↑ₐ s + a)
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_mem_add_iff {a : A} {r s : R} : r + s ∈ σ (↑ₐ s + a) ↔ r ∈ σ a := by
  rw [add_mem_iff, neg_add_cancel_left]
/-
**spectrum.smul_mem_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s in σ (r • a) ↔ s in σ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  simp only [mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]
/-
**spectrum.unit_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a
参数：a : A；r : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `spectrum.smul_mem_smul_iff`：smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} :
 r • s in σ (r • a) ↔ s in σ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
/-
**spectrum.unit_mem_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r in σ (a * b) ↔ ↑r in σ (b * a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Basic.0.spectrum.unit_mem_mul_
comm._abel_1_1`：∀ {A : Type u_1} [inst : Ring A] (x y : A) (h : IsUnit (1 - x * 
y)),   1 + y * (⋯.unit.inv * x) + -(y * x + y * (⋯.unit.inv * (x * (y * x)))…
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) := by
  have h₁ : ∀ x y : A, IsUnit (1 - x * y) → IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    · calc
        (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) =
            1 - y * x + y * (h.unit.inv * (1 - x * y)) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  have := Iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a))
  rw [mul_smul_comm r⁻¹ b a] at this
  simpa only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, ← Units.smul_def,
    IsUnit.smul_sub_iff_sub_inv_smul, smul_mul_assoc]
/-
**spectrum.preimage_units_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：preimage_units_mul_comm (a b : A) : ((↑) : Rˣ -> R) ⁻¹' σ (a * b) = (↑) ⁻¹
' σ (b * a)
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `spectrum.unit_mem_mul_comm`：unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r in
 σ (a * b) ↔ ↑r in σ (b * a)
-/
theorem preimage_units_mul_comm (a b : A) :
    ((↑) : Rˣ → R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) :=
  Set.ext fun _ => unit_mem_mul_comm
/-
**spectrum.setOfPred_isUnit_inter_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：setOfPred_isUnit_inter_mul_comm (a b : A) : {r | IsUnit r} inter σ (a * b)
 = {r | IsUnit r} inter σ (b * a)
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.unit_mem_mul_comm`：unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r in
 σ (a * b) ↔ ↑r in σ (b * a)
-/
theorem setOfPred_isUnit_inter_mul_comm (a b : A) :
    {r | IsUnit r} ∩ σ (a * b) = {r | IsUnit r} ∩ σ (b * a) := by
  ext r
  simpa using fun hr : IsUnit r ↦ unit_mem_mul_comm (r := hr.unit)

@[deprecated (since := "2026-07-09")]
alias setOf_isUnit_inter_mul_comm := setOfPred_isUnit_inter_mul_comm

section Star

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

/-
**spectrum.star_mem_resolventSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：star_mem_resolventSet_iff {r : R} {a : A} : star r in resolventSet R a ↔ r
 in resolventSet R (star a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `IsUnit.star`：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul R] {a : 
R}, IsUnit a → IsUnit (star a)
-/
theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h
/-
**spectrum.map_star** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] [inst_3 : InvolutiveStar R]   [inst_4 : StarRing A] [StarModu
le R A] (a : A), spectrum R (star a) = star (spectrum R a)
参数：a : A；star a；spectrum R a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `spectrum.star_mem_resolventSet_iff`：star_mem_resolventSet_iff {r : R} {a
 : A} : star r in resolventSet R a ↔ r in resolventSet R (star a)
-/
protected theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  simpa only [Set.mem_star, mem_iff, not_iff_not] using! star_mem_resolventSet_iff.symm

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/-
**spectrum.subset_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] 
[SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) : spectrum
 R (a : A) subseteq spectrum R a
参数：a : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
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
theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a :=
  Set.compl_subset_compl.mpr fun _ ↦ IsUnit.map (SubalgebraClass.val s)
/-
**spectrum.singleton_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a)
参数：a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `spectrum.add_mem_iff`：add_mem_iff {a : A} {r s : R} : r + s in σ a ↔ r i
n σ (-↑ₐ s + a)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) :=
  ext fun x => by
    rw [singleton_add, image_add_left, mem_preimage, add_comm, add_mem_iff, map_neg, neg_neg]
/-
**spectrum.add_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r)
参数：a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.singleton_add_eq`：singleton_add_eq (a : A) (r : R) : {r} + σ a 
= σ (↑ₐ r + a)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) :=
  add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r
/-
**spectrum.vadd_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a)
参数：a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `spectrum.singleton_add_eq`：singleton_add_eq (a : A) (r : R) : {r} + σ a 
= σ (↑ₐ r + a)
-/
theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) :=
  singleton_add.symm.trans <| singleton_add_eq a r
/-
**spectrum._root_.resolventSet_neg** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.resolventSet_neg (a : A) : resolventSet R (-a) = -resolventSet R a :=
  Set.ext fun x => by
    simp only [mem_neg, mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]
/-
**spectrum.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：neg_eq (a : A) : -σ a = σ (-a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [inst
_1 : Ring A] [inst_2 : Algebra R A] (a : A),   spectrum R a = (resolventSet R a)
ᶜ
· 使用定理 `Set.compl_neg`：∀ {α : Type u_2} [inst : Neg α] {s : Set α}, -sᶜ = (-s)ᶜ
· 使用定理 `resolventSet_neg`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_
1 : Ring A] [inst_2 : Algebra R A] (a : A),   resolventSet R (-a) = -resolventSe
t R a
-/
theorem neg_eq (a : A) : -σ a = σ (-a) := by
  rw [spectrum, Set.compl_neg, spectrum, resolventSet_neg]
/-
**spectrum.singleton_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a)
参数：a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `spectrum.neg_eq`：neg_eq (a : A) : -σ a = σ (-a)
· 使用定理 `spectrum.singleton_add_eq`：singleton_add_eq (a : A) (r : R) : {r} + σ a 
= σ (↑ₐ r + a)
-/
theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by
  rw [sub_eq_add_neg, neg_eq, singleton_add_eq, sub_eq_add_neg]
/-
**spectrum.sub_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r)
参数：a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `spectrum.neg_eq`：neg_eq (a : A) : -σ a = σ (-a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `spectrum.singleton_sub_eq`：singleton_sub_eq (a : A) (r : R) : {r} - σ a 
= σ (↑ₐ r - a)
-/
theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

end ScalarRing

section ScalarSemifield

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

@[simp]
/-
**spectrum.inv** 是 Mathlib 中的一个引理，位于命名空间 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv₀_mem_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (a : A) ↔ r ∈ spectrum R (↑a⁻¹ : A) := by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [inv_mem_iff]
/-
**spectrum.inv** 是 Mathlib 中的一个引理，位于命名空间 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

end ScalarSemifield

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `Nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
/-
**spectrum.zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：zero_eq [Nontrivial A] : σ (0 : A) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [inst
_1 : Ring A] [inst_2 : Algebra R A] (a : A),   spectrum R a = (resolventSet R a)
ᶜ
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用引理 `IsUnit.smul`：IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommC
lass G M M] [IsScalarTower G M M] {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m
)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Without the assumption `Nontrivial A`, then `0 : A` would be invertible.
-/
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  rw [spectrum, Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
/-
**spectrum.scalar_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k}
参数：k : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `spectrum.singleton_add_eq`：singleton_add_eq (a : A) (r : R) : {r} + σ a 
= σ (↑ₐ r + a)
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `Set.singleton_add_singleton`：∀ {α : Type u_2} [inst : Add α] {a b : α}, 
{a} + {b} = {a + b}
-/
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  rw [← add_zero (↑ₐ k), ← singleton_add_eq, zero_eq, Set.singleton_add_singleton, add_zero]

@[simp]
/-
**spectrum.one_eq** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：one_eq [Nontrivial A] : σ (1 : A) = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `spectrum.scalar_eq`：scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k}
-/
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := scalar_eq 1

/-- the assumption `(σ a).Nonempty` is necessary and cannot be removed without
further conditions on the algebra `A` and scalar field `𝕜`. -/
/-
**spectrum.smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) : σ (k •
 a) = k • σ a
参数：k : 𝕜；a : A；ha : (σ a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.unit_smul_eq_smul`：unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • 
a) = r • σ a

--- 原说明 ---
the assumption `(σ a).Nonempty` is necessary and cannot be removed without
further conditions on the algebra `A` and scalar field `𝕜`.
-/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact unit_smul_eq_smul a (Units.mk0 k h)
/-
**spectrum.nonzero_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0}
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `spectrum.unit_mem_mul_comm`：unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r in
 σ (a * b) ↔ ↑r in σ (b * a)
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
-/
theorem nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) ∈ _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_ne⟩
/-
**spectrum.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {𝕜 : Type u} {A : Type v} [inst : Field 𝕜] [inst_1 : Ring A] [inst_2 : A
lgebra 𝕜 A] (a : Aˣ),   (spectrum 𝕜 ↑a)⁻¹ = spectrum 𝕜 ↑a⁻¹
参数：a : Aˣ；spectrum 𝕜 ↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  ext
  simp

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [FunLike F A B] [AlgHomClass F R A B]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/-
**AlgHom.mem_resolventSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r in resolventSet R a)
 : r in resolventSet R ((φ : A -> B) a)
参数：φ : F；h : r in resolventSet R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
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
theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using! h.map φ
/-
**AlgHom.spectrum_apply_subset** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A -> B) a) subseteq σ a
参数：φ : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AlgHom.mem_resolventSet_apply`：mem_resolventSet_apply (φ : F) {a : A} {r
 : R} (h : r in resolventSet R a) : r in resolventSet R ((φ : A -> B) a)
-/
theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a := fun _ =>
  mt (mem_resolventSet_apply φ)

end CommSemiring

section CommRing

variable {F R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable [FunLike F A R] [AlgHomClass F R A R]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

/-
**AlgHom.apply_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a in σ a
参数：φ : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `coe_subset_nonunits`：coe_subset_nonunits [Semiring α] {I : Ideal α} (h :
 I != ⊤) : (I : Set α) subseteq nonunits α
· 使用定理 `RingHom.ker_ne_top`：ker_ne_top [Nontrivial S] (f : F) : ker f != ⊤
-/
theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ RingHom.ker (φ : A →+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A →+* R)) h]

end CommRing

end AlgHom

@[simp]
/-
**AlgEquiv.spectrum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] 
[Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a
 : A) : spectrum R (f a) = spectrum R a
参数：f : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `AlgHom.spectrum_apply_subset`：spectrum_apply_subset (φ : F) (a : A) : σ 
((φ : A -> B) a) subseteq σ a
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.coe_coe_symm_apply_coe_apply`：coe_coe_symm_apply_coe_apply {F :
 Type*} [EquivLike F A₁ A₂] [AlgEquivClass F R A₁ A₂] (f : F) (x : A₁) : (AlgEqu
ivClass.toAlgEquiv f).symm …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a :=
  Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) <| by
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (AlgEquivClass.toAlgEquiv f : A ≃ₐ[R] B).symm (f a)

section ConjugateUnits

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Conjugation by a unit preserves the spectrum, inverse on right. -/
@[simp]
/-
**spectrum.units_conjugate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum.units_conjugate {a : A} {u : Aˣ} : spectrum R (u * a * u⁻¹) = spe
ctrum R a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Algebra.right_comm`：right_comm (x : A) (r : R) (y : A) : x * algebraMap 
R A r * y = x * y * algebraMap R A r
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Conjugation by a unit preserves the spectrum, inverse on right.
-/
lemma spectrum.units_conjugate {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices ∀ (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) ⊆ spectrum R b by
    refine le_antisymm (this a u) ?_
    apply le_of_eq_of_le ?_ <| this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose hμ
  simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ |>.mul u⁻¹.isUnit

/-- Conjugation by a unit preserves the spectrum, inverse on left. -/
@[simp]
/-
**spectrum.units_conjugate'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum.units_conjugate' {a : A} {u : Aˣ} : spectrum R (u⁻¹ * a * u) = sp
ectrum R a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `spectrum.units_conjugate`：spectrum.units_conjugate {a : A} {u : Aˣ} : sp
ectrum R (u * a * u⁻¹) = spectrum R a

--- 原说明 ---
Conjugation by a unit preserves the spectrum, inverse on left.
-/
lemma spectrum.units_conjugate' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by
  simpa using spectrum.units_conjugate (u := u⁻¹)

end ConjugateUnits

