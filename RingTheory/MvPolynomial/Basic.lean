/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.DFinsupp.Small
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrictTotalDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrictDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative semiring of characteristic `p` has
  characteristic `p`, and similarly for `CharZero`.
* `basisMonomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/

@[expose] public section


noncomputable section

open Set LinearMap Module Submodule

universe u v

variable (σ : Type u) (R : Type v) [CommSemiring R] (p m : ℕ)

namespace MvPolynomial

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ R : Type*} [CommSemiring R] [Small.{u} R] [Small.{u} σ] :
    Small.{u} (MvPolynomial σ R) := small_map AddMonoidAlgebra.coeffEquiv

section CharP

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharP R p] : CharP (MvPolynomial σ R) p where
  cast_eq_zero_iff n := by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

end CharP

section CharZero

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero R] : CharZero (MvPolynomial σ R) where
  cast_injective x y hxy := by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

end CharZero

section ExpChar

variable [ExpChar R p]

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ExpChar (MvPolynomial σ R) p := by
  cases ‹ExpChar R p›; exacts [ExpChar.zero, ExpChar.prime ‹_›]

end ExpChar

section Homomorphism

/-
**MvPolynomial.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomi
al σ R) (f : R ->+* S) : AddMonoidAlgebra.map f p = map f p
参数：p : MvPolynomial σ R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem map_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
    (f : R →+* S) : AddMonoidAlgebra.map f p = map f p := rfl

@[deprecated (since := "2026-06-18")] alias mapRange_eq_map := map_eq_map

end Homomorphism

section Degree

variable {σ}

/-- The submodule of polynomials that are sum of monomials in the set `s`. -/
/-
**MvPolynomial.restrictSupport** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport (s : Set (σ ->₀ Nat)) : Submodule R (MvPolynomial σ R)
参数：s : Set (σ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of polynomials that are sum of monomials in the set `s`.
-/
def restrictSupport (s : Set (σ →₀ ℕ)) : Submodule R (MvPolynomial σ R) :=
  AddMonoidAlgebra.supported R R s

/-- `restrictSupport R s` has a canonical `R`-basis indexed by `s`. -/
/-
**MvPolynomial.basisRestrictSupport** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：basisRestrictSupport (s : Set (σ ->₀ Nat)) : Basis s R (restrictSupport R 
s) where repr
参数：s : Set (σ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`restrictSupport R s` has a canonical `R`-basis indexed by `s`.
-/
def basisRestrictSupport (s : Set (σ →₀ ℕ)) : Basis s R (restrictSupport R s) where
  repr := AddMonoidAlgebra.supportedEquivFinsupp s
/-
**MvPolynomial.restrictSupport_mono** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport_mono {s t : Set (σ ->₀ Nat)} (h : s subseteq t) : restrict
Support R s <= restrictSupport R t
参数：σ ->₀ Nat；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.supported_mono`：∀ {R : Type u_1} {S : Type u_2} {M : Ty
pe u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R S]  
 {s t : Set M}, s ⊆ t…
-/
theorem restrictSupport_mono {s t : Set (σ →₀ ℕ)} (h : s ⊆ t) :
    restrictSupport R s ≤ restrictSupport R t := AddMonoidAlgebra.supported_mono h
/-
**MvPolynomial.restrictSupport_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport_eq_span (s : Set (σ ->₀ Nat)) : restrictSupport R s = .spa
n _ ((monomial · 1) '' s)
参数：s : Set (σ ->₀ Nat)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.supported_eq_span_single`：∀ (R : Type u_1) {M : Type u_
3} [inst : Semiring R] (s : Set M),   AddMonoidAlgebra.supported R R s = Submodu
le.span R ((fun m => AddMonoidA…
-/
lemma restrictSupport_eq_span (s : Set (σ →₀ ℕ)) :
    restrictSupport R s = .span _ ((monomial · 1) '' s) :=
  AddMonoidAlgebra.supported_eq_span_single ..
/-
**MvPolynomial.mem_restrictSupport_iff** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_restrictSupport_iff {s : Set (σ ->₀ Nat)} {r : MvPolynomial σ R} : r i
n restrictSupport R s ↔ ↑r.support subseteq s
参数：σ ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_restrictSupport_iff {s : Set (σ →₀ ℕ)} {r : MvPolynomial σ R} :
    r ∈ restrictSupport R s ↔ ↑r.support ⊆ s := .rfl

@[simp]
/-
**MvPolynomial.monomial_mem_restrictSupport** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynom
ial`。
形式化陈述：monomial_mem_restrictSupport {s : Set (σ ->₀ Nat)} {m} {r : R} : monomial 
m r in restrictSupport R s ↔ m in s ∨ r = 0
参数：σ ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MvPolynomial.support_monomial`：support_monomial [h : Decidable (a = 0)] 
: (monomial s a).support = if a = 0 then ∅ else {s}
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma monomial_mem_restrictSupport {s : Set (σ →₀ ℕ)} {m} {r : R} :
    monomial m r ∈ restrictSupport R s ↔ m ∈ s ∨ r = 0 := by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

open scoped Pointwise in
/-
**MvPolynomial.restrictSupport_add** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport_add (s t : Set (σ ->₀ Nat)) : restrictSupport R (s + t) = 
restrictSupport R s * restrictSupport R t
参数：s t : Set (σ ->₀ Nat)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.restrictSupport_eq_span`：restrictSupport_eq_span (s : Set (
σ ->₀ Nat)) : restrictSupport R s = .span _ ((monomial · 1) '' s)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.add_subset_iff`：∀ {α : Type u_2} [inst : Add α] {s t u : Set α}, s +
 t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x + y ∈ u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma restrictSupport_add (s t : Set (σ →₀ ℕ)) :
    restrictSupport R (s + t) = restrictSupport R s * restrictSupport R t := by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, restrictSupport_eq_span, Submodule.span_mul_span,
      Submodule.span_le, Set.mul_subset_iff]
    simp +contextual [Set.add_mem_add]

open scoped Pointwise in
/-
**MvPolynomial.restrictSupport_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {σ : Type u} (R : Type v) [inst : CommSemiring R], MvPolynomial.restrict
Support R 0 = 1
参数：R : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.restrictSupport_eq_span`：restrictSupport_eq_span (s : Set (
σ ->₀ Nat)) : restrictSupport R s = .span _ ((monomial · 1) '' s)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `AddMonoidAlgebra.smul_single`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {A : Type u_8} [inst_1 : SMulZeroClass A R] (a : A) (m : M) (r : R),  
 a • AddMonoidAlge…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma restrictSupport_zero : restrictSupport R (0 : Set (σ →₀ ℕ)) = 1 := by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simp only [monomial, AddMonoidAlgebra.lsingle_apply, zero_subset, mem_preimage,
      ← AddMonoidAlgebra.one_def, SetLike.mem_coe, Submodule.mem_one, algebraMap_eq]
    exact ⟨1, by simp⟩
  · rintro _ ⟨x, rfl⟩
    simp [mem_restrictSupport_iff, subset_def, coeff, AddMonoidAlgebra.one_def,
      Finsupp.single_apply]

@[simp]
/-
**MvPolynomial.restrictSupport_univ** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport_univ : restrictSupport R (.univ : Set (σ ->₀ Nat)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrictSupport_univ : restrictSupport R (.univ : Set (σ →₀ ℕ)) = ⊤ := by
  ext; simp [mem_restrictSupport_iff]

open scoped Pointwise in
/-
**MvPolynomial.restrictSupport_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupport_nsmul (n : Nat) (s : Set (σ ->₀ Nat)) : restrictSupport R 
(n • s) = restrictSupport R s ^ n
参数：n : Nat；s : Set (σ ->₀ Nat)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `MvPolynomial.restrictSupport_zero`：∀ {σ : Type u} (R : Type v) [inst : C
ommSemiring R], MvPolynomial.restrictSupport R 0 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `MvPolynomial.restrictSupport_add`：restrictSupport_add (s t : Set (σ ->₀ 
Nat)) : restrictSupport R (s + t) = restrictSupport R s * restrictSupport R t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
lemma restrictSupport_nsmul (n : ℕ) (s : Set (σ →₀ ℕ)) :
    restrictSupport R (n • s) = restrictSupport R s ^ n := by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

/-- The ideal defined by `restrictSupport R s` when `s` is an upper set. -/
/-
**MvPolynomial.restrictSupportIdeal** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：restrictSupportIdeal (s : Set (σ ->₀ Nat)) (hs : IsUpperSet s) : Ideal (Mv
Polynomial σ R) where __
参数：s : Set (σ ->₀ Nat)；hs : IsUpperSet s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal defined by `restrictSupport R s` when `s` is an upper set.
-/
def restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs : IsUpperSet s) :
    Ideal (MvPolynomial σ R) where
  __ := restrictSupport R s
  smul_mem' x y hy m (hm : m ∈ (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j ∈ y.support by aesop))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MvPolynomial.restrictScalars_restrictSupportIdeal** 是 Mathlib 中的一个引理，位于命名空间 `M
vPolynomial`。
形式化陈述：restrictScalars_restrictSupportIdeal (s : Set (σ ->₀ Nat)) (hs) : (restric
tSupportIdeal (R
参数：s : Set (σ ->₀ Nat)；hs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma restrictScalars_restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs) :
    (restrictSupportIdeal (R := R) s hs).restrictScalars R = restrictSupport R s :=
  rfl

variable (σ)

/-- The submodule of polynomials of total degree less than or equal to `m`. -/
/-
**MvPolynomial.restrictTotalDegree** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：restrictTotalDegree (m : Nat) : Submodule R (MvPolynomial σ R)
参数：m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of polynomials of total degree less than or equal to `m`.
-/
def restrictTotalDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | (n.sum fun _ e => e) ≤ m }

/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`. -/
/-
**MvPolynomial.restrictDegree** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：restrictDegree (m : Nat) : Submodule R (MvPolynomial σ R)
参数：m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of polynomials such that the degree with respect to each individua
l variable is
less than or equal to `m`.
-/
def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ m }

variable {R}
/-
**MvPolynomial.mem_restrictTotalDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_restrictTotalDegree (p : MvPolynomial σ R) : p in restrictTotalDegree 
σ R m ↔ p.totalDegree <= m
参数：p : MvPolynomial σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p ∈ restrictTotalDegree σ R m ↔ p.totalDegree ≤ m := by
  rw [totalDegree, Finset.sup_le_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.mem_restrictDegree** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_restrictDegree (p : MvPolynomial σ R) (n : Nat) : p in restrictDegree 
σ R n ↔ forall s in p.support, forall i, (s : σ ->₀ Nat) i <= n
参数：p : MvPolynomial σ R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.restrictDegree.eq_1`：∀ (σ : Type u) (R : Type v) [inst : Co
mmSemiring R] (m : ℕ),   MvPolynomial.restrictDegree σ R m = MvPolynomial.restri
ctSupport R {n | ∀ (i …
· 使用定理 `MvPolynomial.restrictSupport.eq_1`：∀ {σ : Type u} (R : Type v) [inst : C
ommSemiring R] (s : Set (σ →₀ ℕ)),   MvPolynomial.restrictSupport R s = AddMonoi
dAlgebra.supported R R …
· 使用定理 `AddMonoidAlgebra.mem_supported`：∀ {R : Type u_1} {S : Type u_2} {M : Typ
e u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R S]   
{s : Set M} {x : Add…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ n := by
  rw [restrictDegree, restrictSupport, AddMonoidAlgebra.mem_supported]
  rfl
/-
**MvPolynomial.mem_restrictDegree_iff_sup** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : Nat
) : p in restrictDegree σ R n ↔ forall i, p.degrees.count i <= n
参数：p : MvPolynomial σ R；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `MvPolynomial.degrees_def`：degrees_def [DecidableEq σ] (p : MvPolynomial 
σ R) : p.degrees = p.support.sup fun s : σ ->₀ Nat => Finsupp.toMultiset s
· 使用定理 `Multiset.count_finset_sup`：count_finset_sup [DecidableEq β] (s : Finset 
α) (f : α -> Multiset β) (b : β) : count b (s.sup f) = s.sup fun a => count b (f
 a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.count_toMultiset`：count_toMultiset [DecidableEq α] (f : α ->₀ Na
t) (a : α) : (toMultiset f).count a = f a
-/
theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degrees.count i ≤ n := by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

variable (R)
/-
**MvPolynomial.restrictTotalDegree_le_restrictDegree** 是 Mathlib 中的一个定理，位于命名空间 `
MvPolynomial`。
形式化陈述：restrictTotalDegree_le_restrictDegree (m : Nat) : restrictTotalDegree σ R 
m <= restrictDegree σ R m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPolynomial.mem_restrictDegree`：mem_restrictDegree (p : MvPolynomial σ 
R) (n : Nat) : p in restrictDegree σ R n ↔ forall s in p.support, forall i, (s :
 σ ->₀ Nat) i <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MvPolynomial.degreeOf_le_iff`：degreeOf_le_iff {n : σ} {f : MvPolynomial 
σ R} {d : Nat} : degreeOf n f <= d ↔ forall m in support f, m n <= d
· 使用引理 `MvPolynomial.degreeOf_le_totalDegree`：degreeOf_le_totalDegree (f : MvPol
ynomial σ R) (i : σ) : f.degreeOf i <= f.totalDegree
· 使用定理 `MvPolynomial.mem_restrictTotalDegree`：mem_restrictTotalDegree (p : MvPol
ynomial σ R) : p in restrictTotalDegree σ R m ↔ p.totalDegree <= m
-/
theorem restrictTotalDegree_le_restrictDegree (m : ℕ) :
    restrictTotalDegree σ R m ≤ restrictDegree σ R m :=
  fun p hp ↦ (mem_restrictDegree _ _ _).mpr fun s hs i ↦ (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

/-- The monomials form a basis on `MvPolynomial σ R`. -/
/-
**MvPolynomial.basisMonomials** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：basisMonomials : Basis (σ ->₀ Nat) R (MvPolynomial σ R) where repr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monomials form a basis on `MvPolynomial σ R`.
-/
def basisMonomials : Basis (σ →₀ ℕ) R (MvPolynomial σ R) where
  repr := AddMonoidAlgebra.coeffLinearEquiv _

@[simp]
/-
**MvPolynomial.coe_basisMonomials** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_basisMonomials : (basisMonomials σ R : (σ ->₀ Nat) -> MvPolynomial σ R
) = fun s => monomial s 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_basisMonomials :
    (basisMonomials σ R : (σ →₀ ℕ) → MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl

/-- The `R`-module `MvPolynomial σ R` is free. -/
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-module `MvPolynomial σ R` is free.
-/
instance : Module.Free R (MvPolynomial σ R) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials σ R)
/-
**MvPolynomial.linearIndependent_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：linearIndependent_X : LinearIndependent R (X : σ -> MvPolynomial σ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Finsupp.single_left_injective`：single_left_injective (h : b != 0) : Func
tion.Injective fun a : α => single a b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem linearIndependent_X : LinearIndependent R (X : σ → MvPolynomial σ R) :=
  (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)
/-
**MvPolynomial.finite_setOfPred_bounded** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma finite_setOfPred_bounded (α) [Finite α] (n : ℕ) :
    Finite {f : α →₀ ℕ | ∀ a, f a ≤ n} :=
  ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite σ] (N : ℕ) : Module.Finite R (restrictDegree σ R N) :=
  have := finite_setOfPred_bounded σ N
  Module.Finite.of_basis (basisRestrictSupport R _)
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite σ] (N : ℕ) : Module.Finite R (restrictTotalDegree σ R N) :=
  have := finite_setOfPred_bounded σ N
  have : Finite {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ N} := by
    rw [Set.finite_coe_iff] at this ⊢
    exact this.subset fun n hn i ↦ (eq_or_ne (n i) 0).elim
      (fun h ↦ h.trans_le N.zero_le) fun h ↦
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) <| Finsupp.mem_support_iff.mpr h).trans hn
  Module.Finite.of_basis (basisRestrictSupport R _)

end Degree

end MvPolynomial

