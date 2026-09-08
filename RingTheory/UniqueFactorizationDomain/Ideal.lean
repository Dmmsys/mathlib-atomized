/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Unique factorization and ascending chain condition on ideals

## Main results
* `Ideal.setOfPred_isPrincipal_wellFoundedOn_gt`,
  `WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt`
  in a domain, well-foundedness of the strict version of ∣ is equivalent to the ascending
  chain condition on principal ideals.
-/

public section

variable {α : Type*}

open UniqueFactorizationMonoid in
/-- Every non-zero prime ideal in a unique factorization domain contains a prime element. -/
/-
**Ideal.IsPrime.exists_mem_prime_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsPrime.exists_mem_prime_of_ne_bot {R : Type*} [CommSemiring R] [Uni
queFactorizationMonoid R] {I : Ideal R} (hI₂ : I.IsPrime) (hI : I != ⊥) : exists
 x in I, Prime x
参数：hI₂ : I.IsPrime；hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.multiset_prod_mem_iff_exists_mem`：∀ {R : Type u} [inst : C
ommSemiring R] {I : Ideal R}, I.IsPrime → ∀ (s : Multiset R), s.prod ∈ I ↔ ∃ p ∈
 s, p ∈ I
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x

--- 原说明 ---
Every non-zero prime ideal in a unique factorization domain contains a prime ele
ment.
-/
theorem Ideal.IsPrime.exists_mem_prime_of_ne_bot {R : Type*} [CommSemiring R]
    [UniqueFactorizationMonoid R] {I : Ideal R} (hI₂ : I.IsPrime) (hI : I ≠ ⊥) :
    ∃ x ∈ I, Prime x := by
  obtain ⟨a : R, ha₁ : a ∈ I, ha₂ : a ≠ 0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  replace ha₁ : (factors a).prod ∈ I := by
    obtain ⟨u : Rˣ, hu : (factors a).prod * u = a⟩ := factors_prod ha₂
    rwa [← hu, mul_unit_mem_iff_mem _ u.isUnit] at ha₁
  obtain ⟨p : R, hp₁ : p ∈ factors a, hp₂ : p ∈ I⟩ :=
    (hI₂.multiset_prod_mem_iff_exists_mem <| factors a).1 ha₁
  exact ⟨p, hp₂, prime_of_factor p hp₁⟩

section Ideal

/-- The ascending chain condition on principal ideals holds in a `WfDvdMonoid` domain. -/
/-
**Ideal.setOfPred_isPrincipal_wellFoundedOn_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.setOfPred_isPrincipal_wellFoundedOn_gt [CommSemiring α] [WfDvdMonoid
 α] [IsDomain α] : {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.wellFoundedOn_image`：wellFoundedOn_image {s : Set β} : (f '' s).Well
FoundedOn r ↔ s.WellFoundedOn (r on f)
· 使用定理 `Set.wellFoundedOn_univ`：wellFoundedOn_univ : (univ : Set α).WellFoundedO
n r ↔ WellFounded r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_lt_span_singleton`：span_singleton_lt_span_singleton
 [IsDomain α] {x y : α} : span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y
 x
· 使用定理 `wellFounded_dvdNotUnit`：wellFounded_dvdNotUnit {α : Type*} [CommMonoidWi
thZero α] [h : WfDvdMonoid α] : WellFounded (DvdNotUnit (α

--- 原说明 ---
The ascending chain condition on principal ideals holds in a `WfDvdMonoid` domai
n.
-/
lemma Ideal.setOfPred_isPrincipal_wellFoundedOn_gt [CommSemiring α] [WfDvdMonoid α] [IsDomain α] :
    {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·) := by
  have : {I : Ideal α | I.IsPrincipal} = ((fun a ↦ Ideal.span {a}) '' Set.univ) := by
    ext
    simp [Submodule.isPrincipal_iff, eq_comm]
  rw [this, Set.wellFoundedOn_image, Set.wellFoundedOn_univ]
  convert! wellFounded_dvdNotUnit (α := α)
  ext
  exact Ideal.span_singleton_lt_span_singleton

@[deprecated (since := "2026-07-09")]
alias Ideal.setOf_isPrincipal_wellFoundedOn_gt := Ideal.setOfPred_isPrincipal_wellFoundedOn_gt

/-- The ascending chain condition on principal ideals in a domain is sufficient to prove that
the domain is `WfDvdMonoid`. -/
/-
**WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt [CommSemiring α] [Is
Domain α] (h : {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·)) : WfDvdMonoi
d α
参数：h : {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.span_singleton_lt_span_singleton`：span_singleton_lt_span_singleton
 [IsDomain α] {x y : α} : span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y
 x
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)

--- 原说明 ---
The ascending chain condition on principal ideals in a domain is sufficient to p
rove that
the domain is `WfDvdMonoid`.
-/
lemma WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt [CommSemiring α] [IsDomain α]
    (h : {I : Ideal α | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    WfDvdMonoid α := by
  have : WellFounded (α := {I : Ideal α // I.IsPrincipal}) (· > ·) := h
  constructor
  convert! InvImage.wf (fun a => ⟨Ideal.span ({ a } : Set α), _, rfl⟩) this
  ext
  exact Ideal.span_singleton_lt_span_singleton.symm

@[deprecated (since := "2026-07-09")]
alias WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt :=
  WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt

end Ideal

