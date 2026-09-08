/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Polynomials supported by a set of variables

This file contains the definition and lemmas about `MvPolynomial.supported`.

## Main definitions

* `MvPolynomial.supported` : Given a set `s : Set σ`, `supported R s` is the subalgebra of
  `MvPolynomial σ R` consisting of polynomials whose set of variables is contained in `s`.
  This subalgebra is isomorphic to `MvPolynomial s R`.

## Tags
variables, polynomial, vars
-/

@[expose] public section


universe u v w

namespace MvPolynomial

variable {σ : Type*} {R : Type u}

section CommSemiring

variable [CommSemiring R] {p : MvPolynomial σ R}

variable (R) in
/-- The set of polynomials whose variables are contained in `s` as a `Subalgebra` over `R`. -/
/-
**MvPolynomial.supported** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：supported (s : Set σ) : Subalgebra R (MvPolynomial σ R)
参数：s : Set σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of polynomials whose variables are contained in `s` as a `Subalgebra` ov
er `R`.
-/
noncomputable def supported (s : Set σ) : Subalgebra R (MvPolynomial σ R) :=
  Algebra.adjoin R (X '' s)

open Algebra

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.supported_eq_range_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：supported_eq_range_rename (s : Set σ) : supported R s = (rename ((↑) : s -
> σ)).range
参数：s : Set σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.supported.eq_1`：∀ {σ : Type u_1} (R : Type u) [inst : CommS
emiring R] (s : Set σ),   MvPolynomial.supported R s = Algebra.adjoin R (MvPolyn
omial.X '' s)
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Algebra.adjoin_range_eq_range_aeval`：∀ (R : Type u) {S₁ : Type v} {σ : T
ype u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R 
S₁]   (f : σ → S₁), Algeb…
· 使用引理 `MvPolynomial.rename_eq_aeval`：rename_eq_aeval (f : σ -> τ) : rename (R
-/
theorem supported_eq_range_rename (s : Set σ) : supported R s = (rename ((↑) : s → σ)).range := by
  rw [supported, Set.image_eq_range, adjoin_range_eq_range_aeval, rename_eq_aeval]
  congr

/-- The isomorphism between the subalgebra of polynomials supported by `s` and
`MvPolynomial s R`. -/
/-
**MvPolynomial.supportedEquivMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomia
l`。
形式化陈述：supportedEquivMvPolynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial 
s R
参数：s : Set σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range

--- 原说明 ---
The isomorphism between the subalgebra of polynomials supported by `s` and
`MvPolynomial s R`.
-/
noncomputable def supportedEquivMvPolynomial (s : Set σ) : supported R s ≃ₐ[R] MvPolynomial s R :=
  (Subalgebra.equivOfEq _ _ (supported_eq_range_rename s)).trans
    (AlgEquiv.ofInjective (rename ((↑) : s → σ)) (rename_injective _ Subtype.val_injective)).symm

@[simp]
/-
**MvPolynomial.supportedEquivMvPolynomial_symm_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：supportedEquivMvPolynomial_symm_C (s : Set σ) (x : R) : (supportedEquivMvP
olynomial s).symm (C x) = algebraMap R (supported R s) x
参数：s : Set σ；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `Subalgebra.equivOfEq_apply`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S T : Subalgebra R A)   (h
 : S = T) (x : ↥…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supportedEquivMvPolynomial_symm_C (s : Set σ) (x : R) :
    (supportedEquivMvPolynomial s).symm (C x) = algebraMap R (supported R s) x := by
  ext1
  simp [supportedEquivMvPolynomial, MvPolynomial.algebraMap_eq]

@[simp]
/-
**MvPolynomial.supportedEquivMvPolynomial_symm_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：supportedEquivMvPolynomial_symm_X (s : Set σ) (i : s) : (↑((supportedEquiv
MvPolynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) = X ↑i
参数：s : Set σ；i : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Subalgebra.equivOfEq_apply`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S T : Subalgebra R A)   (h
 : S = T) (x : ↥…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supportedEquivMvPolynomial_symm_X (s : Set σ) (i : s) :
    (↑((supportedEquivMvPolynomial s).symm (X i : MvPolynomial s R)) : MvPolynomial σ R) =
      X ↑i := by
  simp [supportedEquivMvPolynomial]

variable {s t : Set σ}
/-
**MvPolynomial.mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_supported : p in supported R s ↔ ↑p.vars subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `MvPolynomial.vars_rename`：vars_rename [DecidableEq τ] (f : σ -> τ) (φ : 
MvPolynomial σ R) : (rename f φ).vars subseteq φ.vars.image f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `MvPolynomial.exists_rename_eq_of_vars_subset_range`：exists_rename_eq_of_
vars_subset_range (p : MvPolynomial σ R) (f : τ -> σ) (hfi : Injective f) (hf : 
↑p.vars subseteq Set.range f) : exists q…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem mem_supported : p ∈ supported R s ↔ ↑p.vars ⊆ s := by
  classical
  rw [supported_eq_range_rename, AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective (by simpa)
/-
**MvPolynomial.supported_eq_vars_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：supported_eq_vars_subset : (supported R s : Set (MvPolynomial σ R)) = { p 
| ↑p.vars subseteq s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `MvPolynomial.mem_supported`：mem_supported : p in supported R s ↔ ↑p.vars
 subseteq s
-/
theorem supported_eq_vars_subset : (supported R s : Set (MvPolynomial σ R)) = { p | ↑p.vars ⊆ s } :=
  Set.ext fun _ ↦ mem_supported

@[simp]
/-
**MvPolynomial.mem_supported_vars** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_supported_vars (p : MvPolynomial σ R) : p in supported R (↑p.vars : Se
t σ)
参数：p : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_supported`：mem_supported : p in supported R s ↔ ↑p.vars
 subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mem_supported_vars (p : MvPolynomial σ R) : p ∈ supported R (↑p.vars : Set σ) := by
  rw [mem_supported]

variable (s)
/-
**MvPolynomial.supported_eq_adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：supported_eq_adjoin_X : supported R s = Algebra.adjoin R (X '' s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem supported_eq_adjoin_X : supported R s = Algebra.adjoin R (X '' s) := rfl

@[simp]
/-
**MvPolynomial.supported_univ** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：supported_univ : supported R (Set.univ : Set σ) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem supported_univ : supported R (Set.univ : Set σ) = ⊤ := by
  simp [Algebra.eq_top_iff, mem_supported]

@[simp]
/-
**MvPolynomial.supported_empty** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：supported_empty : supported R (∅ : Set σ) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Algebra.adjoin_empty`：adjoin_empty : adjoin R (∅ : Set A) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supported_empty : supported R (∅ : Set σ) = ⊥ := by simp [supported_eq_adjoin_X]

variable {s}
/-
**MvPolynomial.supported_mono** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：supported_mono (st : s subseteq t) : supported R s <= supported R t
参数：st : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem supported_mono (st : s ⊆ t) : supported R s ≤ supported R t :=
  Algebra.adjoin_mono (Set.image_mono st)

@[simp]
/-
**MvPolynomial.X_mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mem_supported [Nontrivial R] {i : σ} : X i in supported R s ↔ i in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.vars_X`：vars_X [Nontrivial R] : (X n : MvPolynomial σ R).va
rs = {n}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem X_mem_supported [Nontrivial R] {i : σ} : X i ∈ supported R s ↔ i ∈ s := by
  simp [mem_supported]

@[simp]
/-
**MvPolynomial.supported_le_supported_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomia
l`。
形式化陈述：supported_le_supported_iff [Nontrivial R] : supported R s <= supported R t
 ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPolynomial.supported_mono`：supported_mono (st : s subseteq t) : suppor
ted R s <= supported R t
-/
theorem supported_le_supported_iff [Nontrivial R] : supported R s ≤ supported R t ↔ s ⊆ t := by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact supported_mono
/-
**MvPolynomial.supported_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：supported_strictMono [Nontrivial R] : StrictMono (supported R : Set σ -> S
ubalgebra R (MvPolynomial σ R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MvPolynomial.supported_le_supported_iff`：supported_le_supported_iff [Non
trivial R] : supported R s <= supported R t ↔ s subseteq t
-/
theorem supported_strictMono [Nontrivial R] :
    StrictMono (supported R : Set σ → Subalgebra R (MvPolynomial σ R)) :=
  strictMono_of_le_iff_le fun _ _ ↦ supported_le_supported_iff.symm
/-
**MvPolynomial.exists_restrict_to_vars** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ Int} 
(hF : ↑F.vars subseteq s) : exists f : (s -> R) -> R, forall x : σ -> R, f (x ∘ 
(↑) : s -> R) = aeval x F
参数：R : Type*；hF : ↑F.vars subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.mem_range`：mem_range (φ : A ->ₐ[R] B) {y : B} : y in φ.range ↔ ex
ists x, φ x = y
· 使用定理 `MvPolynomial.supported_eq_range_rename`：supported_eq_range_rename (s : S
et σ) : supported R s = (rename ((↑) : s -> σ)).range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.mem_supported`：mem_supported : p in supported R s ↔ ↑p.vars
 subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_restrict_to_vars (R : Type*) [CommRing R] {F : MvPolynomial σ ℤ}
    (hF : ↑F.vars ⊆ s) : ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ (↑) : s → R) = aeval x F := by
  rw [← mem_supported, supported_eq_range_rename, AlgHom.mem_range] at hF
  obtain ⟨F', hF'⟩ := hF
  use fun z ↦ aeval z F'
  intro x
  simp only [← hF', aeval_rename]

end CommSemiring

end MvPolynomial

