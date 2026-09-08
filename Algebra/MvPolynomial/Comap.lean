/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# `comap` operation on `MvPolynomial`

This file defines the `comap` function on `MvPolynomial`.

`MvPolynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

/-- Given an algebra hom `f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
/-
**MvPolynomial.comap** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：comap (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) : (τ -> R) -> σ -> R
参数：f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an algebra hom `f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R :=
  fun x i => aeval x (f (X i))

@[simp]
/-
**MvPolynomial.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_apply (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) (x : τ -> R) (i
 : σ) : comap f x i = aeval x (f (X i))
参数：f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R；x : τ -> R；i : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    comap f x i = aeval x (f (X i)) :=
  rfl

@[simp]
/-
**MvPolynomial.comap_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_id_apply (x : σ -> R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x
参数：x : σ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_id_apply (x : σ → R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  simp only [comap, AlgHom.id_apply, aeval_X]

variable (σ R)
/-
**MvPolynomial.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.comap_id_apply`：comap_id_apply (x : σ -> R) : comap (AlgHom
.id R (MvPolynomial σ R)) x = x
-/
theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  exact comap_id_apply x

variable {σ R}
/-
**MvPolynomial.comap_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_comp_apply (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) (g : MvPol
ynomial τ R ->ₐ[R] MvPolynomial υ R) (x : υ -> R) : comap (g.comp f) x = comap f
 (comap g x)
参数：f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R；g : MvPolynomial τ R ->ₐ[R] MvPo
lynomial υ R；x : υ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `MvPolynomial.aeval_unique`：aeval_unique (φ : MvPolynomial σ R ->ₐ[R] S₁)
 : φ = aeval (φ ∘ X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_eval₂Hom`：map_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁
) (g : σ -> S₁) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = e
val₂Hom (φ.comp…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
-/
theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) (x : υ → R) :
    comap (g.comp f) x = comap f (comap g x) := by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
    ext r
    apply aeval_C
/-
**MvPolynomial.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_comp (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) (g : MvPolynomia
l τ R ->ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g
参数：f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R；g : MvPolynomial τ R ->ₐ[R] MvPo
lynomial υ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.comap_comp_apply`：comap_comp_apply (f : MvPolynomial σ R ->
ₐ[R] MvPolynomial τ R) (g : MvPolynomial τ R ->ₐ[R] MvPolynomial υ R) (x : υ -> 
R) : comap (g.comp …
-/
theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g := by
  funext x
  exact comap_comp_apply _ _ _
/-
**MvPolynomial.comap_eq_id_of_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_eq_id_of_eq_id (f : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R) (hf : 
forall φ, f φ = φ) (x : σ -> R) : comap f x = x
参数：f : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R；hf : forall φ, f φ = φ；x : σ -> 
R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.comap_id_apply`：comap_id_apply (x : σ -> R) : comap (AlgHom
.id R (MvPolynomial σ R)) x = x
-/
theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ)
    (x : σ → R) : comap f x = x := by
  convert! comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]
/-
**MvPolynomial.comap_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comap_rename (f : σ -> τ) (x : τ -> R) : comap (rename f) x = x ∘ f
参数：f : σ -> τ；x : τ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_rename (f : σ → τ) (x : τ → R) : comap (rename f) x = x ∘ f := by
  funext
  simp [rename_X, comap_apply, aeval_X]

/-- If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
/-
**MvPolynomial.comapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ -> R) ≃ (σ -
> R) where toFun
参数：f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to
 `R`.
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ → R) ≃ (σ → R) where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.symm_comp]

@[simp]
/-
**MvPolynomial.comapEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (comapEquiv
 f : (τ -> R) -> σ -> R) = comap f
参数：f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (comapEquiv f : (τ → R) → σ → R) = comap f :=
  rfl

@[simp]
/-
**MvPolynomial.comapEquiv_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : ((coma
pEquiv f).symm : (σ -> R) -> τ -> R) = comap f.symm
参数：f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ → R) → τ → R) = comap f.symm :=
  rfl

end MvPolynomial

