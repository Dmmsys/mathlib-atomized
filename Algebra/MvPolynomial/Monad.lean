/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Variables

/-!

# Monad operations on `MvPolynomial`

This file defines two monadic operations on `MvPolynomial`. Given `p : MvPolynomial σ R`,

* `MvPolynomial.bind₁` and `MvPolynomial.join₁` operate on the variable type `σ`.
* `MvPolynomial.bind₂` and `MvPolynomial.join₂` operate on the coefficient type `R`.

- `MvPolynomial.bind₁ f φ` with `f : σ → MvPolynomial τ R` and `φ : MvPolynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : MvPolynomial τ R`.
- `MvPolynomial.join₁ φ` with `φ : MvPolynomial (MvPolynomial σ R) R` collapses `φ` to
  a `MvPolynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : MvPolynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `MvPolynomial.bind₂ f φ` with `f : R →+* MvPolynomial σ S` and `φ : MvPolynomial σ R`
  is the `MvPolynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `MvPolynomial σ R`.
- `MvPolynomial.join₂ φ` with `φ : MvPolynomial σ (MvPolynomial σ R)` collapses `φ` to
  a `MvPolynomial σ R`, by considering `φ` as polynomial expression in `MvPolynomial σ R`.

These operations themselves have algebraic structure: `MvPolynomial.bind₁`
and `MvPolynomial.join₁` are algebra homs and
`MvPolynomial.bind₂` and `MvPolynomial.join₂` are ring homs.

They interact in convenient ways with `MvPolynomial.rename`, `MvPolynomial.map`,
`MvPolynomial.vars`, and other polynomial operations.
Indeed, `MvPolynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `MvPolynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add a `LawfulMonad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `Monad`,
since it is not a monad in `Type` but in `CommRingCat` (or rather `CommSemiRingCat`).

-/

@[expose] public section


noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {τ : Type*}
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/--
`bind₁` is the "left-hand side" bind operation on `MvPolynomial`, operating on the variable type.
Given a polynomial `p : MvPolynomial σ R` and a map `f : σ → MvPolynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bind₁` is the "left-hand side" bind operation on `MvPolynomial`, operating on t
he variable type.
Given a polynomial `p : MvPolynomial σ R` and a map `f : σ → MvPolynomial τ R` t
aking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variab
le in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type rem
ains the same.
This operation is an algebra hom.
-/
def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f

/-- `bind₂` is the "right-hand side" bind operation on `MvPolynomial`,
operating on the coefficient type.
Given a polynomial `p : MvPolynomial σ R` and
a map `f : R → MvPolynomial σ S` taking coefficients in `p` to polynomials over a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`bind₂` is the "right-hand side" bind operation on `MvPolynomial`,
operating on the coefficient type.
Given a polynomial `p : MvPolynomial σ R` and
a map `f : R → MvPolynomial σ S` taking coefficients in `p` to polynomials over 
a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂Hom f X

/--
`join₁` is the monadic join operation corresponding to `MvPolynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
/-
**MvPolynomial.join** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomi
al σ S
参数：f : R →+* S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`join₁` is the monadic join operation corresponding to `MvPolynomial.bind₁`. Giv
en a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficient
s in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients i
n `R`.
This operation is an algebra hom.
-/
def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id

/--
`join₂` is the monadic join operation corresponding to `MvPolynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
/-
**MvPolynomial.join** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomi
al σ S
参数：f : R →+* S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`join₂` is the monadic join operation corresponding to `MvPolynomial.bind₂`. Giv
en a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficient
s in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients i
n `R`.
This operation is a ring hom.
-/
def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X

@[simp]
/-
**MvPolynomial.aeval_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂Hom f X = bind₂ f :=
  rfl

section

variable (σ R)

@[simp]
/-
**MvPolynomial.aeval_id_eq_join** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) :
    eval₂Hom C id φ = join₁ φ :=
  rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_id_X_eq_join₂ : eval₂Hom (RingHom.id _) X = @join₂ σ R _ :=
  rfl

end

-- In this file, we don't want to use these simp lemmas,
-- because we first need to show how these new definitions interact
-- and the proofs fall back on unfolding the definitions and call simp afterwards
attribute [-simp]
  aeval_eq_bind₁ eval₂Hom_C_eq_bind₁ eval₂Hom_eq_bind₂ aeval_id_eq_join₁ eval₂Hom_id_X_eq_join₂

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂Hom_X' f X i

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_X_left : bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  simp

variable (f : σ → MvPolynomial τ R)
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_C_right (f : σ → MvPolynomial τ R) (x) : bind₁ f (C x) = C x := algHom_C _ _

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂Hom_C f X r

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_C_left : bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := by ext : 2 <;> simp

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
  RingHom.ext <| bind₂_C_right _

@[simp]
/-
**MvPolynomial.join** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomi
al σ S
参数：f : R →+* S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    join₂ (map f φ) = bind₂ f φ := by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]

@[simp]
/-
**MvPolynomial.join** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomi
al σ S
参数：f : R →+* S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
  RingHom.ext <| join₂_map _
/-
**MvPolynomial.aeval_id_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_id_rename (f : σ -> MvPolynomial τ R) (p : MvPolynomial σ R) : aeval
 id (rename f p) = aeval f p
参数：f : σ -> MvPolynomial τ R；p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.id_comp]

@[simp]
/-
**MvPolynomial.join** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomi
al σ S
参数：f : R →+* S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  apply bind₁_bind₁
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) := by ext : 2 <;> simp
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ
/-
**MvPolynomial.rename_comp_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rename_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (bind₁ f) = bind₁ fun i => rename g <| f i := by
  ext1 i
  simp
/-
**MvPolynomial.rename_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rename_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g <| f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ
/-
**MvPolynomial.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_comp_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) := by
  ext1 i
  simp
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by simp [bind₂]

@[simp]
/-
**MvPolynomial.map_comp_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：map_comp_C (f : R ->+* S) : (map f).comp (C : R ->+* MvPolynomial σ R) = C
.comp f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
-/
theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C

-- mixing the two monad structures
/-
**MvPolynomial.hom_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁, map_aeval, algebraMap_eq]
/-
**MvPolynomial.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁, map_comp_C, ← eval₂Hom_map_hom]
  rfl

@[simp]
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [hom_bind₁, eval₂Hom_comp_C]
/-
**MvPolynomial.aeval_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _
/-
**MvPolynomial.aeval_comp_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply aeval_bind₁
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) :
    (eval₂Hom f g).comp (bind₂ h) = eval₂Hom ((eval₂Hom f g).comp h) g := by ext : 2 <;> simp
/-
**MvPolynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：eval (f : σ -> R) : MvPolynomial σ R ->+* R
参数：f : σ -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂Hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ
/-
**MvPolynomial.aeval_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂Hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
  eval₂Hom_bind₂ _ _ _ _

alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i ∈ d.support, f i ^ d i := by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]

@[simp]
/-
**MvPolynomial.bind** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) : mv_polyno
mial σ R →+* mv_polynomial τ S
参数：f : R →+* mv_polynomial τ S；g : σ → mv_polynomial τ S。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    bind₂ f (monomial d 1) = monomial d 1 := by rw [bind₂_monomial, f.map_one, one_mul]

section

/-
**MvPolynomial.vars_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vars_bind₁ [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (bind₁ f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars := by
  calc (bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ →₀ ℕ => (bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum, ← φ.as_sum]
    _ ≤ φ.support.biUnion fun i : σ →₀ ℕ => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUnion fun d : σ →₀ ℕ => vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) := by
      simp only [bind₁_monomial]
    _ ≤ φ.support.biUnion fun d : σ →₀ ℕ => d.support.biUnion fun i => vars (f i) := ?_
    -- proof below
    _ ≤ φ.vars.biUnion fun i : σ => vars (f i) := ?_
    -- proof below
  · apply Finset.biUnion_mono
    intro d _hd
    calc
      vars (C (coeff d φ) * ∏ i ∈ d.support, f i ^ d i) ≤
          (C (coeff d φ)).vars ∪ (∏ i ∈ d.support, f i ^ d i).vars :=
        vars_mul _ _
      _ ≤ (∏ i ∈ d.support, f i ^ d i).vars := by
        simp only [Finset.empty_union, vars_C, Finset.Subset.refl]
      _ ≤ d.support.biUnion fun i : σ => vars (f i ^ d i) := vars_prod _
      _ ≤ d.support.biUnion fun i : σ => (f i).vars := ?_
    apply Finset.biUnion_mono
    intro i _hi
    apply vars_pow
  · intro j
    simp_rw [Finset.mem_biUnion]
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩
    exact ⟨i, (mem_vars_iff_mem_support _).mpr ⟨d, hd, hi⟩, hj⟩

end

/-
**MvPolynomial.mem_vars_bind** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_vars_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j ∈ (bind₁ f φ).vars) : ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars := by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_bind₁ f φ h
/-
**MvPolynomial.monad** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：monad : Monad fun σ => MvPolynomial σ R where map f p
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monad : Monad fun σ => MvPolynomial σ R where
  map f p := rename f p
  pure := X
  bind p f := bind₁ f p
/-
**MvPolynomial.lawfulFunctor** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R where map_const
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
-/
instance lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R where
  map_const := by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]
/-
**MvPolynomial.lawfulMonad** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：lawfulMonad : LawfulMonad fun σ => MvPolynomial σ R where pure_bind
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.bind₁_rename`：bind₁_rename {υ : Type*} (f : τ -> MvPolynomi
al υ R) (g : σ -> τ) (φ : MvPolynomial σ R) : bind₁ f (rename g φ) = bind₁ (f ∘ 
g) φ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MvPolynomial.rename_eq_aeval`：rename_eq_aeval (f : σ -> τ) : rename (R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.rename_id`：rename_id : rename id = AlgHom.id R (MvPolynomia
l σ R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance lawfulMonad : LawfulMonad fun σ => MvPolynomial σ R where
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁]
  seqLeft_eq _ _ := by
    simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), bind₁_rename]; simp [rename_eq_aeval]; rfl
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  pure_seq := by intros; simp [(· <$> ·), pure, Seq.seq]
  bind_pure_comp _ _ := congr(⇑$((rename_eq_aeval ..).symm) _)
  bind_map := by aesop

/-
Possible TODO for the future:

Enable the following definitions, and write a lot of supporting lemmas.

def bind (f : R →+* mv_polynomial τ S) (g : σ → mv_polynomial τ S) :
    mv_polynomial σ R →+* mv_polynomial τ S :=
  eval₂_hom f g

def join (f : R →+* S) : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
  aeval (map f)

def ajoin [algebra R S] : mv_polynomial (mv_polynomial σ R) S →ₐ[S] mv_polynomial σ S :=
  join (algebra_map R S)

-/
end MvPolynomial

