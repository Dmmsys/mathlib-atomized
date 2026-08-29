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
Definition of `bind₁` / `bind₁` 的定义

English:
definition bind₁
  signature: (f : σ -> MvPolynomial τ R)
  body: aeval f

中文:
定义 bind₁
  签名: (f : σ -> MvPolynomial τ R)
  定义体: aeval f
-/
def bind₁ (f : σ -> MvPolynomial τ R) : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R :=
  aeval f

/--
Definition of `bind₂` / `bind₂` 的定义

English:
definition bind₂
  signature: (f : R ->+* MvPolynomial σ S)
  body: eval₂Hom f X

中文:
定义 bind₂
  签名: (f : R ->+* MvPolynomial σ S)
  定义体: eval₂Hom f X
-/
def bind₂ (f : R ->+* MvPolynomial σ S) : MvPolynomial σ R ->+* MvPolynomial σ S :=
  eval₂Hom f X

/--
Definition of `join₁` / `join₁` 的定义

English:
definition join₁
  signature: : MvPolynomial (MvPolynomial σ R) R ->ₐ[R] MvPolynomial σ R
  body: aeval id

中文:
定义 join₁
  签名: : MvPolynomial (MvPolynomial σ R) R ->ₐ[R] MvPolynomial σ R
  定义体: aeval id
-/
def join₁ : MvPolynomial (MvPolynomial σ R) R ->ₐ[R] MvPolynomial σ R :=
  aeval id

/--
Definition of `join₂` / `join₂` 的定义

English:
definition join₂
  signature: : MvPolynomial σ (MvPolynomial σ R) ->+* MvPolynomial σ R
  body: eval₂Hom (RingHom.id _) X

@[simp]

中文:
定义 join₂
  签名: : MvPolynomial σ (MvPolynomial σ R) ->+* MvPolynomial σ R
  定义体: eval₂Hom (RingHom.id _) X

@[simp]

Depends on / 依赖: RingHom, RingHom.id
-/
def join₂ : MvPolynomial σ (MvPolynomial σ R) ->+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X

@[simp]
/--
theorem `aeval_eq_bind₁` / 定理 `aeval_eq_bind₁`

English:
theorem aeval_eq_bind₁
  given: (f : σ -> MvPolynomial τ R)
  statement: aeval f = bind₁ f
  proof: rfl

@[simp]

中文:
定理 aeval_eq_bind₁
  条件: (f : σ -> MvPolynomial τ R)
  结论: aeval f = bind₁ f
  证明: rfl

@[simp]
-/
theorem aeval_eq_bind₁ (f : σ -> MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl

@[simp]
/--
theorem `eval₂Hom_C_eq_bind₁` / 定理 `eval₂Hom_C_eq_bind₁`

English:
theorem eval₂Hom_C_eq_bind₁
  given: (f : σ -> MvPolynomial τ R)
  statement: eval₂Hom C f = bind₁ f
  proof: rfl

@[simp]

中文:
定理 eval₂Hom_C_eq_bind₁
  条件: (f : σ -> MvPolynomial τ R)
  结论: eval₂Hom C f = bind₁ f
  证明: rfl

@[simp]
-/
theorem eval₂Hom_C_eq_bind₁ (f : σ -> MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl

@[simp]
/--
theorem `eval₂Hom_eq_bind₂` / 定理 `eval₂Hom_eq_bind₂`

English:
theorem eval₂Hom_eq_bind₂
  given: (f : R ->+* MvPolynomial σ S)
  statement: eval₂Hom f X = bind₂ f
  proof: rfl

中文:
定理 eval₂Hom_eq_bind₂
  条件: (f : R ->+* MvPolynomial σ S)
  结论: eval₂Hom f X = bind₂ f
  证明: rfl
-/
theorem eval₂Hom_eq_bind₂ (f : R ->+* MvPolynomial σ S) : eval₂Hom f X = bind₂ f :=
  rfl

section

variable (σ R)

@[simp]
/--
theorem `aeval_id_eq_join₁` / 定理 `aeval_id_eq_join₁`

English:
theorem aeval_id_eq_join₁
  statement: aeval id = @join₁ σ R _
  proof: rfl

中文:
定理 aeval_id_eq_join₁
  结论: aeval id = @join₁ σ R _
  证明: rfl
-/
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl

/--
theorem `eval₂Hom_C_id_eq_join₁` / 定理 `eval₂Hom_C_id_eq_join₁`

English:
theorem eval₂Hom_C_id_eq_join₁
  given: (φ : MvPolynomial (MvPolynomial σ R) R)
  proof: rfl

@[simp]

中文:
定理 eval₂Hom_C_id_eq_join₁
  条件: (φ : MvPolynomial (MvPolynomial σ R) R)
  证明: rfl

@[simp]
-/
theorem eval₂Hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) :
    eval₂Hom C id φ = join₁ φ :=
  rfl

@[simp]
/--
theorem `eval₂Hom_id_X_eq_join₂` / 定理 `eval₂Hom_id_X_eq_join₂`

English:
theorem eval₂Hom_id_X_eq_join₂
  statement: eval₂Hom (RingHom.id _) X = @join₂ σ R _
  proof: rfl

中文:
定理 eval₂Hom_id_X_eq_join₂
  结论: eval₂Hom (RingHom.id _) X = @join₂ σ R _
  证明: rfl
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
/--
theorem `bind₁_X_right` / 定理 `bind₁_X_right`

English:
theorem bind₁_X_right
  given: (f : σ -> MvPolynomial τ R) (i : σ)
  statement: bind₁ f (X i) = f i
  proof: aeval_X f i

@[simp]

中文:
定理 bind₁_X_right
  条件: (f : σ -> MvPolynomial τ R) (i : σ)
  结论: bind₁ f (X i) = f i
  证明: aeval_X f i

@[simp]

Depends on / 依赖: aeval_X
-/
theorem bind₁_X_right (f : σ -> MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i

@[simp]
/--
theorem `bind₂_X_right` / 定理 `bind₂_X_right`

English:
theorem bind₂_X_right
  given: (f : R ->+* MvPolynomial σ S) (i : σ)
  statement: bind₂ f (X i) = X i
  proof: eval₂Hom_X' f X i

@[simp]

中文:
定理 bind₂_X_right
  条件: (f : R ->+* MvPolynomial σ S) (i : σ)
  结论: bind₂ f (X i) = X i
  证明: eval₂Hom_X' f X i

@[simp]
-/
theorem bind₂_X_right (f : R ->+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂Hom_X' f X i

@[simp]
/--
theorem `bind₁_X_left` / 定理 `bind₁_X_left`

English:
theorem bind₁_X_left
  statement: bind₁ (X : σ -> MvPolynomial σ R) = AlgHom.id R _
  proof: by
  ext1 i
  simp

中文:
定理 bind₁_X_left
  结论: bind₁ (X : σ -> MvPolynomial σ R) = AlgHom.id R _
  证明: by
  ext1 i
  simp
-/
theorem bind₁_X_left : bind₁ (X : σ -> MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  simp

variable (f : σ -> MvPolynomial τ R)

/--
theorem `bind₁_C_right` / 定理 `bind₁_C_right`

English:
theorem bind₁_C_right
  given: (f : σ -> MvPolynomial τ R) (x)
  statement: bind₁ f (C x) = C x
  proof: algHom_C _ _

@[simp]

中文:
定理 bind₁_C_right
  条件: (f : σ -> MvPolynomial τ R) (x)
  结论: bind₁ f (C x) = C x
  证明: algHom_C _ _

@[simp]

Depends on / 依赖: algHom_C
-/
theorem bind₁_C_right (f : σ -> MvPolynomial τ R) (x) : bind₁ f (C x) = C x := algHom_C _ _

@[simp]
/--
theorem `bind₂_C_right` / 定理 `bind₂_C_right`

English:
theorem bind₂_C_right
  given: (f : R ->+* MvPolynomial σ S) (r : R)
  statement: bind₂ f (C r) = f r
  proof: eval₂Hom_C f X r

@[simp]

中文:
定理 bind₂_C_right
  条件: (f : R ->+* MvPolynomial σ S) (r : R)
  结论: bind₂ f (C r) = f r
  证明: eval₂Hom_C f X r

@[simp]
-/
theorem bind₂_C_right (f : R ->+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂Hom_C f X r

@[simp]
/--
theorem `bind₂_C_left` / 定理 `bind₂_C_left`

English:
theorem bind₂_C_left
  statement: bind₂ (C : R ->+* MvPolynomial σ R) = RingHom.id _
  proof: by ext : 2 <;> simp

@[simp]

中文:
定理 bind₂_C_left
  结论: bind₂ (C : R ->+* MvPolynomial σ R) = RingHom.id _
  证明: by ext : 2 <;> simp

@[simp]
-/
theorem bind₂_C_left : bind₂ (C : R ->+* MvPolynomial σ R) = RingHom.id _ := by ext : 2 <;> simp

@[simp]
/--
theorem `bind₂_comp_C` / 定理 `bind₂_comp_C`

English:
theorem bind₂_comp_C
  given: (f : R ->+* MvPolynomial σ S)
  statement: (bind₂ f).comp C = f
  proof: RingHom.ext bind₂_C_right _

@[simp]

中文:
定理 bind₂_comp_C
  条件: (f : R ->+* MvPolynomial σ S)
  结论: (bind₂ f).comp C = f
  证明: RingHom.ext bind₂_C_right _

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem bind₂_comp_C (f : R ->+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
RingHom.ext bind₂_C_right _

@[simp]
/--
theorem `join₂_map` / 定理 `join₂_map`

English:
theorem join₂_map
  given: (f : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R)
  proof: by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]

@[simp]

中文:
定理 join₂_map
  条件: (f : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R)
  证明: by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]

@[simp]

Depends on / 依赖: RingHom, RingHom.id_comp, id_comp
-/
theorem join₂_map (f : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    join₂ (map f φ) = bind₂ f φ := by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]

@[simp]
/--
theorem `join₂_comp_map` / 定理 `join₂_comp_map`

English:
theorem join₂_comp_map
  given: (f : R ->+* MvPolynomial σ S)
  statement: join₂.comp (map f) = bind₂ f
  proof: RingHom.ext join₂_map _

中文:
定理 join₂_comp_map
  条件: (f : R ->+* MvPolynomial σ S)
  结论: join₂.comp (map f) = bind₂ f
  证明: RingHom.ext join₂_map _

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem join₂_comp_map (f : R ->+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
RingHom.ext join₂_map _

/--
theorem `aeval_id_rename` / 定理 `aeval_id_rename`

English:
theorem aeval_id_rename
  given: (f : σ -> MvPolynomial τ R) (p : MvPolynomial σ R)
  proof: by rw [aeval_rename, Function.id_comp]

@[simp]

中文:
定理 aeval_id_rename
  条件: (f : σ -> MvPolynomial τ R) (p : MvPolynomial σ R)
  证明: by rw [aeval_rename, Function.id_comp]

@[simp]

Depends on / 依赖: Function, Function.id_comp, aeval_rename, id_comp
-/
theorem aeval_id_rename (f : σ -> MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.id_comp]

@[simp]
/--
theorem `join₁_rename` / 定理 `join₁_rename`

English:
theorem join₁_rename
  given: (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: aeval_id_rename _ _

@[simp]

中文:
定理 join₁_rename
  条件: (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: aeval_id_rename _ _

@[simp]

Depends on / 依赖: aeval_id_rename
-/
theorem join₁_rename (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _

@[simp]
/--
theorem `bind₁_id` / 定理 `bind₁_id`

English:
theorem bind₁_id
  statement: bind₁ (@id (MvPolynomial σ R)) = join₁
  proof: rfl

@[simp]

中文:
定理 bind₁_id
  结论: bind₁ (@id (MvPolynomial σ R)) = join₁
  证明: rfl

@[simp]
-/
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl

@[simp]
/--
theorem `bind₂_id` / 定理 `bind₂_id`

English:
theorem bind₂_id
  statement: bind₂ (RingHom.id (MvPolynomial σ R)) = join₂
  proof: rfl

中文:
定理 bind₂_id
  结论: bind₂ (RingHom.id (MvPolynomial σ R)) = join₂
  证明: rfl
-/
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl

/--
theorem `bind₁_bind₁` / 定理 `bind₁_bind₁`

English:
theorem bind₁_bind₁
  statement: {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R)
  proof: by
  simp [bind₁, ← comp_aeval]

中文:
定理 bind₁_bind₁
  结论: {υ : 类型} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R)
  证明: by
  simp [bind₁, ← comp_aeval]

Depends on / 依赖: comp_aeval
-/
theorem bind₁_bind₁ {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]

/--
theorem `bind₁_comp_bind₁` / 定理 `bind₁_comp_bind₁`

English:
theorem bind₁_comp_bind₁
  given: {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R)
  proof: by
  ext1
  apply bind₁_bind₁

中文:
定理 bind₁_comp_bind₁
  条件: {υ : 类型} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R)
  证明: by
  ext1
  apply bind₁_bind₁
-/
theorem bind₁_comp_bind₁ {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  apply bind₁_bind₁

/--
theorem `bind₂_comp_bind₂` / 定理 `bind₂_comp_bind₂`

English:
theorem bind₂_comp_bind₂
  given: (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T)
  proof: by ext : 2 <;> simp

中文:
定理 bind₂_comp_bind₂
  条件: (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T)
  证明: by ext : 2 <;> simp
-/
theorem bind₂_comp_bind₂ (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) := by ext : 2 <;> simp

/--
theorem `bind₂_bind₂` / 定理 `bind₂_bind₂`

English:
theorem bind₂_bind₂
  statement: (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T)
  proof: RingHom.congr_fun (bind₂_comp_bind₂ f g) φ

中文:
定理 bind₂_bind₂
  结论: (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T)
  证明: RingHom.congr_fun (bind₂_comp_bind₂ f g) φ

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun
-/
theorem bind₂_bind₂ (f : R ->+* MvPolynomial σ S) (g : S ->+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ

/--
theorem `rename_comp_bind₁` / 定理 `rename_comp_bind₁`

English:
theorem rename_comp_bind₁
  given: {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> υ)
  proof: by
  ext1 i
  simp

中文:
定理 rename_comp_bind₁
  条件: {υ : 类型} (f : σ -> MvPolynomial τ R) (g : τ -> υ)
  证明: by
  ext1 i
  simp
-/
theorem rename_comp_bind₁ {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> υ) :
(rename g).comp (bind₁ f) = bind₁ fun i => rename g f i := by
  ext1 i
  simp

/--
theorem `rename_bind₁` / 定理 `rename_bind₁`

English:
theorem rename_bind₁
  given: {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> υ) (φ : MvPolynomial σ R)
  proof: AlgHom.congr_fun (rename_comp_bind₁ f g) φ

中文:
定理 rename_bind₁
  条件: {υ : 类型} (f : σ -> MvPolynomial τ R) (g : τ -> υ) (φ : MvPolynomial σ R)
  证明: AlgHom.congr_fun (rename_comp_bind₁ f g) φ

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun
-/
theorem rename_bind₁ {υ : Type*} (f : σ -> MvPolynomial τ R) (g : τ -> υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g <| f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ

/--
theorem `map_bind₂` / 定理 `map_bind₂`

English:
theorem map_bind₂
  given: (f : R ->+* MvPolynomial σ S) (g : S ->+* T) (φ : MvPolynomial σ R)
  proof: by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]

中文:
定理 map_bind₂
  条件: (f : R ->+* MvPolynomial σ S) (g : S ->+* T) (φ : MvPolynomial σ R)
  证明: by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_X
-/
theorem map_bind₂ (f : R ->+* MvPolynomial σ S) (g : S ->+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]

/--
theorem `bind₁_comp_rename` / 定理 `bind₁_comp_rename`

English:
theorem bind₁_comp_rename
  given: {υ : Type*} (f : τ -> MvPolynomial υ R) (g : σ -> τ)
  proof: by
  ext1 i
  simp

中文:
定理 bind₁_comp_rename
  条件: {υ : 类型} (f : τ -> MvPolynomial υ R) (g : σ -> τ)
  证明: by
  ext1 i
  simp
-/
theorem bind₁_comp_rename {υ : Type*} (f : τ -> MvPolynomial υ R) (g : σ -> τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) := by
  ext1 i
  simp

/--
theorem `bind₁_rename` / 定理 `bind₁_rename`

English:
theorem bind₁_rename
  given: {υ : Type*} (f : τ -> MvPolynomial υ R) (g : σ -> τ) (φ : MvPolynomial σ R)
  proof: AlgHom.congr_fun (bind₁_comp_rename f g) φ

中文:
定理 bind₁_rename
  条件: {υ : 类型} (f : τ -> MvPolynomial υ R) (g : σ -> τ) (φ : MvPolynomial σ R)
  证明: AlgHom.congr_fun (bind₁_comp_rename f g) φ

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun
-/
theorem bind₁_rename {υ : Type*} (f : τ -> MvPolynomial υ R) (g : σ -> τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ

/--
theorem `bind₂_map` / 定理 `bind₂_map`

English:
theorem bind₂_map
  given: (f : S ->+* MvPolynomial σ T) (g : R ->+* S) (φ : MvPolynomial σ R)
  proof: by simp [bind₂]

@[simp]

中文:
定理 bind₂_map
  条件: (f : S ->+* MvPolynomial σ T) (g : R ->+* S) (φ : MvPolynomial σ R)
  证明: by simp [bind₂]

@[simp]
-/
theorem bind₂_map (f : S ->+* MvPolynomial σ T) (g : R ->+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by simp [bind₂]

@[simp]
/--
theorem `map_comp_C` / 定理 `map_comp_C`

English:
theorem map_comp_C
  given: (f : R ->+* S)
  statement: (map f).comp (C : R ->+* MvPolynomial σ R) = C.comp f
  proof: by
  ext1
  apply map_C

中文:
定理 map_comp_C
  条件: (f : R ->+* S)
  结论: (map f).comp (C : R ->+* MvPolynomial σ R) = C.comp f
  证明: by
  ext1
  apply map_C

Depends on / 依赖: map_C
-/
theorem map_comp_C (f : R ->+* S) : (map f).comp (C : R ->+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C

-- mixing the two monad structures
/--
theorem `hom_bind₁` / 定理 `hom_bind₁`

English:
theorem hom_bind₁
  given: (f : MvPolynomial τ R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: by
  rw [bind₁]; rw [map_aeval]; rw [algebraMap_eq]

中文:
定理 hom_bind₁
  条件: (f : MvPolynomial τ R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: by
  rw [bind₁]; rw [map_aeval]; rw [algebraMap_eq]

Depends on / 依赖: algebraMap_eq, map_aeval
-/
theorem hom_bind₁ (f : MvPolynomial τ R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁]; rw [map_aeval]; rw [algebraMap_eq]

/--
theorem `map_bind₁` / 定理 `map_bind₁`

English:
theorem map_bind₁
  given: (f : R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: by
  rw [hom_bind₁]; rw [map_comp_C]; rw [← eval₂Hom_map_hom]
  rfl

@[simp]

中文:
定理 map_bind₁
  条件: (f : R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: by
  rw [hom_bind₁]; rw [map_comp_C]; rw [← eval₂Hom_map_hom]
  rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.map, map_comp_C, smul_equiv_smul
-/
theorem map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁]; rw [map_comp_C]; rw [← eval₂Hom_map_hom]
  rfl

@[simp]
/--
theorem `eval₂Hom_comp_C` / 定理 `eval₂Hom_comp_C`

English:
theorem eval₂Hom_comp_C
  given: (f : R ->+* S) (g : σ -> S)
  statement: (eval₂Hom f g).comp C = f
  proof: by
  ext1 r
  exact eval₂_C f g r

中文:
定理 eval₂Hom_comp_C
  条件: (f : R ->+* S) (g : σ -> S)
  结论: (eval₂Hom f g).comp C = f
  证明: by
  ext1 r
  exact eval₂_C f g r
-/
theorem eval₂Hom_comp_C (f : R ->+* S) (g : σ -> S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r

/--
theorem `eval₂Hom_bind₁` / 定理 `eval₂Hom_bind₁`

English:
theorem eval₂Hom_bind₁
  given: (f : R ->+* S) (g : τ -> S) (h : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: by
  rw [hom_bind₁]; rw [eval₂Hom_comp_C]

中文:
定理 eval₂Hom_bind₁
  条件: (f : R ->+* S) (g : τ -> S) (h : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: by
  rw [hom_bind₁]; rw [eval₂Hom_comp_C]
-/
theorem eval₂Hom_bind₁ (f : R ->+* S) (g : τ -> S) (h : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [hom_bind₁]; rw [eval₂Hom_comp_C]

/--
theorem `aeval_bind₁` / 定理 `aeval_bind₁`

English:
theorem aeval_bind₁
  given: [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: eval₂Hom_bind₁ _ _ _ _

中文:
定理 aeval_bind₁
  条件: [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: eval₂Hom_bind₁ _ _ _ _
-/
theorem aeval_bind₁ [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

/--
theorem `aeval_comp_bind₁` / 定理 `aeval_comp_bind₁`

English:
theorem aeval_comp_bind₁
  given: [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R)
  proof: by
  ext1
  apply aeval_bind₁

中文:
定理 aeval_comp_bind₁
  条件: [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R)
  证明: by
  ext1
  apply aeval_bind₁
-/
theorem aeval_comp_bind₁ [Algebra R S] (f : τ -> S) (g : σ -> MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply aeval_bind₁

/--
theorem `eval₂Hom_comp_bind₂` / 定理 `eval₂Hom_comp_bind₂`

English:
theorem eval₂Hom_comp_bind₂
  given: (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S)
  proof: by ext : 2 <;> simp

中文:
定理 eval₂Hom_comp_bind₂
  条件: (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S)
  证明: by ext : 2 <;> simp
-/
theorem eval₂Hom_comp_bind₂ (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S) :
    (eval₂Hom f g).comp (bind₂ h) = eval₂Hom ((eval₂Hom f g).comp h) g := by ext : 2 <;> simp

/--
theorem `eval₂Hom_bind₂` / 定理 `eval₂Hom_bind₂`

English:
theorem eval₂Hom_bind₂
  statement: (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S)
  proof: RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ

中文:
定理 eval₂Hom_bind₂
  结论: (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S)
  证明: RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ

Depends on / 依赖: RingHom, RingHom.congr_fun, congr_fun
-/
theorem eval₂Hom_bind₂ (f : S ->+* T) (g : σ -> T) (h : R ->+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ

/--
theorem `aeval_bind₂` / 定理 `aeval_bind₂`

English:
theorem aeval_bind₂
  given: [Algebra S T] (f : σ -> T) (g : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R)
  proof: eval₂Hom_bind₂ _ _ _ _

alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁

中文:
定理 aeval_bind₂
  条件: [Algebra S T] (f : σ -> T) (g : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R)
  证明: eval₂Hom_bind₂ _ _ _ _

alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁
-/
theorem aeval_bind₂ [Algebra S T] (f : σ -> T) (g : R ->+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂Hom ((↑(aeval f : _ ->ₐ[S] _) : _ ->+* _).comp g) f φ :=
  eval₂Hom_bind₂ _ _ _ _

alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁

/--
theorem `bind₁_monomial` / 定理 `bind₁_monomial`

English:
theorem bind₁_monomial
  given: (f : σ -> MvPolynomial τ R) (d : σ ->₀ Nat) (r : R)
  proof: by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]

中文:
定理 bind₁_monomial
  条件: (f : σ -> MvPolynomial τ R) (d : σ ->₀ 自然数) (r : R)
  证明: by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]

Depends on / 依赖: Finsupp, Finsupp.prod, map_mul, map_pow, map_prod, monomial_eq
-/
theorem bind₁_monomial (f : σ -> MvPolynomial τ R) (d : σ ->₀ Nat) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^ d i := by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]

/--
theorem `bind₂_monomial` / 定理 `bind₂_monomial`

English:
theorem bind₂_monomial
  given: (f : R ->+* MvPolynomial σ S) (d : σ ->₀ Nat) (r : R)
  proof: by
  simp only [monomial_eq, map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]

@[simp]

中文:
定理 bind₂_monomial
  条件: (f : R ->+* MvPolynomial σ S) (d : σ ->₀ 自然数) (r : R)
  证明: by
  simp only [monomial_eq, map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.prod, map_mul, map_pow, map_prod, monomial_eq, one_mul
-/
theorem bind₂_monomial (f : R ->+* MvPolynomial σ S) (d : σ ->₀ Nat) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]

@[simp]
/--
theorem `bind₂_monomial_one` / 定理 `bind₂_monomial_one`

English:
theorem bind₂_monomial_one
  given: (f : R ->+* MvPolynomial σ S) (d : σ ->₀ Nat)
  proof: by rw [bind₂_monomial, f.map_one, one_mul]

中文:
定理 bind₂_monomial_one
  条件: (f : R ->+* MvPolynomial σ S) (d : σ ->₀ 自然数)
  证明: by rw [bind₂_monomial, f.map_one, one_mul]

Depends on / 依赖: f.map_one, map_one, one_mul
-/
theorem bind₂_monomial_one (f : R ->+* MvPolynomial σ S) (d : σ ->₀ Nat) :
    bind₂ f (monomial d 1) = monomial d 1 := by rw [bind₂_monomial, f.map_one, one_mul]

section

/--
theorem `vars_bind₁` / 定理 `vars_bind₁`

English:
theorem vars_bind₁
  given: [DecidableEq τ] (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: by
  calc (bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ ->₀ Nat => (bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum]; rw [← φ.as_sum]
    _ <= φ.support.biUnion fun i : σ ->₀ Nat => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUni

中文:
定理 vars_bind₁
  条件: [DecidableEq τ] (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  证明: by
  calc (bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ ->₀ Nat => (bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum]; rw [← φ.as_sum]
    _ <= φ.support.biUnion fun i : σ ->₀ Nat => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUni

Depends on / 依赖: as_sum, biUnion, d.support, d.support.biUnion, map_sum, monomial, support, support.biUnion, support.sum, vars_sum_subset
-/
theorem vars_bind₁ [DecidableEq τ] (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (bind₁ f φ).vars subseteq φ.vars.biUnion fun i => (f i).vars := by
  calc (bind₁ f φ).vars
    _ = (φ.support.sum fun x : σ ->₀ Nat => (bind₁ f) (monomial x (coeff x φ))).vars := by
      rw [← map_sum]; rw [← φ.as_sum]
    _ <= φ.support.biUnion fun i : σ ->₀ Nat => ((bind₁ f) (monomial i (coeff i φ))).vars :=
      (vars_sum_subset _ _)
    _ = φ.support.biUnion fun d : σ ->₀ Nat => vars (C (coeff d φ) * ∏ i in d.support, f i ^ d i) := by
      simp only [bind₁_monomial]
    _ <= φ.support.biUnion fun d : σ ->₀ Nat => d.support.biUnion fun i => vars (f i) := ?_
    -- proof below
    _ <= φ.vars.biUnion fun i : σ => vars (f i) := ?_
    -- proof below
  · apply Finset.biUnion_mono
    intro d _hd
    calc
      vars (C (coeff d φ) * ∏ i in d.support, f i ^ d i) <=
          (C (coeff d φ)).vars union (∏ i in d.support, f i ^ d i).vars :=
        vars_mul _ _
      _ <= (∏ i in d.support, f i ^ d i).vars := by
        simp only [Finset.empty_union, vars_C, Finset.Subset.refl]
      _ <= d.support.biUnion fun i : σ => vars (f i ^ d i) := vars_prod _
      _ <= d.support.biUnion fun i : σ => (f i).vars := ?_
    apply Finset.biUnion_mono
    intro i _hi
    apply vars_pow
  · intro j
    simp_rw [Finset.mem_biUnion]
    rintro ⟨d, hd, ⟨i, hi, hj⟩⟩
    exact ⟨i, (mem_vars_iff_mem_support _).mpr ⟨d, hd, hi⟩, hj⟩

end

/--
theorem `mem_vars_bind₁` / 定理 `mem_vars_bind₁`

English:
theorem mem_vars_bind₁
  statement: (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
  proof: by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_bind₁ f φ h

中文:
定理 mem_vars_bind₁
  结论: (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
  证明: by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_bind₁ f φ h

Depends on / 依赖: Finset, Finset.mem_biUnion, classical, exists_prop, mem_biUnion, mem_support_iff
-/
theorem mem_vars_bind₁ (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j in (bind₁ f φ).vars) : exists i : σ, i in φ.vars ∧ j in (f i).vars := by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_bind₁ f φ h

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad fun σ => MvPolynomial σ R where
  body: rename f p
  pure := X
  bind p f := bind₁ f p

中文:
实例 monad
  签名: : Monad fun σ => MvPolynomial σ R where
  定义体: rename f p
  pure := X
  bind p f := bind₁ f p
-/
instance monad : Monad fun σ => MvPolynomial σ R where
  map f p := rename f p
  pure := X
  bind p f := bind₁ f p

/--
Instance `lawfulFunctor` / 实例 `lawfulFunctor`

English:
instance lawfulFunctor
  signature: : LawfulFunctor fun σ => MvPolynomial σ R where
  body: by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]

中文:
实例 lawfulFunctor
  签名: : LawfulFunctor fun σ => MvPolynomial σ R where
  定义体: by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]

Depends on / 依赖: comp_map, id_map, intros
-/
instance lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R where
  map_const := by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]

/--
Instance `lawfulMonad` / 实例 `lawfulMonad`

English:
instance lawfulMonad
  signature: : LawfulMonad fun σ => MvPolynomial σ R where
  body: by intros; simp [pure, bind]
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁]
  seqLeft_eq _ _ := by
    simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), bind₁_rename]; simp [rename_eq_aeval]; rfl
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  pure_

中文:
实例 lawfulMonad
  签名: : LawfulMonad fun σ => MvPolynomial σ R where
  定义体: by intros; simp [pure, bind]
  bind_assoc := by intros; simp [bind, ← bind₁_comp_bind₁]
  seqLeft_eq _ _ := by
    simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), bind₁_rename]; simp [rename_eq_aeval]; rfl
  seqRight_eq := by intros; simp [SeqRight.seqRight, Seq.seq, (· <$> ·), bind₁_rename]; rfl
  pure_

Depends on / 依赖: Seq.seq, SeqLeft, SeqLeft.seqLeft, SeqRight, SeqRight.seqRight, bind_assoc, bind_map, bind_pure_comp, intros, pure_seq, rename_eq_aeval, seqLeft, seqLeft_eq, seqRight, seqRight_eq
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
