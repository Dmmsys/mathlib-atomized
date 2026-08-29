/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# (Semi)linear equivalences

In this file we define

* `LinearEquiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `RingHom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `RingHom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `starRingEnd`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Algebra/Ring/CompTypeclasses`.

The group structure on automorphisms, `LinearEquiv.automorphismGroup`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

@[expose] public section

assert_not_exists Field Pi.module

open Function

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

section

/--
Definition of `LinearEquiv` / `LinearEquiv` 的定义

English:
structure LinearEquiv
  parameters: {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
  extends: LinearMap σ M M₂, M ≃+ M₂
  (no additional axioms)

中文:
结构 线性等价
  参数: {R : 类型} {S : 类型} [半环 R] [半环 S] (σ : R ->+* S)
  继承: 线性映射 σ M M₂, M ≃+ M₂
  (无附加公理)
-/
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S)
  {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toAddEquiv

/-- The backwards directed function underlying a linear equivalence. -/
add_decl_doc LinearEquiv.invFun

/-- `LinearEquiv.invFun` is a right inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.right_inv

/-- `LinearEquiv.invFun` is a left inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.left_inv

/-- `M ≃ₛₗ[σ] M₂` denotes the type of linear equivalences between `M` and `M₂` over a
ring homomorphism `σ`. -/
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

/-- `M ≃ₗ[R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

/--
Definition of `SemilinearEquivClass` / `SemilinearEquivClass` 的定义

English:
class SemilinearEquivClass
  parameters: (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  extends: AddEquivClass F M M₂
  axioms and operations (1):
    - map_smulₛₗ : forall (f : F) (r : R) (x : M), f (r • x) = σ r • f x

中文:
类 半线性等价类
  参数: (F : 类型) {R S : outParam 类型} [半环 R] [半环 S]
  继承: 加法等价类 F M M₂
  公理与运算 (1 个):
    - map_smulₛₗ : 对任意 (f : F) (r : R) (x : M), f (r • x) = σ r • f x
-/
class SemilinearEquivClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  (σ : outParam <| R ->+* S) {σ' : outParam <| S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  [EquivLike F M M₂] : Prop
  extends AddEquivClass F M M₂ where
  /-- Applying a semilinear equivalence `f` over `σ` to `r • x` equals `σ r • f x`. -/
  map_smulₛₗ : forall (f : F) (r : R) (x : M), f (r • x) = σ r • f x

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.

/--
Definition of `LinearEquivClass` / `LinearEquivClass` 的定义

English:
abbreviation LinearEquivClass
  signature: (F : Type*) (R M M₂ : outParam Type*) [Semiring R] [AddCommMonoid M]
  body: SemilinearEquivClass F (RingHom.id R) M M₂

中文:
缩写 LinearEquivClass
  签名: (F : 类型) (R M M₂ : outParam 类型) [半环 R] [加法交换幺半群 M]
  定义体: SemilinearEquivClass F (RingHom.id R) M M₂

Depends on / 依赖: RingHom, RingHom.id, SemilinearEquivClass
-/
abbrev LinearEquivClass (F : Type*) (R M M₂ : outParam Type*) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  SemilinearEquivClass F (RingHom.id R) M M₂

end

namespace SemilinearEquivClass

variable (F : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module S M₂] {σ : R ->+* S} {σ' : S ->+* R}

instance (priority := 100) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [s : SemilinearEquivClass F σ M M₂] : SemilinearMapClass F σ M M₂ :=
  { s with }

variable {F}

/-- Reinterpret an element of a type of semilinear equivalences as a semilinear equivalence. -/
@[coe]
/--
Definition of `semilinearEquiv` / `semilinearEquiv` 的定义

English:
definition semilinearEquiv
  signature: [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  body: { (f : M ≃+ M₂), (f : M ->ₛₗ[σ] M₂) with }

中文:
定义 semilinearEquiv
  签名: [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  定义体: { (f : M ≃+ M₂), (f : M ->ₛₗ[σ] M₂) with }
-/
def semilinearEquiv [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [SemilinearEquivClass F σ M M₂] (f : F) : M ≃ₛₗ[σ] M₂ :=
  { (f : M ≃+ M₂), (f : M ->ₛₗ[σ] M₂) with }

end SemilinearEquivClass

namespace LinearEquiv

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
-- See note [implicit instance arguments]
variable {modM : Module R M} {modM₂ : Module S M₂} {σ : R ->+* S} {σ' : S ->+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (M ≃ₛₗ[σ] M₂) (M ->ₛₗ[σ] M₂)
  body: ⟨toLinearMap⟩

中文:
实例 :
  签名: Coe (M ≃ₛₗ[σ] M₂) (M ->ₛₗ[σ] M₂)
  定义体: ⟨toLinearMap⟩

Depends on / 依赖: toLinearMap
-/
instance : Coe (M ≃ₛₗ[σ] M₂) (M ->ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
@[implicit_reducible]
/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: (e : M ≃ₛₗ[σ] M₂)
  body: e.toAddEquiv.toEquiv

中文:
定义 toEquiv
  签名: (e : M ≃ₛₗ[σ] M₂)
  定义体: e.toAddEquiv.toEquiv

Depends on / 依赖: e.toAddEquiv.toEquiv, toAddEquiv, toEquiv
-/
def toEquiv (e : M ≃ₛₗ[σ] M₂) : M ≃ M₂ := e.toAddEquiv.toEquiv

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  proof: fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h =>
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]

中文:
定理 toEquiv_injective
  证明: fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h =>
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]

Depends on / 依赖: Injective
-/
theorem toEquiv_injective :
    (toEquiv (modM := modM) (modM₂ := modM₂) : (M ≃ₛₗ[σ] M₂) -> M ≃ M₂).Injective :=
  fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h =>
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {e₁ e₂ : M ≃ₛₗ[σ] M₂}
  statement: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  proof: toEquiv_injective.eq_iff

中文:
定理 toEquiv_inj
  条件: {e₁ e₂ : M ≃ₛₗ[σ] M₂}
  结论: e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
  证明: toEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
theorem toEquiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  statement: Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
  proof: fun _ _ H => toEquiv_injective Equiv.ext LinearMap.congr_fun H

@[simp, norm_cast]

中文:
定理 toLinearMap_injective
  结论: 单射 (toLinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
  证明: fun _ _ H => toEquiv_injective Equiv.ext LinearMap.congr_fun H

@[simp, norm_cast]

Depends on / 依赖: Equiv.ext, LinearMap, LinearMap.congr_fun, congr_fun, toEquiv_injective
-/
theorem toLinearMap_injective : Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂) :=
fun _ _ H => toEquiv_injective Equiv.ext LinearMap.congr_fun H

@[simp, norm_cast]
/--
theorem `toLinearMap_inj` / 定理 `toLinearMap_inj`

English:
theorem toLinearMap_inj
  given: {e₁ e₂ : M ≃ₛₗ[σ] M₂}
  statement: (↑e₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
  proof: toLinearMap_injective.eq_iff

中文:
定理 toLinearMap_inj
  条件: {e₁ e₂ : M ≃ₛₗ[σ] M₂}
  结论: (↑e₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
  证明: toLinearMap_injective.eq_iff

Depends on / 依赖: eq_iff, toLinearMap_injective, toLinearMap_injective.eq_iff
-/
theorem toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  toLinearMap_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃ₛₗ[σ] M₂) M M₂
  body: e.toFun
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (DFunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv

中文:
实例 :
  签名: 等价状 (M ≃ₛₗ[σ] M₂) M M₂
  定义体: e.toFun
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (DFunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv

Depends on / 依赖: e.toFun
-/
instance : EquivLike (M ≃ₛₗ[σ] M₂) M M₂ where
  coe e := e.toFun
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (DFunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂
  body: (·.map_add')
  map_smulₛₗ := (·.map_smul')

中文:
实例 :
  签名: 半线性等价类 (M ≃ₛₗ[σ] M₂) σ M M₂
  定义体: (·.map_add')
  map_smulₛₗ := (·.map_smul')

Depends on / 依赖: map_add
-/
instance : SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂ where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')

/--
theorem `toLinearMap_eq_coe` / 定理 `toLinearMap_eq_coe`

English:
theorem toLinearMap_eq_coe
  given: {e : M ≃ₛₗ[σ] M₂}
  statement: e.toLinearMap = SemilinearMapClass.semilinearMap e
  proof: rfl

@[simp]

中文:
定理 toLinearMap_eq_coe
  条件: {e : M ≃ₛₗ[σ] M₂}
  结论: e.toLinearMap = 半线性映射类.semilinearMap e
  证明: rfl

@[simp]
-/
theorem toLinearMap_eq_coe {e : M ≃ₛₗ[σ] M₂} : e.toLinearMap = SemilinearMapClass.semilinearMap e :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f invFun left_inv right_inv}
  proof: rfl

中文:
定理 coe_mk
  条件: {f invFun left_inv right_inv}
  证明: rfl
-/
theorem coe_mk {f invFun left_inv right_inv} :
    ((⟨f, invFun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) : M -> M₂) = f := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Injective (M ≃ₛₗ[σ] M₂) (M -> M₂) DFunLike.coe
  proof: DFunLike.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: @单射 (M ≃ₛₗ[σ] M₂) (M -> M₂) 依赖函数状.coe
  证明: DFunLike.coe_injective

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M -> M₂) DFunLike.coe :=
  DFunLike.coe_injective

@[simp]
/--
lemma `_root_.SemilinearEquivClass.semilinearEquiv_apply` / 引理 `_root_.SemilinearEquivClass.semilinearEquiv_apply`

English:
lemma _root_.SemilinearEquivClass.semilinearEquiv_apply
  statement: {F : Type*} [EquivLike F M M₂]
  proof: rfl

中文:
引理 _root_.半线性等价类.semilinearEquiv_apply
  结论: {F : 类型} [等价状 F M M₂]
  证明: rfl
-/
lemma _root_.SemilinearEquivClass.semilinearEquiv_apply {F : Type*} [EquivLike F M M₂]
    [SemilinearEquivClass F σ M M₂] (f : F) (x : M) :
    SemilinearEquivClass.semilinearEquiv (M₂ := M₂) f x = f x := rfl

end

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid M₄]
variable [AddCommMonoid N₁] [AddCommMonoid N₂]
variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R ->+* S} {σ' : S ->+* R}
variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}
variable (e e' : M ≃ₛₗ[σ] M₂)

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑(e : M ->ₛₗ[σ] M₂) = e
  proof: rfl

@[simp]

中文:
定理 coe_coe
  结论: ⇑(e : M ->ₛₗ[σ] M₂) = e
  证明: rfl

@[simp]
-/
theorem coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e :=
  rfl

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  statement: ⇑(e.toEquiv) = e
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  结论: ⇑(e.toEquiv) = e
  证明: rfl

@[simp]
-/
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  statement: ⇑e.toLinearMap = e
  proof: rfl

中文:
定理 coe_toLinearMap
  结论: ⇑e.toLinearMap = e
  证明: rfl
-/
theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: e.toFun = e
  proof: by dsimp

中文:
定理 toFun_eq_coe
  结论: e.toFun = e
  证明: by dsimp
-/
theorem toFun_eq_coe : e.toFun = e := by dsimp

section

variable {e e'}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, e x = e' x)
  statement: e = e'
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {x x'}
  statement: x = x' -> e x = e x'
  proof: DFunLike.congr_arg e

中文:
定理 congr_arg
  条件: {x x'}
  结论: x = x' -> e x = e x'
  证明: DFunLike.congr_arg e
-/
protected theorem congr_arg {x x'} : x = x' -> e x = e x' :=
  DFunLike.congr_arg e

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : e = e') (x : M)
  statement: e x = e' x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: (h : e = e') (x : M)
  结论: e x = e' x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: [Module R M]
  body: { LinearMap.id, Equiv.refl M with }

中文:
定义 refl
  签名: [模 R M]
  定义体: { LinearMap.id, Equiv.refl M with }

Depends on / 依赖: Equiv.refl, LinearMap, LinearMap.id
-/
def refl [Module R M] : M ≃ₗ[R] M :=
  { LinearMap.id, Equiv.refl M with }

end

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: [Module R M] (x : M)
  statement: refl R M x = x
  proof: rfl

中文:
定理 refl_apply
  条件: [模 R M] (x : M)
  结论: refl R M x = x
  证明: rfl
-/
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[symm, implicit_reducible]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : M ≃ₛₗ[σ] M₂)
  body: { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' r x := by rw [map_smulₛₗ] }

中文:
定义 symm
  签名: (e : M ≃ₛₗ[σ] M₂)
  定义体: { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' r x := by rw [map_smulₛₗ] }

Depends on / 依赖: e.invFun, e.left_inv, e.right_inv, e.toEquiv.symm, e.toEquiv.symm.invFun, e.toLinearMap.inverse, invFun, inverse, left_inv, map_smul, right_inv, toEquiv, toLinearMap
-/
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' r x := by rw [map_smulₛₗ] }

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R : Type*} {S : Type*} [Semiring R] [Semiring S]
  body: e

中文:
定义 Simps.apply
  签名: {R : 类型} {S : 类型} [半环 R] [半环 S]
  定义体: e
-/
def Simps.apply {R : Type*} {S : Type*} [Semiring R] [Semiring S]
    {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M -> M₂ :=
  e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: {R S : Type*} [Semiring R] [Semiring S]
  body: e.symm

initialize_simps_projections LinearEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: {R S : 类型} [半环 R] [半环 S]
  定义体: e.symm

initialize_simps_projections LinearEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply {R S : Type*} [Semiring R] [Semiring S]
    {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M₂ -> M :=
  e.symm

initialize_simps_projections LinearEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  statement: e.invFun = e.symm
  proof: rfl

中文:
定理 invFun_eq_symm
  结论: e.invFun = e.symm
  证明: rfl
-/
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

/--
theorem `coe_toEquiv_symm` / 定理 `coe_toEquiv_symm`

English:
theorem coe_toEquiv_symm
  statement: e.toEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv_symm
  结论: e.toEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toEquiv
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm := rfl

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {module_M₄ : Module R₄ M₄} {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}
variable {σ₁₂ : R₁ ->+* R₂} {σ₂₁ : R₂ ->+* R₁}
variable {σ₁₃ : R₁ ->+* R₃} {σ₃₁ : R₃ ->+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
variable {σ₁₄ : R₁ ->+* R₄} {σ₄₁ : R₄ ->+* R₁} [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
variable {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂}
variable {σ₂₄ : R₂ ->+* R₄} {σ₄₂ : R₄ ->+* R₂} [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄]
variable {σ₃₄ : R₃ ->+* R₄} {σ₄₃ : R₄ ->+* R₃} [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁]
variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
variable [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂]
variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

set_option linter.overlappingInstances false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `LinearEquiv.self_trans_symm`.
@[trans, nolint unusedArguments]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  body: { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }

中文:
定义 trans
  定义体: { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }

Depends on / 依赖: toEquiv, toEquiv.trans, toLinearMap, toLinearMap.comp
-/
def trans
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}
    [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
    {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]
    (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) : M₁ ≃ₛₗ[σ₁₃] M₃ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }

/-- `e₁ ≪≫ₗ e₂` denotes the composition of the linear equivalences `e₁` and `e₂`. -/
notation3:80 (name := transNotation) e₁:80 " ≪≫ₗ " e₂:81 =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids e₁ e₂

/-- `LinearEquiv.symm` defines an equivalence between `α ≃ₛₗ[σ] β` and `β ≃ₛₗ[σ] α`. -/
@[simps!]
/--
Definition of `symmEquiv` / `symmEquiv` 的定义

English:
definition symmEquiv
  signature: : (M ≃ₛₗ[σ] M₂) ≃ (M₂ ≃ₛₗ[σ'] M) where
  body: .symm
  invFun := .symm

中文:
定义 symmEquiv
  签名: : (M ≃ₛₗ[σ] M₂) ≃ (M₂ ≃ₛₗ[σ'] M) where
  定义体: .symm
  invFun := .symm
-/
def symmEquiv : (M ≃ₛₗ[σ] M₂) ≃ (M₂ ≃ₛₗ[σ'] M) where
  toFun := .symm
  invFun := .symm

variable {e₁₂} {e₂₃}

/--
theorem `coe_toAddEquiv` / 定理 `coe_toAddEquiv`

English:
theorem coe_toAddEquiv
  statement: e.toAddEquiv = e
  proof: rfl

@[simp]

中文:
定理 coe_toAddEquiv
  结论: e.toAddEquiv = e
  证明: rfl

@[simp]
-/
theorem coe_toAddEquiv : e.toAddEquiv = e :=
  rfl

@[simp]
/--
lemma `coe_addEquiv_apply` / 引理 `coe_addEquiv_apply`

English:
lemma coe_addEquiv_apply
  given: (x : M)
  statement: (e : M ≃+ M₂) x = e x
  proof: rfl

中文:
引理 coe_addEquiv_apply
  条件: (x : M)
  结论: (e : M ≃+ M₂) x = e x
  证明: rfl
-/
lemma coe_addEquiv_apply (x : M) : (e : M ≃+ M₂) x = e x :=
  rfl

/--
theorem `toAddMonoidHom_commutes` / 定理 `toAddMonoidHom_commutes`

English:
theorem toAddMonoidHom_commutes
  statement: e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom
  proof: rfl

中文:
定理 toAddMonoidHom_commutes
  结论: e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom
  证明: rfl
-/
theorem toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl

/--
lemma `coe_toAddEquiv_symm` / 引理 `coe_toAddEquiv_symm`

English:
lemma coe_toAddEquiv_symm
  statement: (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm
  proof: rfl

@[simp]

中文:
引理 coe_toAddEquiv_symm
  结论: (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm
  证明: rfl

@[simp]
-/
lemma coe_toAddEquiv_symm : (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (c : M₁)
  statement: (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c)
  proof: rfl

中文:
定理 trans_apply
  条件: (c : M₁)
  结论: (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c)
  证明: rfl
-/
theorem trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) :=
  rfl

/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  proof: rfl

@[simp]

中文:
定理 coe_trans
  证明: rfl

@[simp]
-/
theorem coe_trans :
    (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (c : M₂)
  statement: e (e.symm c) = c
  proof: e.right_inv c

@[simp]

中文:
定理 apply_symm_apply
  条件: (c : M₂)
  结论: e (e.symm c) = c
  证明: e.right_inv c

@[simp]

Depends on / 依赖: e.right_inv, right_inv
-/
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (b : M)
  statement: e.symm (e b) = b
  proof: e.left_inv b

中文:
定理 symm_apply_apply
  条件: (b : M)
  结论: e.symm (e b) = b
  证明: e.left_inv b

Depends on / 依赖: e.left_inv, left_inv
-/
theorem symm_apply_apply (b : M) : e.symm (e b) = b :=
  e.left_inv b

/--
theorem `comp_symm` / 定理 `comp_symm`

English:
theorem comp_symm
  statement: e.toLinearMap ∘ₛₗ e.symm.toLinearMap = LinearMap.id
  proof: LinearMap.ext e.apply_symm_apply

中文:
定理 comp_symm
  结论: e.toLinearMap ∘ₛₗ e.symm.toLinearMap = 线性映射.id
  证明: LinearMap.ext e.apply_symm_apply

Depends on / 依赖: LinearMap, LinearMap.ext, apply_symm_apply, e.apply_symm_apply
-/
theorem comp_symm : e.toLinearMap ∘ₛₗ e.symm.toLinearMap = LinearMap.id :=
  LinearMap.ext e.apply_symm_apply

/--
theorem `symm_comp` / 定理 `symm_comp`

English:
theorem symm_comp
  statement: e.symm.toLinearMap ∘ₛₗ e.toLinearMap = LinearMap.id
  proof: LinearMap.ext e.symm_apply_apply

@[simp]

中文:
定理 symm_comp
  结论: e.symm.toLinearMap ∘ₛₗ e.toLinearMap = 线性映射.id
  证明: LinearMap.ext e.symm_apply_apply

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp : e.symm.toLinearMap ∘ₛₗ e.toLinearMap = LinearMap.id :=
  LinearMap.ext e.symm_apply_apply

@[simp]
/--
lemma `comp_symm_assoc` / 引理 `comp_symm_assoc`

English:
lemma comp_symm_assoc
  given: (f : M₃ ->ₛₗ[σ₃₂] M₂) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  proof: by ext; simp

@[simp]

中文:
引理 comp_symm_assoc
  条件: (f : M₃ ->ₛₗ[σ₃₂] M₂) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  证明: by ext; simp

@[simp]
-/
lemma comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] :
    e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f := by ext; simp

@[simp]
/--
lemma `symm_comp_assoc` / 引理 `symm_comp_assoc`

English:
lemma symm_comp_assoc
  given: (f : M₃ ->ₛₗ[σ₃₁] M₁) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  proof: by ext; simp

@[simp]

中文:
引理 symm_comp_assoc
  条件: (f : M₃ ->ₛₗ[σ₃₁] M₁) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
  证明: by ext; simp

@[simp]
-/
lemma symm_comp_assoc (f : M₃ ->ₛₗ[σ₃₁] M₁) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] :
    e₁₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f := by ext; simp

@[simp]
/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  statement: (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm
  proof: rfl

中文:
定理 trans_symm
  结论: (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm
  证明: rfl
-/
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl

/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (c : M₃)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (c : M₃)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (c : M₃) :
    (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  statement: e.trans (refl S M₂) = e
  proof: toEquiv_injective e.toEquiv.trans_refl

@[simp]

中文:
定理 trans_refl
  结论: e.trans (refl S M₂) = e
  证明: toEquiv_injective e.toEquiv.trans_refl

@[simp]

Depends on / 依赖: e.toEquiv.trans_refl, toEquiv, toEquiv_injective, trans_refl
-/
theorem trans_refl : e.trans (refl S M₂) = e :=
  toEquiv_injective e.toEquiv.trans_refl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  statement: (refl R M).trans e = e
  proof: toEquiv_injective e.toEquiv.refl_trans

中文:
定理 refl_trans
  结论: (refl R M).trans e = e
  证明: toEquiv_injective e.toEquiv.refl_trans

Depends on / 依赖: e.toEquiv.refl_trans, refl_trans, toEquiv, toEquiv_injective
-/
theorem refl_trans : (refl R M).trans e = e :=
  toEquiv_injective e.toEquiv.refl_trans

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

/--
theorem `eq_comp_symm` / 定理 `eq_comp_symm`

English:
theorem eq_comp_symm
  given: {α : Type*} (f : M₂ -> α) (g : M₁ -> α)
  statement: f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g
  proof: e₁₂.toEquiv.eq_comp_symm f g

中文:
定理 eq_comp_symm
  条件: {α : 类型} (f : M₂ -> α) (g : M₁ -> α)
  结论: f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g
  证明: e₁₂.toEquiv.eq_comp_symm f g

Depends on / 依赖: eq_comp_symm, toEquiv, toEquiv.eq_comp_symm
-/
theorem eq_comp_symm {α : Type*} (f : M₂ -> α) (g : M₁ -> α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g

/--
theorem `comp_symm_eq` / 定理 `comp_symm_eq`

English:
theorem comp_symm_eq
  given: {α : Type*} (f : M₂ -> α) (g : M₁ -> α)
  statement: g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂
  proof: e₁₂.toEquiv.comp_symm_eq f g

中文:
定理 comp_symm_eq
  条件: {α : 类型} (f : M₂ -> α) (g : M₁ -> α)
  结论: g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂
  证明: e₁₂.toEquiv.comp_symm_eq f g

Depends on / 依赖: comp_symm_eq, toEquiv, toEquiv.comp_symm_eq
-/
theorem comp_symm_eq {α : Type*} (f : M₂ -> α) (g : M₁ -> α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g

/--
theorem `eq_symm_comp` / 定理 `eq_symm_comp`

English:
theorem eq_symm_comp
  given: {α : Type*} (f : α -> M₁) (g : α -> M₂)
  statement: f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g
  proof: e₁₂.toEquiv.eq_symm_comp f g

中文:
定理 eq_symm_comp
  条件: {α : 类型} (f : α -> M₁) (g : α -> M₂)
  结论: f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g
  证明: e₁₂.toEquiv.eq_symm_comp f g

Depends on / 依赖: eq_symm_comp, toEquiv, toEquiv.eq_symm_comp
-/
theorem eq_symm_comp {α : Type*} (f : α -> M₁) (g : α -> M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g

/--
theorem `symm_comp_eq` / 定理 `symm_comp_eq`

English:
theorem symm_comp_eq
  given: {α : Type*} (f : α -> M₁) (g : α -> M₂)
  statement: e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f
  proof: e₁₂.toEquiv.symm_comp_eq f g

@[simp]

中文:
定理 symm_comp_eq
  条件: {α : 类型} (f : α -> M₁) (g : α -> M₂)
  结论: e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f
  证明: e₁₂.toEquiv.symm_comp_eq f g

@[simp]

Depends on / 依赖: symm_comp_eq, toEquiv, toEquiv.symm_comp_eq
-/
theorem symm_comp_eq {α : Type*} (f : α -> M₁) (g : α -> M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g

@[simp]
/--
theorem `comp_coe` / 定理 `comp_coe`

English:
theorem comp_coe
  given: (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃)
  proof: rfl

中文:
定理 comp_coe
  条件: (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃)
  证明: rfl
-/
theorem comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃] M₃) :=
  rfl

/--
lemma `trans_assoc` / 引理 `trans_assoc`

English:
lemma trans_assoc
  given: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄)
  proof: rfl

中文:
引理 trans_assoc
  条件: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄)
  证明: rfl
-/
lemma trans_assoc (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄) :
    (e₁₂.trans e₂₃).trans e₃₄ = e₁₂.trans (e₂₃.trans e₃₄) := rfl

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]

/--
theorem `eq_comp_toLinearMap_symm` / 定理 `eq_comp_toLinearMap_symm`

English:
theorem eq_comp_toLinearMap_symm
  given: (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃)
  proof: by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

中文:
定理 eq_comp_toLinearMap_symm
  条件: (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃)
  证明: by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]
-/
theorem eq_comp_toLinearMap_symm (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

/--
theorem `comp_toLinearMap_symm_eq` / 定理 `comp_toLinearMap_symm_eq`

English:
theorem comp_toLinearMap_symm_eq
  given: (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃)
  proof: by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

中文:
定理 comp_toLinearMap_symm_eq
  条件: (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃)
  证明: by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

Depends on / 依赖: map_subtype_le, p.subtype, subtype
-/
theorem comp_toLinearMap_symm_eq (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

/--
theorem `eq_toLinearMap_symm_comp` / 定理 `eq_toLinearMap_symm_comp`

English:
theorem eq_toLinearMap_symm_comp
  given: (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂)
  proof: by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

中文:
定理 eq_toLinearMap_symm_comp
  条件: (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂)
  证明: by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]
-/
theorem eq_toLinearMap_symm_comp (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]

/--
theorem `toLinearMap_symm_comp_eq` / 定理 `toLinearMap_symm_comp_eq`

English:
theorem toLinearMap_symm_comp_eq
  given: (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂)
  proof: by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

@[simp]

中文:
定理 toLinearMap_symm_comp_eq
  条件: (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂)
  证明: by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

@[simp]
-/
theorem toLinearMap_symm_comp_eq (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

@[simp]
/--
theorem `comp_toLinearMap_eq_iff` / 定理 `comp_toLinearMap_eq_iff`

English:
theorem comp_toLinearMap_eq_iff
  given: (f g : M₃ ->ₛₗ[σ₃₁] M₁)
  proof: by
  refine ⟨fun h => ?_, congrArg e₁₂.comp⟩
  rw [← (toLinearMap_symm_comp_eq g (e₁₂.toLinearMap.comp f)).mpr h]; rw [eq_toLinearMap_symm_comp]

@[simp]

中文:
定理 comp_toLinearMap_eq_iff
  条件: (f g : M₃ ->ₛₗ[σ₃₁] M₁)
  证明: by
  refine ⟨fun h => ?_, congrArg e₁₂.comp⟩
  rw [← (toLinearMap_symm_comp_eq g (e₁₂.toLinearMap.comp f)).mpr h]; rw [eq_toLinearMap_symm_comp]

@[simp]

Depends on / 依赖: eq_toLinearMap_symm_comp, toLinearMap, toLinearMap.comp, toLinearMap_symm_comp_eq
-/
theorem comp_toLinearMap_eq_iff (f g : M₃ ->ₛₗ[σ₃₁] M₁) :
    e₁₂.toLinearMap.comp f = e₁₂.toLinearMap.comp g ↔ f = g := by
  refine ⟨fun h => ?_, congrArg e₁₂.comp⟩
  rw [← (toLinearMap_symm_comp_eq g (e₁₂.toLinearMap.comp f)).mpr h]; rw [eq_toLinearMap_symm_comp]

@[simp]
/--
theorem `eq_comp_toLinearMap_iff` / 定理 `eq_comp_toLinearMap_iff`

English:
theorem eq_comp_toLinearMap_iff
  given: (f g : M₂ ->ₛₗ[σ₂₃] M₃)
  proof: by
  refine ⟨fun h => ?_, fun a => congrFun (congrArg LinearMap.comp a) e₁₂.toLinearMap⟩
  rw [(eq_comp_toLinearMap_symm g (f.comp e₁₂.toLinearMap)).mpr h.symm]; rw [eq_comp_toLinearMap_symm]

中文:
定理 eq_comp_toLinearMap_iff
  条件: (f g : M₂ ->ₛₗ[σ₂₃] M₃)
  证明: by
  refine ⟨fun h => ?_, fun a => congrFun (congrArg LinearMap.comp a) e₁₂.toLinearMap⟩
  rw [(eq_comp_toLinearMap_symm g (f.comp e₁₂.toLinearMap)).mpr h.symm]; rw [eq_comp_toLinearMap_symm]

Depends on / 依赖: LinearMap, LinearMap.comp, eq_comp_toLinearMap_symm, f.comp, h.symm, toLinearMap
-/
theorem eq_comp_toLinearMap_iff (f g : M₂ ->ₛₗ[σ₂₃] M₃) :
    f.comp e₁₂.toLinearMap = g.comp e₁₂.toLinearMap ↔ f = g := by
  refine ⟨fun h => ?_, fun a => congrFun (congrArg LinearMap.comp a) e₁₂.toLinearMap⟩
  rw [(eq_comp_toLinearMap_symm g (f.comp e₁₂.toLinearMap)).mpr h.symm]; rw [eq_comp_toLinearMap_symm]

/--
lemma `comp_symm_cancel_left` / 引理 `comp_symm_cancel_left`

English:
lemma comp_symm_cancel_left
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₂] M₂)
  proof: by ext; simp

中文:
引理 comp_symm_cancel_left
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₂] M₂)
  证明: by ext; simp
-/
lemma comp_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₂] M₂) :
    e.toLinearMap ∘ₛₗ (e.symm.toLinearMap ∘ₛₗ f) = f := by ext; simp

/--
lemma `symm_comp_cancel_left` / 引理 `symm_comp_cancel_left`

English:
lemma symm_comp_cancel_left
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₁] M₁)
  proof: by ext; simp

中文:
引理 symm_comp_cancel_left
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₁] M₁)
  证明: by ext; simp
-/
lemma symm_comp_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₁] M₁) :
    e.symm.toLinearMap ∘ₛₗ (e.toLinearMap ∘ₛₗ f) = f := by ext; simp

/--
lemma `comp_symm_cancel_right` / 引理 `comp_symm_cancel_right`

English:
lemma comp_symm_cancel_right
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ->ₛₗ[σ₂₃] M₃)
  proof: by ext; simp

中文:
引理 comp_symm_cancel_right
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ->ₛₗ[σ₂₃] M₃)
  证明: by ext; simp
-/
lemma comp_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ->ₛₗ[σ₂₃] M₃) :
    (f ∘ₛₗ e.toLinearMap) ∘ₛₗ e.symm.toLinearMap = f := by ext; simp

/--
lemma `symm_comp_cancel_right` / 引理 `symm_comp_cancel_right`

English:
lemma symm_comp_cancel_right
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ->ₛₗ[σ₁₃] M₃)
  proof: by ext; simp

中文:
引理 symm_comp_cancel_right
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ->ₛₗ[σ₁₃] M₃)
  证明: by ext; simp
-/
lemma symm_comp_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ->ₛₗ[σ₁₃] M₃) :
    (f ∘ₛₗ e.symm.toLinearMap) ∘ₛₗ e.toLinearMap = f := by ext; simp

/--
lemma `trans_symm_cancel_left` / 引理 `trans_symm_cancel_left`

English:
lemma trans_symm_cancel_left
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₛₗ[σ₁₃] M₃)
  proof: by ext; simp

中文:
引理 trans_symm_cancel_left
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₛₗ[σ₁₃] M₃)
  证明: by ext; simp
-/
lemma trans_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₛₗ[σ₁₃] M₃) :
    e.trans (e.symm.trans f) = f := by ext; simp

/--
lemma `symm_trans_cancel_left` / 引理 `symm_trans_cancel_left`

English:
lemma symm_trans_cancel_left
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ≃ₛₗ[σ₂₃] M₃)
  proof: by ext; simp

中文:
引理 symm_trans_cancel_left
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ≃ₛₗ[σ₂₃] M₃)
  证明: by ext; simp
-/
lemma symm_trans_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ≃ₛₗ[σ₂₃] M₃) :
    e.symm.trans (e.trans f) = f := by ext; simp

/--
lemma `trans_symm_cancel_right` / 引理 `trans_symm_cancel_right`

English:
lemma trans_symm_cancel_right
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₁] M₁)
  proof: by ext; simp

中文:
引理 trans_symm_cancel_right
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₁] M₁)
  证明: by ext; simp
-/
lemma trans_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₁] M₁) :
    (f.trans e).trans e.symm = f := by ext; simp

/--
lemma `symm_trans_cancel_right` / 引理 `symm_trans_cancel_right`

English:
lemma symm_trans_cancel_right
  given: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₂] M₂)
  proof: by ext; simp

@[simp]

中文:
引理 symm_trans_cancel_right
  条件: (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₂] M₂)
  证明: by ext; simp

@[simp]
-/
lemma symm_trans_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₂] M₂) :
    (f.trans e.symm).trans e = f := by ext; simp

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  given: [Module R M]
  statement: (refl R M).symm = LinearEquiv.refl R M
  proof: rfl

@[simp]

中文:
定理 refl_symm
  条件: [模 R M]
  结论: (refl R M).symm = 线性等价.refl R M
  证明: rfl

@[simp]
-/
theorem refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M :=
  rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (f : M₁ ≃ₛₗ[σ₁₂] M₂)
  statement: f.trans f.symm = LinearEquiv.refl R₁ M₁
  proof: by
  ext x
  simp

@[simp]

中文:
定理 self_trans_symm
  条件: (f : M₁ ≃ₛₗ[σ₁₂] M₂)
  结论: f.trans f.symm = 线性等价.refl R₁ M₁
  证明: by
  ext x
  simp

@[simp]
-/
theorem self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R₁ M₁ := by
  ext x
  simp

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (f : M₁ ≃ₛₗ[σ₁₂] M₂)
  statement: f.symm.trans f = LinearEquiv.refl R₂ M₂
  proof: by
  ext x
  simp

@[simp]

中文:
定理 symm_trans_self
  条件: (f : M₁ ≃ₛₗ[σ₁₂] M₂)
  结论: f.symm.trans f = 线性等价.refl R₂ M₂
  证明: by
  ext x
  simp

@[simp]
-/
theorem symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.symm.trans f = LinearEquiv.refl R₂ M₂ := by
  ext x
  simp

@[simp]
/--
theorem `refl_toLinearMap` / 定理 `refl_toLinearMap`

English:
theorem refl_toLinearMap
  given: [Module R M]
  statement: (LinearEquiv.refl R M : M ->ₗ[R] M) = LinearMap.id
  proof: rfl

@[simp]

中文:
定理 refl_toLinearMap
  条件: [模 R M]
  结论: (线性等价.refl R M : M ->ₗ[R] M) = 线性映射.id
  证明: rfl

@[simp]
-/
theorem refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M ->ₗ[R] M) = LinearMap.id :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f h₁ h₂)
  statement: (LinearEquiv.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: (f h₁ h₂)
  结论: (线性等价.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e
  证明: ext fun _ => rfl
-/
theorem mk_coe (f h₁ h₂) : (LinearEquiv.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e :=
  ext fun _ => rfl

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (a b : M)
  statement: e (a + b) = e a + e b
  proof: map_add e a b

中文:
定理 map_add
  条件: (a b : M)
  结论: e (a + b) = e a + e b
  证明: map_add e a b
-/
protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: e 0 = 0
  proof: map_zero e

中文:
定理 map_zero
  结论: e 0 = 0
  证明: map_zero e
-/
protected theorem map_zero : e 0 = 0 :=
  map_zero e

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (c : R) (x : M)
  statement: e (c • x) = (σ : R -> S) c • e x
  proof: e.map_smul' c x

中文:
定理 map_smulₛₗ
  条件: (c : R) (x : M)
  结论: e (c • x) = (σ : R -> S) c • e x
  证明: e.map_smul' c x
-/
protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ : R -> S) c • e x :=
  e.map_smul' c x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁)
  statement: e (c • x) = c • e x
  proof: map_smulₛₗ e c x

中文:
定理 map_smul
  条件: (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁)
  结论: e (c • x) = c • e x
  证明: map_smulₛₗ e c x
-/
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x :=
  map_smulₛₗ e c x

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: {x : M}
  statement: e x = 0 ↔ x = 0
  proof: e.toAddEquiv.map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  条件: {x : M}
  结论: e x = 0 ↔ x = 0
  证明: e.toAddEquiv.map_eq_zero_iff

Depends on / 依赖: e.toAddEquiv.map_eq_zero_iff, map_eq_zero_iff, toAddEquiv
-/
theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff

/--
theorem `map_ne_zero_iff` / 定理 `map_ne_zero_iff`

English:
theorem map_ne_zero_iff
  given: {x : M}
  statement: e x != 0 ↔ x != 0
  proof: e.toAddEquiv.map_ne_zero_iff

@[simp]

中文:
定理 map_ne_zero_iff
  条件: {x : M}
  结论: e x != 0 ↔ x != 0
  证明: e.toAddEquiv.map_ne_zero_iff

@[simp]

Depends on / 依赖: e.toAddEquiv.map_ne_zero_iff, map_ne_zero_iff, toAddEquiv
-/
theorem map_ne_zero_iff {x : M} : e x != 0 ↔ x != 0 :=
  e.toAddEquiv.map_ne_zero_iff

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : M ≃ₛₗ[σ] M₂)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : M ≃ₛₗ[σ] M₂)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  given: [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ']
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  条件: [模 R M] [模 S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ']
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ'] :
    Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) -> M₂ ≃ₛₗ[σ'] M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `mk_coe'` / 定理 `mk_coe'`

English:
theorem mk_coe'
  given: (f h₁ h₂ h₃ h₄)
  proof: symm_bijective.injective ext fun _ => rfl

@[simp]

中文:
定理 mk_coe'
  条件: (f h₁ h₂ h₃ h₄)
  证明: symm_bijective.injective ext fun _ => rfl

@[simp]

Depends on / 依赖: injective, symm_bijective, symm_bijective.injective
-/
theorem mk_coe' (f h₁ h₂ h₃ h₄) :
    (LinearEquiv.mk ⟨⟨f, h₁⟩, h₂⟩ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
symm_bijective.injective ext fun _ => rfl

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (toLinearMap invFun h₁ h₂)
  statement: dsimp%
  proof: rfl

中文:
定理 symm_mk
  条件: (toLinearMap invFun h₁ h₂)
  结论: dsimp%
  证明: rfl

Depends on / 依赖: invFun
-/
theorem symm_mk (toLinearMap invFun h₁ h₂) : dsimp%
    (mk toLinearMap invFun h₁ h₂ : M ≃ₛₗ[σ] M₂).symm =
      { (mk toLinearMap invFun h₁ h₂ : M ≃ₛₗ[σ] M₂).symm with
        toFun := invFun
        invFun := toLinearMap } :=
  rfl

/--
theorem `coe_symm_mk` / 定理 `coe_symm_mk`

English:
theorem coe_symm_mk
  statement: [Module R M] [Module R M₂]
  proof: rfl

@[simp]

中文:
定理 coe_symm_mk
  结论: [模 R M] [模 R M₂]
  证明: rfl

@[simp]
-/
theorem coe_symm_mk [Module R M] [Module R M₂]
    {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl

@[simp]
/--
theorem `coe_symm_mk'` / 定理 `coe_symm_mk'`

English:
theorem coe_symm_mk'
  statement: [Module R M] [Module R M₂]
  proof: rfl

中文:
定理 coe_symm_mk'
  结论: [模 R M] [模 R M₂]
  证明: rfl
-/
theorem coe_symm_mk' [Module R M] [Module R M₂]
    {f inv_fun left_inv right_inv} :
    ⇑(⟨f, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun := rfl

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  statement: Function.Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  结论: 函数.双射 e
  证明: e.toEquiv.bijective
-/
protected theorem bijective : Function.Bijective e :=
  e.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Function.Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  结论: 函数.单射 e
  证明: e.toEquiv.injective
-/
protected theorem injective : Function.Injective e :=
  e.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  statement: Function.Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  结论: 函数.满射 e
  证明: e.toEquiv.surjective
-/
protected theorem surjective : Function.Surjective e :=
  e.toEquiv.surjective

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (s : Set M)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (s : 集合 M)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toEquiv.image_eq_preimage_symm s
-/
protected theorem image_eq_preimage_symm (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

/--
theorem `image_symm_eq_preimage` / 定理 `image_symm_eq_preimage`

English:
theorem image_symm_eq_preimage
  given: (s : Set M₂)
  statement: e.symm '' s = e ⁻¹' s
  proof: e.toEquiv.symm.image_eq_preimage_symm s

中文:
定理 image_symm_eq_preimage
  条件: (s : 集合 M₂)
  结论: e.symm '' s = e ⁻¹' s
  证明: e.toEquiv.symm.image_eq_preimage_symm s
-/
protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage_symm s

end

/-- `Equiv.cast (congrArg _ h)` as a linear equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {ι : Type*} {M : ι -> Type*}
  body: AddEquiv.cast h
  map_smul' _ _ := by cases h; rfl

中文:
定义 cast
  签名: {ι : 类型} {M : ι -> 类型}
  定义体: AddEquiv.cast h
  map_smul' _ _ := by cases h; rfl
-/
protected def cast {ι : Type*} {M : ι -> Type*}
    [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)] {i j : ι} (h : i = j) :
    M i ≃ₗ[R] M j where
  toAddEquiv := AddEquiv.cast h
  map_smul' _ _ := by cases h; rfl

/-- Interpret a `RingEquiv` `f` as an `f`-semilinear equiv. -/
@[simps]
/--
Definition of `_root_.RingEquiv.toSemilinearEquiv` / `_root_.RingEquiv.toSemilinearEquiv` 的定义

English:
definition _root_.RingEquiv.toSemilinearEquiv
  signature: (f : R ≃+* S)
  body: RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
    R ≃ₛₗ[(↑f : R ->+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }

中文:
定义 _root_.环等价.toSemilinearEquiv
  签名: (f : R ≃+* S)
  定义体: RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
    R ≃ₛₗ[(↑f : R ->+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }

Depends on / 依赖: RingHomInvPair, RingHomInvPair.of_ringEquiv, of_ringEquiv
-/
def _root_.RingEquiv.toSemilinearEquiv (f : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
    R ≃ₛₗ[(↑f : R ->+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R ->+* S) (f.symm : S ->+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `_root_.RingEquiv.symm_toSemilinearEquiv_symm_apply` / 引理 `_root_.RingEquiv.symm_toSemilinearEquiv_symm_apply`

English:
lemma _root_.RingEquiv.symm_toSemilinearEquiv_symm_apply
  given: (f : R ≃+* S) (x : R)
  proof: rfl

中文:
引理 _root_.环等价.symm_toSemilinearEquiv_symm_apply
  条件: (f : R ≃+* S) (x : R)
  证明: rfl

Depends on / 依赖: RingHomClass, RingHomClass.toRingHom, toRingHom
-/
lemma _root_.RingEquiv.symm_toSemilinearEquiv_symm_apply (f : R ≃+* S) (x : R) :
  f.symm.toSemilinearEquiv.symm (σ' := RingHomClass.toRingHom f) x = f x := rfl

variable [AddCommMonoid M]

/--
Definition of `ofInvolutive` / `ofInvolutive` 的定义

English:
definition ofInvolutive
  signature: {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  body: { f, hf.toPerm f with }

@[simp]

中文:
定义 ofInvolutive
  签名: {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  定义体: { f, hf.toPerm f with }

@[simp]

Depends on / 依赖: hf.toPerm, toPerm
-/
def ofInvolutive {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M ->ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }

@[simp]
/--
theorem `coe_ofInvolutive` / 定理 `coe_ofInvolutive`

English:
theorem coe_ofInvolutive
  statement: {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  proof: rfl

中文:
定理 coe_ofInvolutive
  结论: {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  证明: rfl
-/
theorem coe_ofInvolutive {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M ->ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl

end AddCommMonoid

section smul
variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [Module S V]
  [AddCommMonoid W] [Module R W] [Module S W]
  [AddCommMonoid G] [Module R G] [Module S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Sˣ (V ≃ₗ[R] W)
  body: { __ := (α : S) • e.toLinearMap
    invFun x := (↑α⁻¹ : S) • e.symm x
    left_inv _ := by simp [LinearMapClass.map_smul_of_tower e.symm, smul_smul]
    right_inv _ := by simp [smul_smul] }

中文:
实例 :
  签名: 标量乘法 Sˣ (V ≃ₗ[R] W)
  定义体: { __ := (α : S) • e.toLinearMap
    invFun x := (↑α⁻¹ : S) • e.symm x
    left_inv _ := by simp [LinearMapClass.map_smul_of_tower e.symm, smul_smul]
    right_inv _ := by simp [smul_smul] }

Depends on / 依赖: LinearMapClass, LinearMapClass.map_smul_of_tower, e.symm, e.toLinearMap, invFun, left_inv, map_smul_of_tower, right_inv, smul_smul, toLinearMap
-/
instance : SMul Sˣ (V ≃ₗ[R] W) where smul α e :=
  { __ := (α : S) • e.toLinearMap
    invFun x := (↑α⁻¹ : S) • e.symm x
    left_inv _ := by simp [LinearMapClass.map_smul_of_tower e.symm, smul_smul]
    right_inv _ := by simp [smul_smul] }

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (α : Sˣ) (e : V ≃ₗ[R] W) (x : V)
  statement: (α • e) x = (α : S) • e x
  proof: rfl

中文:
定理 smul_apply
  条件: (α : Sˣ) (e : V ≃ₗ[R] W) (x : V)
  结论: (α • e) x = (α : S) • e x
  证明: rfl
-/
@[simp] theorem smul_apply (α : Sˣ) (e : V ≃ₗ[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl

/--
theorem `symm_smul_apply` / 定理 `symm_smul_apply`

English:
theorem symm_smul_apply
  given: (e : V ≃ₗ[R] W) (α : Sˣ) (x : W)
  proof: rfl

中文:
定理 symm_smul_apply
  条件: (e : V ≃ₗ[R] W) (α : Sˣ) (x : W)
  证明: rfl
-/
theorem symm_smul_apply (e : V ≃ₗ[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl

/--
theorem `symm_smul` / 定理 `symm_smul`

English:
theorem symm_smul
  given: [SMulCommClass R S V] (e : V ≃ₗ[R] W) (α : Sˣ)
  proof: rfl

中文:
定理 symm_smul
  条件: [标量交换类 R S V] (e : V ≃ₗ[R] W) (α : Sˣ)
  证明: rfl
-/
@[simp] theorem symm_smul [SMulCommClass R S V] (e : V ≃ₗ[R] W) (α : Sˣ) :
    (α • e).symm = α⁻¹ • e.symm := rfl

/--
theorem `toLinearMap_smul` / 定理 `toLinearMap_smul`

English:
theorem toLinearMap_smul
  given: (e : V ≃ₗ[R] W) (α : Sˣ)
  proof: rfl

中文:
定理 toLinearMap_smul
  条件: (e : V ≃ₗ[R] W) (α : Sˣ)
  证明: rfl
-/
@[simp] theorem toLinearMap_smul (e : V ≃ₗ[R] W) (α : Sˣ) :
    (α • e).toLinearMap = (α : S) • e.toLinearMap := rfl

/--
theorem `smul_trans` / 定理 `smul_trans`

English:
theorem smul_trans
  statement: [SMulCommClass R S V] [IsScalarTower S R G]
  proof: by ext; simp [LinearMapClass.map_smul_of_tower f]

中文:
定理 smul_trans
  结论: [标量交换类 R S V] [标量塔 S R G]
  证明: by ext; simp [LinearMapClass.map_smul_of_tower f]

Depends on / 依赖: LinearMapClass, LinearMapClass.map_smul_of_tower, map_smul_of_tower
-/
theorem smul_trans [SMulCommClass R S V] [IsScalarTower S R G]
    (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) :
    (α • e).trans f = α • (e.trans f) := by ext; simp [LinearMapClass.map_smul_of_tower f]

/--
theorem `trans_smul` / 定理 `trans_smul`

English:
theorem trans_smul
  statement: [IsScalarTower S R G]
  proof: by ext; simp

中文:
定理 trans_smul
  结论: [标量塔 S R G]
  证明: by ext; simp
-/
theorem trans_smul [IsScalarTower S R G]
    (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

end smul
end LinearEquiv
