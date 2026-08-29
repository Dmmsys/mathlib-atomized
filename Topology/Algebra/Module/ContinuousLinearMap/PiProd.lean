/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps on products and Pi types

In this file, we collect various constructions relating continuous linear maps with (binary or
arbitrary) products.

## Main definitions

Binary products (viewed as categorical products):

* `ContinuousLinearMap.fst R M₁ M₂ : M₁ × M₂ →L[R] M₁` and
  `ContinuousLinearMap.snd R M₁ M₂ : M₁ × M₂ →L[R] M₂` are the two projections, given
  respectively by `fst (x, y) = x` and `snd (x, y) = y`. These are the continuous versions
  of `LinearMap.fst` and `LinearMap.snd`.
* `ContinuousLinearMap.prod f₁ f₂` is the continuous linear map `M →L[R] N₁ × N₂` given by two
  continuous linear maps `f₁ : M →L[R] N₁` and `f₂ : M →L[R] N₂`. This is the continuous version
  of `LinearMap.prod`.
* `ContinuousLinearMap.prodEquiv` shows that the above is a bijection: every continuous linear
  map to a product is obtained this way. In other words, this is the universal property of the
  product.
* `ContinuousLinearMap.prodMap f₁ f₂` is the continuous linear map `M₁ × M₂ →L[R] N₁ × N₂` given by
  two continuous linear maps `f₁ : M₁ →L[R] N₁` and `f₂ : M₂ →L[R] N₂`. This is the continuous
  version of `LinearMap.prodMap`.

Binary products (viewed as categorical coproducts):

* `ContinuousLinearMap.inl R M₁ M₂ : M₁ →L[R] M₁ × M₂` and
  `ContinuousLinearMap.inr R M₁ M₂ : M₂ →L[R] M₁ × M₂` are the two inclusions, given
  respectively by `inl x = (x, 0)` and `inr x = (0, x)`. These are the continuous versions
  of `LinearMap.inl` and `LinearMap.inr`.
* `ContinuousLinearMap.coprod f₁ f₂` is the continuous linear map ` M₁ × M₂ →L[R] N` given by
  two continuous linear maps `f₁ : M₁ →L[R] N` and `f₂ : M₂ →L[R] N`. This is the continuous
  version of `LinearMap.coprod`.
* `ContinuousLinearMap.coprodEquiv` shows that the above is a bijection: every continuous linear
  map from a (binary) product is obtained this way. In other words, this is the universal property
  of the coproduct.

Indexed products:

* `ContinuousLinearMap.pi f` is the continuous linear map `M →L[R] (Π i, N i)` given by a family
  `f₁ : Π i, M →L[R] N i` of continuous linear maps. This is the continuous version
  of `LinearMap.pi`.
* `ContinuousLinearMap.piMap f` is the continuous linear map `(Π i, M i) →L[R] (Π i, N i)` given by
  a family `f : Π i, M i →L[R] N i` of continuous linear maps. This is the continuous
  version of `LinearMap.piMap`.
* `ContinuousLinearMap.proj j : (Π i, M i) →L[R] M j` is the projection given by
  `proj i f = f i`. This is the continuous version of `LinearMap.proj`.
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable
  {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃)
  body: .prod f₁ f₂

@[simp, norm_cast]

中文:
定义 乘积
  签名: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃)
  定义体: .prod f₁ f₂

@[simp, norm_cast]
-/
protected def prod (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) :
    M₁ ->L[R] M₂ × M₃ where
  toLinearMap := .prod f₁ f₂

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_prod
  条件: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_prod (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) :
    (f₁.prod f₂ : M₁ ->ₗ[R] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) (x : M₁)
  proof: rfl

中文:
定理 prod_apply
  条件: (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) (x : M₁)
  证明: rfl
-/
theorem prod_apply (f₁ : M₁ ->L[R] M₂) (f₂ : M₁ ->L[R] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section

variable (R M₁ M₂)

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : M₁ ->L[R] M₁ × M₂
  body: (ContinuousLinearMap.id R M₁).prod 0

中文:
定义 inl
  签名: : M₁ ->L[R] M₁ × M₂
  定义体: (ContinuousLinearMap.id R M₁).prod 0

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id
-/
def inl : M₁ ->L[R] M₁ × M₂ :=
  (ContinuousLinearMap.id R M₁).prod 0

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : M₂ ->L[R] M₁ × M₂
  body: (0 : M₂ ->L[R] M₁).prod (.id R M₂)

中文:
定义 inr
  签名: : M₂ ->L[R] M₁ × M₂
  定义体: (0 : M₂ ->L[R] M₁).prod (.id R M₂)
-/
def inr : M₂ ->L[R] M₁ × M₂ :=
  (0 : M₂ ->L[R] M₁).prod (.id R M₂)

end

@[simp]
/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x : M₁)
  statement: inl R M₁ M₂ x = (x, 0)
  proof: rfl

@[simp]

中文:
定理 inl_apply
  条件: (x : M₁)
  结论: inl R M₁ M₂ x = (x, 0)
  证明: rfl

@[simp]
-/
theorem inl_apply (x : M₁) : inl R M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (x : M₂)
  statement: inr R M₁ M₂ x = (0, x)
  proof: rfl

@[simp, norm_cast]

中文:
定理 inr_apply
  条件: (x : M₂)
  结论: inr R M₁ M₂ x = (0, x)
  证明: rfl

@[simp, norm_cast]
-/
theorem inr_apply (x : M₂) : inr R M₁ M₂ x = (0, x) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inl` / 定理 `coe_inl`

English:
theorem coe_inl
  statement: (inl R M₁ M₂ : M₁ ->ₗ[R] M₁ × M₂) = LinearMap.inl R M₁ M₂
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inl
  结论: (inl R M₁ M₂ : M₁ ->ₗ[R] M₁ × M₂) = 线性映射.inl R M₁ M₂
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inl : (inl R M₁ M₂ : M₁ ->ₗ[R] M₁ × M₂) = LinearMap.inl R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inr` / 定理 `coe_inr`

English:
theorem coe_inr
  statement: (inr R M₁ M₂ : M₂ ->ₗ[R] M₁ × M₂) = LinearMap.inr R M₁ M₂
  proof: rfl

中文:
定理 coe_inr
  结论: (inr R M₁ M₂ : M₂ ->ₗ[R] M₁ × M₂) = 线性映射.inr R M₁ M₂
  证明: rfl
-/
theorem coe_inr : (inr R M₁ M₂ : M₂ ->ₗ[R] M₁ × M₂) = LinearMap.inr R M₁ M₂ :=
  rfl

/--
lemma `comp_inl_add_comp_inr` / 引理 `comp_inl_add_comp_inr`

English:
lemma comp_inl_add_comp_inr
  given: (L : M₁ × M₂ ->L[R] M₃) (v : M₁ × M₂)
  proof: by simp [← map_add]

中文:
引理 comp_inl_add_comp_inr
  条件: (L : M₁ × M₂ ->L[R] M₃) (v : M₁ × M₂)
  证明: by simp [← map_add]

Depends on / 依赖: map_add
-/
lemma comp_inl_add_comp_inr (L : M₁ × M₂ ->L[R] M₃) (v : M₁ × M₂) :
    L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M₂) v.2 = L v := by simp [← map_add]

/--
theorem `ker_prod` / 定理 `ker_prod`

English:
theorem ker_prod
  given: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  proof: by
  simp

中文:
定理 ker_prod
  条件: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  证明: by
  simp
-/
theorem ker_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) :
    ker (f.prod g : M₁ ->ₗ[R] M₂ × M₃) = ker (f : M₁ ->ₗ[R] M₂) ⊓ ker (g : M₁ ->ₗ[R] M₃) := by
  simp

variable (R M₁ M₂)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : M₁ × M₂ ->L[R] M₁ where
  body: LinearMap.fst R M₁ M₂

中文:
定义 fst
  签名: : M₁ × M₂ ->L[R] M₁ where
  定义体: LinearMap.fst R M₁ M₂

Depends on / 依赖: LinearMap, LinearMap.fst
-/
def fst : M₁ × M₂ ->L[R] M₁ where
  toLinearMap := LinearMap.fst R M₁ M₂

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : M₁ × M₂ ->L[R] M₂ where
  body: LinearMap.snd R M₁ M₂

中文:
定义 snd
  签名: : M₁ × M₂ ->L[R] M₂ where
  定义体: LinearMap.snd R M₁ M₂

Depends on / 依赖: LinearMap, LinearMap.snd
-/
def snd : M₁ × M₂ ->L[R] M₂ where
  toLinearMap := LinearMap.snd R M₁ M₂

variable {R M₁ M₂}

@[simp, norm_cast]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ↑(fst R M₁ M₂) = LinearMap.fst R M₁ M₂
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_fst
  结论: ↑(fst R M₁ M₂) = 线性映射.fst R M₁ M₂
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_fst : ↑(fst R M₁ M₂) = LinearMap.fst R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_fst'` / 定理 `coe_fst'`

English:
theorem coe_fst'
  statement: ⇑(fst R M₁ M₂) = Prod.fst
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_fst'
  结论: ⇑(fst R M₁ M₂) = 积类型.fst
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_fst' : ⇑(fst R M₁ M₂) = Prod.fst :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_snd
  结论: ↑(snd R M₁ M₂) = 线性映射.snd R M₁ M₂
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_snd : ↑(snd R M₁ M₂) = LinearMap.snd R M₁ M₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_snd'` / 定理 `coe_snd'`

English:
theorem coe_snd'
  statement: ⇑(snd R M₁ M₂) = Prod.snd
  proof: rfl

@[simp]

中文:
定理 coe_snd'
  结论: ⇑(snd R M₁ M₂) = 积类型.snd
  证明: rfl

@[simp]
-/
theorem coe_snd' : ⇑(snd R M₁ M₂) = Prod.snd :=
  rfl

@[simp]
/--
theorem `fst_prod_snd` / 定理 `fst_prod_snd`

English:
theorem fst_prod_snd
  statement: (fst R M₁ M₂).prod (snd R M₁ M₂) = .id R (M₁ × M₂)
  proof: ext fun ⟨_x, _y⟩ => rfl

@[simp]

中文:
定理 fst_prod_snd
  结论: (fst R M₁ M₂).乘积 (snd R M₁ M₂) = .id R (M₁ × M₂)
  证明: ext fun ⟨_x, _y⟩ => rfl

@[simp]
-/
theorem fst_prod_snd : (fst R M₁ M₂).prod (snd R M₁ M₂) = .id R (M₁ × M₂) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  given: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  proof: ext fun _x => rfl

@[simp]

中文:
定理 fst_comp_prod
  条件: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  证明: ext fun _x => rfl

@[simp]
-/
theorem fst_comp_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) :
    (fst R M₂ M₃).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  given: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  proof: ext fun _x => rfl

中文:
定理 snd_comp_prod
  条件: (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃)
  证明: ext fun _x => rfl
-/
theorem snd_comp_prod (f : M₁ ->L[R] M₂) (g : M₁ ->L[R] M₃) :
    (snd R M₂ M₃).comp (f.prod g) = g :=
  ext fun _x => rfl

/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: fst R M₁ M₂ ∘L inl R M₁ M₂ = .id R M₁
  proof: rfl

中文:
定理 fst_comp_inl
  结论: fst R M₁ M₂ ∘L inl R M₁ M₂ = .id R M₁
  证明: rfl
-/
@[simp] theorem fst_comp_inl : fst R M₁ M₂ ∘L inl R M₁ M₂ = .id R M₁ := rfl
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: fst R M₁ M₂ ∘L inr R M₁ M₂ = 0
  proof: rfl

中文:
定理 fst_comp_inr
  结论: fst R M₁ M₂ ∘L inr R M₁ M₂ = 0
  证明: rfl
-/
@[simp] theorem fst_comp_inr : fst R M₁ M₂ ∘L inr R M₁ M₂ = 0 := rfl
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: snd R M₁ M₂ ∘L inl R M₁ M₂ = 0
  proof: rfl

中文:
定理 snd_comp_inl
  结论: snd R M₁ M₂ ∘L inl R M₁ M₂ = 0
  证明: rfl
-/
@[simp] theorem snd_comp_inl : snd R M₁ M₂ ∘L inl R M₁ M₂ = 0 := rfl
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: snd R M₁ M₂ ∘L inr R M₁ M₂ = .id R M₂
  proof: rfl

中文:
定理 snd_comp_inr
  结论: snd R M₁ M₂ ∘L inr R M₁ M₂ = .id R M₂
  证明: rfl
-/
@[simp] theorem snd_comp_inr : snd R M₁ M₂ ∘L inr R M₁ M₂ = .id R M₂ := rfl

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄)
  body: (f₁.comp (fst R M₁ M₃)).prod (f₂.comp (snd R M₁ M₃))

@[simp, norm_cast]

中文:
定义 prodMap
  签名: (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄)
  定义体: (f₁.comp (fst R M₁ M₃)).prod (f₂.comp (snd R M₁ M₃))

@[simp, norm_cast]
-/
def prodMap (f₁ : M₁ ->L[R] M₂) (f₂ : M₃ ->L[R] M₄) :
    M₁ × M₃ ->L[R] M₂ × M₄ :=
  (f₁.comp (fst R M₁ M₃)).prod (f₂.comp (snd R M₁ M₃))

@[simp, norm_cast]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: (f₁ : M₁ ->L[R] M₂)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_prodMap
  结论: (f₁ : M₁ ->L[R] M₂)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_prodMap (f₁ : M₁ ->L[R] M₂)
    (f₂ : M₃ ->L[R] M₄) : ↑(f₁.prodMap f₂) = (f₁ : M₁ ->ₗ[R] M₂).prodMap (f₂ : M₃ ->ₗ[R] M₄) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_prodMap'` / 定理 `coe_prodMap'`

English:
theorem coe_prodMap'
  statement: (f₁ : M₁ ->L[R] M₂)
  proof: rfl

中文:
定理 coe_prodMap'
  结论: (f₁ : M₁ ->L[R] M₂)
  证明: rfl
-/
theorem coe_prodMap' (f₁ : M₁ ->L[R] M₂)
    (f₂ : M₃ ->L[R] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

end Semiring

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι -> Type*}
  [forall i, TopologicalSpace (φ i)] [forall i, AddCommMonoid (φ i)] [forall i, Module R (φ i)]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : forall i, M ->L[R] φ i)
  body: .pi fun i => f i

@[simp]

中文:
定义 pi
  签名: (f : 对任意 i, M ->L[R] φ i)
  定义体: .pi fun i => f i

@[simp]
-/
def pi (f : forall i, M ->L[R] φ i) : M ->L[R] forall i, φ i where
  toLinearMap := .pi fun i => f i

@[simp]
/--
theorem `coe_pi'` / 定理 `coe_pi'`

English:
theorem coe_pi'
  given: (f : forall i, M ->L[R] φ i)
  statement: ⇑(pi f) = fun c i => f i c
  proof: rfl

@[simp]

中文:
定理 coe_pi'
  条件: (f : 对任意 i, M ->L[R] φ i)
  结论: ⇑(pi f) = fun c i => f i c
  证明: rfl

@[simp]
-/
theorem coe_pi' (f : forall i, M ->L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl

@[simp]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  given: (f : forall i, M ->L[R] φ i)
  statement: (pi f : M ->ₗ[R] forall i, φ i) = LinearMap.pi fun i => f i
  proof: rfl

中文:
定理 coe_pi
  条件: (f : 对任意 i, M ->L[R] φ i)
  结论: (pi f : M ->ₗ[R] 对任意 i, φ i) = 线性映射.pi fun i => f i
  证明: rfl
-/
theorem coe_pi (f : forall i, M ->L[R] φ i) : (pi f : M ->ₗ[R] forall i, φ i) = LinearMap.pi fun i => f i :=
  rfl

/--
theorem `pi_apply` / 定理 `pi_apply`

English:
theorem pi_apply
  given: (f : forall i, M ->L[R] φ i) (c : M) (i : ι)
  statement: pi f c i = f i c
  proof: rfl

中文:
定理 pi_apply
  条件: (f : 对任意 i, M ->L[R] φ i) (c : M) (i : ι)
  结论: pi f c i = f i c
  证明: rfl
-/
theorem pi_apply (f : forall i, M ->L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl

/--
theorem `pi_eq_zero` / 定理 `pi_eq_zero`

English:
theorem pi_eq_zero
  given: (f : forall i, M ->L[R] φ i)
  statement: pi f = 0 ↔ forall i, f i = 0
  proof: by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_comm

中文:
定理 pi_eq_zero
  条件: (f : 对任意 i, M ->L[R] φ i)
  结论: pi f = 0 ↔ 对任意 i, f i = 0
  证明: by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_comm

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, ext_iff, forall_comm, funext_iff, pi_apply
-/
theorem pi_eq_zero (f : forall i, M ->L[R] φ i) : pi f = 0 ↔ forall i, f i = 0 := by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_comm

/--
theorem `pi_zero` / 定理 `pi_zero`

English:
theorem pi_zero
  statement: pi (fun _ => 0 : forall i, M ->L[R] φ i) = 0
  proof: ext fun _ => rfl

中文:
定理 pi_zero
  结论: pi (fun _ => 0 : 对任意 i, M ->L[R] φ i) = 0
  证明: ext fun _ => rfl
-/
theorem pi_zero : pi (fun _ => 0 : forall i, M ->L[R] φ i) = 0 :=
  ext fun _ => rfl

/--
theorem `pi_comp` / 定理 `pi_comp`

English:
theorem pi_comp
  given: (f : forall i, M ->L[R] φ i) (g : M₂ ->L[R] M)
  proof: rfl

中文:
定理 pi_comp
  条件: (f : 对任意 i, M ->L[R] φ i) (g : M₂ ->L[R] M)
  证明: rfl
-/
theorem pi_comp (f : forall i, M ->L[R] φ i) (g : M₂ ->L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : ι)
  body: .proj i

@[simp]

中文:
定义 proj
  签名: (i : ι)
  定义体: .proj i

@[simp]
-/
def proj (i : ι) : (forall i, φ i) ->L[R] φ i where
  toLinearMap := .proj i

@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (i : ι) (b : forall i, φ i)
  statement: (proj i : (forall i, φ i) ->L[R] φ i) b = b i
  proof: rfl

@[simp]

中文:
定理 proj_apply
  条件: (i : ι) (b : 对任意 i, φ i)
  结论: (proj i : (对任意 i, φ i) ->L[R] φ i) b = b i
  证明: rfl

@[simp]
-/
theorem proj_apply (i : ι) (b : forall i, φ i) : (proj i : (forall i, φ i) ->L[R] φ i) b = b i :=
  rfl

@[simp]
/--
theorem `proj_pi` / 定理 `proj_pi`

English:
theorem proj_pi
  given: (f : forall i, M₂ ->L[R] φ i) (i : ι)
  statement: (proj i).comp (pi f) = f i
  proof: rfl

@[simp]

中文:
定理 proj_pi
  条件: (f : 对任意 i, M₂ ->L[R] φ i) (i : ι)
  结论: (proj i).comp (pi f) = f i
  证明: rfl

@[simp]
-/
theorem proj_pi (f : forall i, M₂ ->L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
/--
theorem `coe_proj` / 定理 `coe_proj`

English:
theorem coe_proj
  given: (i : ι)
  statement: (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) -> φ i) ->ₗ[R] _)
  proof: rfl

@[simp]

中文:
定理 coe_proj
  条件: (i : ι)
  结论: (proj i).toLinearMap = (线性映射.proj i : ((i : ι) -> φ i) ->ₗ[R] _)
  证明: rfl

@[simp]
-/
theorem coe_proj (i : ι) : (proj i).toLinearMap = (LinearMap.proj i : ((i : ι) -> φ i) ->ₗ[R] _) :=
  rfl

@[simp]
/--
theorem `pi_proj` / 定理 `pi_proj`

English:
theorem pi_proj
  statement: pi proj = .id R (forall i, φ i)
  proof: rfl

@[simp]

中文:
定理 pi_proj
  结论: pi proj = .id R (对任意 i, φ i)
  证明: rfl

@[simp]
-/
theorem pi_proj : pi proj = .id R (forall i, φ i) := rfl

@[simp]
/--
theorem `pi_proj_comp` / 定理 `pi_proj_comp`

English:
theorem pi_proj_comp
  given: (f : M₂ ->L[R] forall i, φ i)
  statement: pi (proj · ∘L f) = f
  proof: rfl

中文:
定理 pi_proj_comp
  条件: (f : M₂ ->L[R] 对任意 i, φ i)
  结论: pi (proj · ∘L f) = f
  证明: rfl
-/
theorem pi_proj_comp (f : M₂ ->L[R] forall i, φ i) : pi (proj · ∘L f) = f := rfl

/--
theorem `iInf_ker_proj` / 定理 `iInf_ker_proj`

English:
theorem iInf_ker_proj
  proof: LinearMap.iInf_ker_proj

中文:
定理 iInf_ker_proj
  证明: LinearMap.iInf_ker_proj

Depends on / 依赖: LinearMap, LinearMap.iInf_ker_proj, iInf_ker_proj
-/
theorem iInf_ker_proj :
    (⨅ i, ker (proj i : (forall i, φ i) ->L[R] φ i).toLinearMap : Submodule R (forall i, φ i)) = ⊥ :=
  LinearMap.iInf_ker_proj

section PiMap
variable {ψ : ι -> Type*} [forall i, TopologicalSpace (ψ i)] [forall i, AddCommMonoid (ψ i)]
  [forall i, Module R (ψ i)]

/--
Definition of `piMap` / `piMap` 的定义

English:
definition piMap
  signature: (f : forall i, φ i ->L[R] ψ i)
  body: .pi fun i => f i ∘L .proj i

@[simp]

中文:
定义 piMap
  签名: (f : 对任意 i, φ i ->L[R] ψ i)
  定义体: .pi fun i => f i ∘L .proj i

@[simp]
-/
def piMap (f : forall i, φ i ->L[R] ψ i) : (forall i, φ i) ->L[R] (forall i, ψ i) :=
  .pi fun i => f i ∘L .proj i

@[simp]
/--
theorem `coe_piMap` / 定理 `coe_piMap`

English:
theorem coe_piMap
  given: (f : forall i, φ i ->L[R] ψ i)
  proof: rfl

@[simp]

中文:
定理 coe_piMap
  条件: (f : 对任意 i, φ i ->L[R] ψ i)
  证明: rfl

@[simp]
-/
theorem coe_piMap (f : forall i, φ i ->L[R] ψ i) :
    (piMap f : (forall i, φ i) ->ₗ[R] (forall i, ψ i)) = .piMap fun i => f i :=
  rfl

@[simp]
/--
theorem `coe_piMap'` / 定理 `coe_piMap'`

English:
theorem coe_piMap'
  given: (f : forall i, φ i ->L[R] ψ i)
  statement: ⇑(piMap f) = Pi.map fun i => f i
  proof: rfl

中文:
定理 coe_piMap'
  条件: (f : 对任意 i, φ i ->L[R] ψ i)
  结论: ⇑(piMap f) = 依赖函数类型.map fun i => f i
  证明: rfl
-/
theorem coe_piMap' (f : forall i, φ i ->L[R] ψ i) : ⇑(piMap f) = Pi.map fun i => f i :=
  rfl

end PiMap

variable (R φ)

/--
Definition of `_root_.Pi.compRightL` / `_root_.Pi.compRightL` 的定义

English:
definition _root_.Pi.compRightL
  signature: {α : Type*} (f : α -> ι)
  body: fun v i => v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

中文:
定义 _root_.依赖函数类型.compRightL
  签名: {α : 类型} (f : α -> ι)
  定义体: fun v i => v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
-/
def _root_.Pi.compRightL {α : Type*} (f : α -> ι) : ((i : ι) -> φ i) ->L[R] ((i : α) -> φ (f i)) where
  toFun := fun v i => v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

/--
lemma `_root_.Pi.compRightL_apply` / 引理 `_root_.Pi.compRightL_apply`

English:
lemma _root_.Pi.compRightL_apply
  given: {α : Type*} (f : α -> ι) (v : (i : ι) -> φ i) (i : α)
  proof: rfl

中文:
引理 _root_.依赖函数类型.compRightL_apply
  条件: {α : 类型} (f : α -> ι) (v : (i : ι) -> φ i) (i : α)
  证明: rfl
-/
@[simp] lemma _root_.Pi.compRightL_apply {α : Type*} (f : α -> ι) (v : (i : ι) -> φ i) (i : α) :
    Pi.compRightL R φ f v i = v (f i) := rfl

/-- `Pi.single` as a bundled continuous linear map. -/
@[simps! -fullyApplied]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: [DecidableEq ι] (i : ι)
  body: .single R φ i

中文:
定义 single
  签名: [DecidableEq ι] (i : ι)
  定义体: .single R φ i

Depends on / 依赖: single
-/
def single [DecidableEq ι] (i : ι) : φ i ->L[R] (forall i, φ i) where
  toLinearMap := .single R φ i

/--
lemma `sum_comp_single` / 引理 `sum_comp_single`

English:
lemma sum_comp_single
  given: [Fintype ι] [DecidableEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i)
  proof: by
  simp [← map_sum, LinearMap.sum_single_apply]

中文:
引理 sum_comp_single
  条件: [有限类型 ι] [DecidableEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i)
  证明: by
  simp [← map_sum, LinearMap.sum_single_apply]

Depends on / 依赖: LinearMap, LinearMap.sum_single_apply, map_sum, sum_single_apply
-/
lemma sum_comp_single [Fintype ι] [DecidableEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i) :
    ∑ i, L.comp (.single R φ i) (v i) = L v := by
  simp [← map_sum, LinearMap.sum_single_apply]

end Pi

section Ring

variable {R : Type*} [Ring R]
  {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] [Module R M₃]

/--
theorem `range_prod_eq` / 定理 `range_prod_eq`

English:
theorem range_prod_eq
  given: {f : M ->L[R] M₂} {g : M ->L[R] M₃} (h : f.ker ⊔ g.ker = ⊤)
  proof: LinearMap.range_prod_eq h

中文:
定理 range_prod_eq
  条件: {f : M ->L[R] M₂} {g : M ->L[R] M₃} (h : f.ker ⊔ g.ker = ⊤)
  证明: LinearMap.range_prod_eq h

Depends on / 依赖: LinearMap, LinearMap.range_prod_eq, range_prod_eq
-/
theorem range_prod_eq {f : M ->L[R] M₂} {g : M ->L[R] M₃} (h : f.ker ⊔ g.ker = ⊤) :
    (f.prod g).range = f.range.prod g.range :=
  LinearMap.range_prod_eq h

/--
theorem `ker_prod_ker_le_ker_coprod` / 定理 `ker_prod_ker_le_ker_coprod`

English:
theorem ker_prod_ker_le_ker_coprod
  given: (f : M ->L[R] M₃) (g : M₂ ->L[R] M₃)
  proof: LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

中文:
定理 ker_prod_ker_le_ker_coprod
  条件: (f : M ->L[R] M₃) (g : M₂ ->L[R] M₃)
  证明: LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

Depends on / 依赖: LinearMap, LinearMap.ker_prod_ker_le_ker_coprod, f.toLinearMap, g.toLinearMap, ker_prod_ker_le_ker_coprod, toLinearMap
-/
theorem ker_prod_ker_le_ker_coprod (f : M ->L[R] M₃) (g : M₂ ->L[R] M₃) :
    f.ker.prod g.ker <= (f.coprod g).ker :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

end Ring

section SMul

variable
  {R : Type*} [Semiring R]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]

/-- `ContinuousLinearMap.prod` as an `Equiv`. -/
@[simps apply]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (M ->L[R] M₂) × (M ->L[R] M₃) ≃ (M ->L[R] M₂ × M₃) where
  body: f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩

中文:
定义 prodEquiv
  签名: : (M ->L[R] M₂) × (M ->L[R] M₃) ≃ (M ->L[R] M₂ × M₃) where
  定义体: f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
-/
def prodEquiv : (M ->L[R] M₂) × (M ->L[R] M₃) ≃ (M ->L[R] M₂ × M₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩

/--
theorem `prod_ext_iff` / 定理 `prod_ext_iff`

English:
theorem prod_ext_iff
  given: {f g : M × M₂ ->L[R] M₃}
  proof: by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]

中文:
定理 prod_ext_iff
  条件: {f g : M × M₂ ->L[R] M₃}
  证明: by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]

Depends on / 依赖: LinearMap, LinearMap.prod_ext_iff, coe_inj, prod_ext_iff
-/
theorem prod_ext_iff {f g : M × M₂ ->L[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]
/--
theorem `prod_ext` / 定理 `prod_ext`

English:
theorem prod_ext
  statement: {f g : M × M₂ ->L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  proof: prod_ext_iff.2 ⟨hl, hr⟩

中文:
定理 prod_ext
  结论: {f g : M × M₂ ->L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  证明: prod_ext_iff.2 ⟨hl, hr⟩

Depends on / 依赖: prod_ext_iff
-/
theorem prod_ext {f g : M × M₂ ->L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable (S : Type*) [Semiring S]
  [Module S M₂] [ContinuousAdd M₂] [SMulCommClass R S M₂] [ContinuousConstSMul S M₂]
  [Module S M₃] [ContinuousAdd M₃] [SMulCommClass R S M₃] [ContinuousConstSMul S M₃]

/-- `ContinuousLinearMap.prod` as a `LinearEquiv`.

See `ContinuousLinearMap.prodL` for the `ContinuousLinearEquiv` version. -/
@[simps apply]
/--
Definition of `prodₗ` / `prodₗ` 的定义

English:
definition prodₗ
  signature: : ((M ->L[R] M₂) × (M ->L[R] M₃)) ≃ₗ[S] M ->L[R] M₂ × M₃
  body: { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

中文:
定义 prodₗ
  签名: : ((M ->L[R] M₂) × (M ->L[R] M₃)) ≃ₗ[S] M ->L[R] M₂ × M₃
  定义体: { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

Depends on / 依赖: map_add, map_smul, prodEquiv
-/
def prodₗ : ((M ->L[R] M₂) × (M ->L[R] M₃)) ≃ₗ[S] M ->L[R] M₂ × M₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

end SMul

section coprod

variable {R S M N M₁ M₂ : Type*}
  [Semiring R] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace M₁] [TopologicalSpace M₂]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] [ContinuousAdd M] [AddCommMonoid N] [Module R N]
  [ContinuousAdd N] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
@[simps! coe apply]
/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  body: .coprod f₁ f₂

中文:
定义 coprod
  签名: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  定义体: .coprod f₁ f₂

Depends on / 依赖: coprod
-/
def coprod (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) : M₁ × M₂ ->L[R] M where
  toLinearMap := .coprod f₁ f₂

/--
lemma `coprod_add` / 引理 `coprod_add`

English:
lemma coprod_add
  given: (f₁ g₁ : M₁ ->L[R] M) (f₂ g₂ : M₂ ->L[R] M)
  proof: by ext <;> simp

中文:
引理 coprod_add
  条件: (f₁ g₁ : M₁ ->L[R] M) (f₂ g₂ : M₂ ->L[R] M)
  证明: by ext <;> simp
-/
@[simp] lemma coprod_add (f₁ g₁ : M₁ ->L[R] M) (f₂ g₂ : M₂ ->L[R] M) :
    (f₁ + g₁).coprod (f₂ + g₂) = f₁.coprod f₂ + g₁.coprod g₂ := by ext <;> simp

/--
lemma `range_coprod` / 引理 `range_coprod`

English:
lemma range_coprod
  given: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  proof: LinearMap.range_coprod ..

中文:
引理 range_coprod
  条件: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  证明: LinearMap.range_coprod ..

Depends on / 依赖: LinearMap, LinearMap.range_coprod, range_coprod
-/
lemma range_coprod (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) :
    (f₁.coprod f₂).range = f₁.range ⊔ f₂.range := LinearMap.range_coprod ..

/--
lemma `comp_fst_add_comp_snd` / 引理 `comp_fst_add_comp_snd`

English:
lemma comp_fst_add_comp_snd
  given: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  proof: rfl

中文:
引理 comp_fst_add_comp_snd
  条件: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  证明: rfl
-/
lemma comp_fst_add_comp_snd (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) :
    f₁.comp (.fst _ _ _) + f₂.comp (.snd _ _ _) = f₁.coprod f₂ := rfl

/--
lemma `comp_coprod` / 引理 `comp_coprod`

English:
lemma comp_coprod
  given: (f : M ->L[R] N) (g₁ : M₁ ->L[R] M) (g₂ : M₂ ->L[R] M)
  proof: coe_injective LinearMap.comp_coprod ..

中文:
引理 comp_coprod
  条件: (f : M ->L[R] N) (g₁ : M₁ ->L[R] M) (g₂ : M₂ ->L[R] M)
  证明: coe_injective LinearMap.comp_coprod ..

Depends on / 依赖: LinearMap, LinearMap.comp_coprod, coe_injective, comp_coprod
-/
lemma comp_coprod (f : M ->L[R] N) (g₁ : M₁ ->L[R] M) (g₂ : M₂ ->L[R] M) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
coe_injective LinearMap.comp_coprod ..

/--
lemma `coprod_comp_inl` / 引理 `coprod_comp_inl`

English:
lemma coprod_comp_inl
  given: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  proof: coe_injective LinearMap.coprod_inl ..

中文:
引理 coprod_comp_inl
  条件: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  证明: coe_injective LinearMap.coprod_inl ..
-/
@[simp] lemma coprod_comp_inl (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) :
(f₁.coprod f₂).comp (.inl _ _ _) = f₁ := coe_injective LinearMap.coprod_inl ..

/--
lemma `coprod_comp_inr` / 引理 `coprod_comp_inr`

English:
lemma coprod_comp_inr
  given: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  proof: coe_injective LinearMap.coprod_inr ..

@[simp]

中文:
引理 coprod_comp_inr
  条件: (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M)
  证明: coe_injective LinearMap.coprod_inr ..

@[simp]
-/
@[simp] lemma coprod_comp_inr (f₁ : M₁ ->L[R] M) (f₂ : M₂ ->L[R] M) :
(f₁.coprod f₂).comp (.inr _ _ _) = f₂ := coe_injective LinearMap.coprod_inr ..

@[simp]
/--
lemma `coprod_inl_inr` / 引理 `coprod_inl_inr`

English:
lemma coprod_inl_inr
  statement: ContinuousLinearMap.coprod (.inl R M N) (.inr R M N) = .id R (M × N)
  proof: coe_injective LinearMap.coprod_inl_inr

@[simp]

中文:
引理 coprod_inl_inr
  结论: 连续线性映射.coprod (.inl R M N) (.inr R M N) = .id R (M × N)
  证明: coe_injective LinearMap.coprod_inl_inr

@[simp]

Depends on / 依赖: LinearMap, LinearMap.coprod_inl_inr, coe_injective, coprod_inl_inr
-/
lemma coprod_inl_inr : ContinuousLinearMap.coprod (.inl R M N) (.inr R M N) = .id R (M × N) :=
coe_injective LinearMap.coprod_inl_inr

@[simp]
/--
lemma `coprod_comp_inl_inr` / 引理 `coprod_comp_inl_inr`

English:
lemma coprod_comp_inl_inr
  given: [ContinuousAdd M₁] [ContinuousAdd M₂] (f : M × M₁ ->L[R] M₂)
  proof: by
  rw [← ContinuousLinearMap.comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

中文:
引理 coprod_comp_inl_inr
  条件: [连续加法 M₁] [连续加法 M₂] (f : M × M₁ ->L[R] M₂)
  证明: by
  rw [← ContinuousLinearMap.comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_coprod, comp_coprod, comp_id, coprod_inl_inr
-/
lemma coprod_comp_inl_inr [ContinuousAdd M₁] [ContinuousAdd M₂] (f : M × M₁ ->L[R] M₂) :
    (f ∘L .inl R M M₁).coprod (f ∘L .inr R M M₁) = f := by
  rw [← ContinuousLinearMap.comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.

See `ContinuousLinearMap.coprodEquivL` for the `ContinuousLinearEquiv` version.
-/
@[simps]
/--
Definition of `coprodEquiv` / `coprodEquiv` 的定义

English:
definition coprodEquiv
  signature: [ContinuousAdd M₁] [ContinuousAdd M₂] [Semiring S] [Module S M]
  body: f.1.coprod f.2
  invFun f := (f.comp (.inl ..), f.comp (.inr ..))
  left_inv f := by simp
  right_inv f := by simp [← comp_coprod f (.inl R M₁ M₂)]
  map_add' a b := coprod_add ..
  map_smul' r a := by
    dsimp
    ext <;> simp [smul_apply]

中文:
定义 coprodEquiv
  签名: [连续加法 M₁] [连续加法 M₂] [半环 S] [模 S M]
  定义体: f.1.coprod f.2
  invFun f := (f.comp (.inl ..), f.comp (.inr ..))
  left_inv f := by simp
  right_inv f := by simp [← comp_coprod f (.inl R M₁ M₂)]
  map_add' a b := coprod_add ..
  map_smul' r a := by
    dsimp
    ext <;> simp [smul_apply]

Depends on / 依赖: coprod
-/
def coprodEquiv [ContinuousAdd M₁] [ContinuousAdd M₂] [Semiring S] [Module S M]
    [ContinuousConstSMul S M] [SMulCommClass R S M] :
    ((M₁ ->L[R] M) × (M₂ ->L[R] M)) ≃ₗ[S] M₁ × M₂ ->L[R] M where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (.inl ..), f.comp (.inr ..))
  left_inv f := by simp
  right_inv f := by simp [← comp_coprod f (.inl R M₁ M₂)]
  map_add' a b := coprod_add ..
  map_smul' r a := by
    dsimp
    ext <;> simp [smul_apply]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] [ContinuousAdd M] [AddCommMonoid M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

/--
lemma `ker_coprod_of_disjoint_range` / 引理 `ker_coprod_of_disjoint_range`

English:
lemma ker_coprod_of_disjoint_range
  statement: {f₁ : M₁ ->L[R] M} {f₂ : M₂ ->L[R] M}
  proof: LinearMap.ker_coprod_of_disjoint_range f₁.toLinearMap f₂.toLinearMap hf

中文:
引理 ker_coprod_of_disjoint_range
  结论: {f₁ : M₁ ->L[R] M} {f₂ : M₂ ->L[R] M}
  证明: LinearMap.ker_coprod_of_disjoint_range f₁.toLinearMap f₂.toLinearMap hf

Depends on / 依赖: LinearMap, LinearMap.ker_coprod_of_disjoint_range, ker_coprod_of_disjoint_range, toLinearMap
-/
lemma ker_coprod_of_disjoint_range {f₁ : M₁ ->L[R] M} {f₂ : M₂ ->L[R] M}
    (hf : Disjoint f₁.range f₂.range) :
    (f₁.coprod f₂).ker = f₁.ker.prod f₂.ker :=
  LinearMap.ker_coprod_of_disjoint_range f₁.toLinearMap f₂.toLinearMap hf

end AddCommGroup

end coprod

end ContinuousLinearMap
