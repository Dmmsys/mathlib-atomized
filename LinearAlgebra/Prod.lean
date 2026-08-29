/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Group.Graph
public import Mathlib.LinearAlgebra.Span.Basic

/-! ### Products of modules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `Submodule.prod`, `Submodule.map`,
`Submodule.comap`, `LinearMap.range`, and `LinearMap.ker`.

## Main definitions

- products in the domain:
  - `LinearMap.fst`
  - `LinearMap.snd`
  - `LinearMap.coprod`
  - `LinearMap.prod_ext`
- products in the codomain:
  - `LinearMap.inl`
  - `LinearMap.inr`
  - `LinearMap.prod`
- products in both domain and codomain:
  - `LinearMap.prodMap`
  - `LinearEquiv.prodMap`
  - `LinearEquiv.skewProd`
- product with the trivial module:
  - `LinearEquiv.prodUnique`
  - `LinearEquiv.uniqueProd`
-/

@[expose] public section


universe u v w x y z u' v' w' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}
variable {M₅ M₆ : Type*}

section Prod

namespace LinearMap

variable (S : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid M₅] [AddCommMonoid M₆]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]
variable [Module R M₅] [Module R M₆]
variable (f : M ->ₗ[R] M₂)

section

variable (R M M₂)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : M × M₂ ->ₗ[R] M where
  body: Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

中文:
定义 fst
  签名: : M × M₂ ->ₗ[R] M where
  定义体: Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

Depends on / 依赖: Prod.fst
-/
def fst : M × M₂ ->ₗ[R] M where
  toFun := Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : M × M₂ ->ₗ[R] M₂ where
  body: Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

中文:
定义 snd
  签名: : M × M₂ ->ₗ[R] M₂ where
  定义体: Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

Depends on / 依赖: Prod.snd
-/
def snd : M × M₂ ->ₗ[R] M₂ where
  toFun := Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

end

@[simp]
/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: (x : M × M₂)
  statement: fst R M M₂ x = x.1
  proof: rfl

@[simp]

中文:
定理 fst_apply
  条件: (x : M × M₂)
  结论: fst R M M₂ x = x.1
  证明: rfl

@[simp]
-/
theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 :=
  rfl

@[simp]
/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: (x : M × M₂)
  statement: snd R M M₂ x = x.2
  proof: rfl

中文:
定理 snd_apply
  条件: (x : M × M₂)
  结论: snd R M M₂ x = x.2
  证明: rfl
-/
theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 :=
  rfl

/--
lemma `coe_fst` / 引理 `coe_fst`

English:
lemma coe_fst
  statement: ⇑(fst R M M₂) = Prod.fst
  proof: rfl

中文:
引理 coe_fst
  结论: ⇑(fst R M M₂) = 积类型.fst
  证明: rfl
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst R M M₂) = Prod.fst := rfl

/--
lemma `coe_snd` / 引理 `coe_snd`

English:
lemma coe_snd
  statement: ⇑(snd R M M₂) = Prod.snd
  proof: rfl

中文:
引理 coe_snd
  结论: ⇑(snd R M M₂) = 积类型.snd
  证明: rfl
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd R M M₂) = Prod.snd := rfl

/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  statement: Function.Surjective (fst R M M₂)
  proof: fun x => ⟨(x, 0), rfl⟩

中文:
定理 fst_surjective
  结论: 函数.满射 (fst R M M₂)
  证明: fun x => ⟨(x, 0), rfl⟩
-/
theorem fst_surjective : Function.Surjective (fst R M M₂) := fun x => ⟨(x, 0), rfl⟩

/--
theorem `snd_surjective` / 定理 `snd_surjective`

English:
theorem snd_surjective
  statement: Function.Surjective (snd R M M₂)
  proof: fun x => ⟨(0, x), rfl⟩

中文:
定理 snd_surjective
  结论: 函数.满射 (snd R M M₂)
  证明: fun x => ⟨(0, x), rfl⟩
-/
theorem snd_surjective : Function.Surjective (snd R M M₂) := fun x => ⟨(0, x), rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The prod of two linear maps is a linear map. -/
@[simps]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  body: Function.prod f g
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Function.prod_apply, Prod.smul_mk, map_smul, RingHom.id_apply]

中文:
定义 乘积
  签名: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  定义体: Function.prod f g
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Function.prod_apply, Prod.smul_mk, map_smul, RingHom.id_apply]

Depends on / 依赖: Function, Function.prod
-/
def prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : M ->ₗ[R] M₂ × M₃ where
  toFun := Function.prod f g
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Function.prod_apply, Prod.smul_mk, map_smul, RingHom.id_apply]

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  结论: ⇑(f.乘积 g) = 函数.乘积 f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  statement: (fst R M₂ M₃).comp (prod f g) = f
  proof: rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  结论: (fst R M₂ M₃).comp (乘积 f g) = f
  证明: rfl

@[simp]
-/
theorem fst_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (fst R M₂ M₃).comp (prod f g) = f := rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  statement: (snd R M₂ M₃).comp (prod f g) = g
  proof: rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  结论: (snd R M₂ M₃).comp (乘积 f g) = g
  证明: rfl

@[simp]
-/
theorem snd_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (snd R M₂ M₃).comp (prod f g) = g := rfl

@[simp]
/--
theorem `pair_fst_snd` / 定理 `pair_fst_snd`

English:
theorem pair_fst_snd
  statement: prod (fst R M M₂) (snd R M M₂) = LinearMap.id
  proof: rfl

中文:
定理 pair_fst_snd
  结论: 乘积 (fst R M M₂) (snd R M M₂) = 线性映射.id
  证明: rfl

Depends on / 依赖: instIsOpenPosMeasure, prod.instIsOpenPosMeasure
-/
theorem pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = LinearMap.id := rfl

/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  statement: (f : M₂ ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  proof: rfl

中文:
定理 prod_comp
  结论: (f : M₂ ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  证明: rfl
-/
theorem prod_comp (f : M₂ ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
    (h : M ->ₗ[R] M₂) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClass R S M₃]
  body: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 prodEquiv
  签名: [模 S M₂] [模 S M₃] [标量交换类 R S M₂] [标量交换类 R S M₃]
  定义体: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: instIsLocallyFiniteMeasure, prod.instIsLocallyFiniteMeasure
-/
def prodEquiv [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClass R S M₃] :
    ((M ->ₗ[R] M₂) × (M ->ₗ[R] M₃)) ≃ₗ[S] M ->ₗ[R] M₂ × M₃ where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section

variable (R M M₂)

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : M ->ₗ[R] M × M₂
  body: prod LinearMap.id 0

中文:
定义 inl
  签名: : M ->ₗ[R] M × M₂
  定义体: prod LinearMap.id 0

Depends on / 依赖: LinearMap, LinearMap.id
-/
def inl : M ->ₗ[R] M × M₂ :=
  prod LinearMap.id 0

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : M₂ ->ₗ[R] M × M₂
  body: prod 0 LinearMap.id

中文:
定义 inr
  签名: : M₂ ->ₗ[R] M × M₂
  定义体: prod 0 LinearMap.id

Depends on / 依赖: LinearMap, LinearMap.id, instIsFiniteMeasure, prod.instIsFiniteMeasure
-/
def inr : M₂ ->ₗ[R] M × M₂ :=
  prod 0 LinearMap.id

/--
theorem `range_inl` / 定理 `range_inl`

English:
theorem range_inl
  statement: range (inl R M M₂) = ker (snd R M M₂)
  proof: by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.fst, Prod.ext rfl h.symm⟩

中文:
定理 range_inl
  结论: range (inl R M M₂) = ker (snd R M M₂)
  证明: by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.fst, Prod.ext rfl h.symm⟩

Depends on / 依赖: Prod.ext, h.symm, mem_ker, mem_range, x.fst
-/
theorem range_inl : range (inl R M M₂) = ker (snd R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.fst, Prod.ext rfl h.symm⟩

/--
theorem `ker_snd` / 定理 `ker_snd`

English:
theorem ker_snd
  statement: ker (snd R M M₂) = range (inl R M M₂)
  proof: Eq.symm range_inl R M M₂

中文:
定理 ker_snd
  结论: ker (snd R M M₂) = range (inl R M M₂)
  证明: Eq.symm range_inl R M M₂

Depends on / 依赖: Eq.symm, instIsProbabilityMeasure, prod.instIsProbabilityMeasure, range_inl
-/
theorem ker_snd : ker (snd R M M₂) = range (inl R M M₂) :=
Eq.symm range_inl R M M₂

/--
theorem `range_inr` / 定理 `range_inr`

English:
theorem range_inr
  statement: range (inr R M M₂) = ker (fst R M M₂)
  proof: by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.snd, Prod.ext h.symm rfl⟩

中文:
定理 range_inr
  结论: range (inr R M M₂) = ker (fst R M M₂)
  证明: by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.snd, Prod.ext h.symm rfl⟩

Depends on / 依赖: Prod.ext, h.symm, mem_ker, mem_range, x.snd
-/
theorem range_inr : range (inr R M M₂) = ker (fst R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.snd, Prod.ext h.symm rfl⟩

/--
theorem `ker_fst` / 定理 `ker_fst`

English:
theorem ker_fst
  statement: ker (fst R M M₂) = range (inr R M M₂)
  proof: Eq.symm range_inr R M M₂

中文:
定理 ker_fst
  结论: ker (fst R M M₂) = range (inr R M M₂)
  证明: Eq.symm range_inr R M M₂

Depends on / 依赖: Eq.symm, instIsFiniteMeasureOnCompacts, prod.instIsFiniteMeasureOnCompacts, range_inr
-/
theorem ker_fst : ker (fst R M M₂) = range (inr R M M₂) :=
Eq.symm range_inr R M M₂

/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: fst R M M₂ ∘ₗ inl R M M₂ = id
  proof: rfl

中文:
定理 fst_comp_inl
  结论: fst R M M₂ ∘ₗ inl R M M₂ = id
  证明: rfl
-/
@[simp] theorem fst_comp_inl : fst R M M₂ ∘ₗ inl R M M₂ = id := rfl

/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: snd R M M₂ ∘ₗ inl R M M₂ = 0
  proof: rfl

中文:
定理 snd_comp_inl
  结论: snd R M M₂ ∘ₗ inl R M M₂ = 0
  证明: rfl
-/
@[simp] theorem snd_comp_inl : snd R M M₂ ∘ₗ inl R M M₂ = 0 := rfl

/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: fst R M M₂ ∘ₗ inr R M M₂ = 0
  proof: rfl

中文:
定理 fst_comp_inr
  结论: fst R M M₂ ∘ₗ inr R M M₂ = 0
  证明: rfl
-/
@[simp] theorem fst_comp_inr : fst R M M₂ ∘ₗ inr R M M₂ = 0 := rfl

/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: snd R M M₂ ∘ₗ inr R M M₂ = id
  proof: rfl

中文:
定理 snd_comp_inr
  结论: snd R M M₂ ∘ₗ inr R M M₂ = id
  证明: rfl
-/
@[simp] theorem snd_comp_inr : snd R M M₂ ∘ₗ inr R M M₂ = id := rfl

end

@[simp]
/--
theorem `coe_inl` / 定理 `coe_inl`

English:
theorem coe_inl
  statement: (inl R M M₂ : M -> M × M₂) = fun x => (x, 0)
  proof: rfl

中文:
定理 coe_inl
  结论: (inl R M M₂ : M -> M × M₂) = fun x => (x, 0)
  证明: rfl
-/
theorem coe_inl : (inl R M M₂ : M -> M × M₂) = fun x => (x, 0) :=
  rfl

/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x : M)
  statement: inl R M M₂ x = (x, 0)
  proof: rfl

@[simp]

中文:
定理 inl_apply
  条件: (x : M)
  结论: inl R M M₂ x = (x, 0)
  证明: rfl

@[simp]
-/
theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) :=
  rfl

@[simp]
/--
theorem `coe_inr` / 定理 `coe_inr`

English:
theorem coe_inr
  statement: (inr R M M₂ : M₂ -> M × M₂) = Prod.mk 0
  proof: rfl

中文:
定理 coe_inr
  结论: (inr R M M₂ : M₂ -> M × M₂) = 积类型.mk 0
  证明: rfl
-/
theorem coe_inr : (inr R M M₂ : M₂ -> M × M₂) = Prod.mk 0 :=
  rfl

/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (x : M₂)
  statement: inr R M M₂ x = (0, x)
  proof: rfl

中文:
定理 inr_apply
  条件: (x : M₂)
  结论: inr R M M₂ x = (0, x)
  证明: rfl
-/
theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) :=
  rfl

/--
theorem `inl_eq_prod` / 定理 `inl_eq_prod`

English:
theorem inl_eq_prod
  statement: inl R M M₂ = prod LinearMap.id 0
  proof: rfl

中文:
定理 inl_eq_prod
  结论: inl R M M₂ = 乘积 线性映射.id 0
  证明: rfl
-/
theorem inl_eq_prod : inl R M M₂ = prod LinearMap.id 0 :=
  rfl

/--
theorem `inr_eq_prod` / 定理 `inr_eq_prod`

English:
theorem inr_eq_prod
  statement: inr R M M₂ = prod 0 LinearMap.id
  proof: rfl

中文:
定理 inr_eq_prod
  结论: inr R M M₂ = 乘积 0 线性映射.id
  证明: rfl
-/
theorem inr_eq_prod : inr R M M₂ = prod 0 LinearMap.id :=
  rfl

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Function.Injective (inl R M M₂)
  proof: fun _ => by simp

中文:
定理 inl_injective
  结论: 函数.单射 (inl R M M₂)
  证明: fun _ => by simp
-/
theorem inl_injective : Function.Injective (inl R M M₂) := fun _ => by simp

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Function.Injective (inr R M M₂)
  proof: fun _ => by simp

中文:
定理 inr_injective
  结论: 函数.单射 (inr R M M₂)
  证明: fun _ => by simp
-/
theorem inr_injective : Function.Injective (inr R M M₂) := fun _ => by simp

/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  body: f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp]

中文:
定义 coprod
  签名: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  定义体: f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp]

Depends on / 依赖: f.comp, g.comp
-/
def coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : M × M₂ ->ₗ[R] M₃ :=
  f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp]
/--
theorem `coprod_apply` / 定理 `coprod_apply`

English:
theorem coprod_apply
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (x : M × M₂)
  proof: rfl

@[simp]

中文:
定理 coprod_apply
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (x : M × M₂)
  证明: rfl

@[simp]
-/
theorem coprod_apply (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (x : M × M₂) :
    coprod f g x = f x.1 + g x.2 :=
  rfl

@[simp]
/--
theorem `coprod_inl` / 定理 `coprod_inl`

English:
theorem coprod_inl
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  statement: (coprod f g).comp (inl R M M₂) = f
  proof: by
  ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp]

中文:
定理 coprod_inl
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  结论: (coprod f g).comp (inl R M M₂) = f
  证明: by
  ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp]

Depends on / 依赖: add_zero, comp_apply, coprod_apply, inl_apply, map_zero
-/
theorem coprod_inl (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : (coprod f g).comp (inl R M M₂) = f := by
  ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp]
/--
theorem `coprod_inr` / 定理 `coprod_inr`

English:
theorem coprod_inr
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  statement: (coprod f g).comp (inr R M M₂) = g
  proof: by
  ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp]

中文:
定理 coprod_inr
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  结论: (coprod f g).comp (inr R M M₂) = g
  证明: by
  ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp]

Depends on / 依赖: comp_apply, coprod_apply, inr_apply, map_zero, zero_add
-/
theorem coprod_inr (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : (coprod f g).comp (inr R M M₂) = g := by
  ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp]
/--
theorem `coprod_inl_inr` / 定理 `coprod_inl_inr`

English:
theorem coprod_inl_inr
  statement: coprod (inl R M M₂) (inr R M M₂) = LinearMap.id
  proof: by
  ext <;>
    simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]

中文:
定理 coprod_inl_inr
  结论: coprod (inl R M M₂) (inr R M M₂) = 线性映射.id
  证明: by
  ext <;>
    simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]

Depends on / 依赖: Prod.mk_add_mk, add_zero, coprod_apply, id_apply, inl_apply, inr_apply, mk_add_mk, zero_add
-/
theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id := by
  ext <;>
    simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]

/--
theorem `coprod_zero_left` / 定理 `coprod_zero_left`

English:
theorem coprod_zero_left
  given: (g : M₂ ->ₗ[R] M₃)
  statement: (0 : M ->ₗ[R] M₃).coprod g = g.comp (snd R M M₂)
  proof: zero_add _

中文:
定理 coprod_zero_left
  条件: (g : M₂ ->ₗ[R] M₃)
  结论: (0 : M ->ₗ[R] M₃).coprod g = g.comp (snd R M M₂)
  证明: zero_add _

Depends on / 依赖: zero_add
-/
theorem coprod_zero_left (g : M₂ ->ₗ[R] M₃) : (0 : M ->ₗ[R] M₃).coprod g = g.comp (snd R M M₂) :=
  zero_add _

/--
theorem `coprod_zero_right` / 定理 `coprod_zero_right`

English:
theorem coprod_zero_right
  given: (f : M ->ₗ[R] M₃)
  statement: f.coprod (0 : M₂ ->ₗ[R] M₃) = f.comp (fst R M M₂)
  proof: add_zero _

中文:
定理 coprod_zero_right
  条件: (f : M ->ₗ[R] M₃)
  结论: f.coprod (0 : M₂ ->ₗ[R] M₃) = f.comp (fst R M M₂)
  证明: add_zero _

Depends on / 依赖: add_zero
-/
theorem coprod_zero_right (f : M ->ₗ[R] M₃) : f.coprod (0 : M₂ ->ₗ[R] M₃) = f.comp (fst R M M₂) :=
  add_zero _

/--
theorem `comp_coprod` / 定理 `comp_coprod`

English:
theorem comp_coprod
  given: (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃) (g₂ : M₂ ->ₗ[R] M₃)
  proof: ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

中文:
定理 comp_coprod
  条件: (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃) (g₂ : M₂ ->ₗ[R] M₃)
  证明: ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

Depends on / 依赖: f.map_add, map_add
-/
theorem comp_coprod (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃) (g₂ : M₂ ->ₗ[R] M₃) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

/--
theorem `fst_eq_coprod` / 定理 `fst_eq_coprod`

English:
theorem fst_eq_coprod
  statement: fst R M M₂ = coprod LinearMap.id 0
  proof: by ext; simp

中文:
定理 fst_eq_coprod
  结论: fst R M M₂ = coprod 线性映射.id 0
  证明: by ext; simp
-/
theorem fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0 := by ext; simp

/--
theorem `snd_eq_coprod` / 定理 `snd_eq_coprod`

English:
theorem snd_eq_coprod
  statement: snd R M M₂ = coprod 0 LinearMap.id
  proof: by ext; simp

@[simp]

中文:
定理 snd_eq_coprod
  结论: snd R M M₂ = coprod 0 线性映射.id
  证明: by ext; simp

@[simp]
-/
theorem snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id := by ext; simp

@[simp]
/--
theorem `coprod_comp_prod` / 定理 `coprod_comp_prod`

English:
theorem coprod_comp_prod
  given: (f : M₂ ->ₗ[R] M₄) (g : M₃ ->ₗ[R] M₄) (f' : M ->ₗ[R] M₂) (g' : M ->ₗ[R] M₃)
  proof: rfl

@[simp]

中文:
定理 coprod_comp_prod
  条件: (f : M₂ ->ₗ[R] M₄) (g : M₃ ->ₗ[R] M₄) (f' : M ->ₗ[R] M₂) (g' : M ->ₗ[R] M₃)
  证明: rfl

@[simp]
-/
theorem coprod_comp_prod (f : M₂ ->ₗ[R] M₄) (g : M₃ ->ₗ[R] M₄) (f' : M ->ₗ[R] M₂) (g' : M ->ₗ[R] M₃) :
    (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g' :=
  rfl

@[simp]
/--
theorem `coprod_map_prod` / 定理 `coprod_map_prod`

English:
theorem coprod_map_prod
  statement: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (S : Submodule R M)
  proof: SetLike.coe_injective by
    simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
    rw [← Set.image2_add]; rw [Set.image2_image_left]; rw [Set.image2_image_right]
    exact Set.image_prod fun m m₂ => f m + g m₂

@[simp]

中文:
定理 coprod_map_prod
  结论: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (S : 子模 R M)
  证明: SetLike.coe_injective by
    simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
    rw [← Set.image2_add]; rw [Set.image2_image_left]; rw [Set.image2_image_right]
    exact Set.image_prod fun m m₂ => f m + g m₂

@[simp]

Depends on / 依赖: LinearMap, LinearMap.coprod_apply, Set.image2_add, Set.image2_image_left, Set.image2_image_right, Set.image_prod, SetLike, SetLike.coe_injective, Submodule, Submodule.coe_sup, Submodule.map_coe, coe_injective, coe_sup, coprod_apply, image2_add, image2_image_left, image2_image_right, image_prod, map_coe
-/
theorem coprod_map_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (S : Submodule R M)
    (S' : Submodule R M₂) : (Submodule.prod S S').map (LinearMap.coprod f g) = S.map f ⊔ S'.map g :=
SetLike.coe_injective by
    simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
    rw [← Set.image2_add]; rw [Set.image2_image_left]; rw [Set.image2_image_right]
    exact Set.image_prod fun m m₂ => f m + g m₂

@[simp]
/--
theorem `coprod_comp_inl_inr` / 定理 `coprod_comp_inl_inr`

English:
theorem coprod_comp_inl_inr
  given: (f : M × M₂ ->ₗ[R] M₃)
  proof: by
  rw [← comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

中文:
定理 coprod_comp_inl_inr
  条件: (f : M × M₂ ->ₗ[R] M₃)
  证明: by
  rw [← comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

Depends on / 依赖: comp_coprod, comp_id, coprod_inl_inr
-/
theorem coprod_comp_inl_inr (f : M × M₂ ->ₗ[R] M₃) :
    (f.comp (inl R M M₂)).coprod (f.comp (inr R M M₂)) = f := by
  rw [← comp_coprod]; rw [coprod_inl_inr]; rw [comp_id]

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/--
Definition of `coprodEquiv` / `coprodEquiv` 的定义

English:
definition coprodEquiv
  signature: [Module S M₃] [SMulCommClass R S M₃]
  body: f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, coprod_apply]

中文:
定义 coprodEquiv
  签名: [模 S M₃] [标量交换类 R S M₃]
  定义体: f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, coprod_apply]

Depends on / 依赖: coprod
-/
def coprodEquiv [Module S M₃] [SMulCommClass R S M₃] :
    ((M ->ₗ[R] M₃) × (M₂ ->ₗ[R] M₃)) ≃ₗ[S] M × M₂ ->ₗ[R] M₃ where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, coprod_apply]

/--
theorem `prod_ext_iff` / 定理 `prod_ext_iff`

English:
theorem prod_ext_iff
  given: {f g : M × M₂ ->ₗ[R] M₃}
  proof: (coprodEquiv Nat).symm.injective.eq_iff.symm.trans Prod.ext_iff

中文:
定理 prod_ext_iff
  条件: {f g : M × M₂ ->ₗ[R] M₃}
  证明: (coprodEquiv Nat).symm.injective.eq_iff.symm.trans Prod.ext_iff

Depends on / 依赖: Prod.ext_iff, coprodEquiv, eq_iff, ext_iff, injective, symm.injective.eq_iff.symm.trans
-/
theorem prod_ext_iff {f g : M × M₂ ->ₗ[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  (coprodEquiv Nat).symm.injective.eq_iff.symm.trans Prod.ext_iff

/--
Split equality of linear maps from a product into linear maps over each component, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/--
theorem `prod_ext` / 定理 `prod_ext`

English:
theorem prod_ext
  statement: {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  proof: prod_ext_iff.2 ⟨hl, hr⟩

中文:
定理 prod_ext
  结论: {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  证明: prod_ext_iff.2 ⟨hl, hr⟩

Depends on / 依赖: instSigmaFinite, prod.instSigmaFinite, prod_ext_iff
-/
theorem prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  body: (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

中文:
定义 prodMap
  签名: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  定义体: (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

Depends on / 依赖: f.comp, g.comp, instSFinite, prod.instSFinite
-/
def prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : M × M₂ ->ₗ[R] M₃ × M₄ :=
  (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))

/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  statement: ⇑(f.prodMap g) = Prod.map f g
  proof: rfl

@[simp]

中文:
定理 coe_prodMap
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  结论: ⇑(f.prodMap g) = 积类型.map f g
  证明: rfl

@[simp]
-/
theorem coe_prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/--
theorem `prodMap_apply` / 定理 `prodMap_apply`

English:
theorem prodMap_apply
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (x)
  statement: f.prodMap g x = (f x.1, g x.2)
  proof: rfl

中文:
定理 prodMap_apply
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (x)
  结论: f.prodMap g x = (f x.1, g x.2)
  证明: rfl
-/
theorem prodMap_apply (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

/--
theorem `prodMap_comap_prod` / 定理 `prodMap_comap_prod`

English:
theorem prodMap_comap_prod
  statement: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M₂)
  proof: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

中文:
定理 prodMap_comap_prod
  结论: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : 子模 R M₂)
  证明: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

Depends on / 依赖: Set.preimage_prod_map_prod, SetLike, SetLike.coe_injective, coe_injective, preimage_prod_map_prod
-/
theorem prodMap_comap_prod (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M₂)
    (S' : Submodule R M₄) :
    (Submodule.prod S S').comap (LinearMap.prodMap f g) = (S.comap f).prod (S'.comap g) :=
SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

/--
theorem `prodMap_map_prod` / 定理 `prodMap_map_prod`

English:
theorem prodMap_map_prod
  statement: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M)
  proof: SetLike.coe_injective Set.prodMap_image_prod f g _ _

@[simp]

中文:
定理 prodMap_map_prod
  结论: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : 子模 R M)
  证明: SetLike.coe_injective Set.prodMap_image_prod f g _ _

@[simp]

Depends on / 依赖: Set.prodMap_image_prod, SetLike, SetLike.coe_injective, coe_injective, prodMap_image_prod
-/
theorem prodMap_map_prod (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M)
    (S' : Submodule R M₃) :
    (Submodule.prod S S').map (LinearMap.prodMap f g) = (S.map f).prod (S'.map g) :=
SetLike.coe_injective Set.prodMap_image_prod f g _ _

@[simp]
/--
theorem `ker_prodMap` / 定理 `ker_prodMap`

English:
theorem ker_prodMap
  given: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄)
  proof: by
  dsimp only [ker]
  rw [← prodMap_comap_prod]; rw [Submodule.prod_bot]

@[simp]

中文:
定理 ker_prodMap
  条件: (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄)
  证明: by
  dsimp only [ker]
  rw [← prodMap_comap_prod]; rw [Submodule.prod_bot]

@[simp]

Depends on / 依赖: Submodule, Submodule.prod_bot, prodMap_comap_prod, prod_bot
-/
theorem ker_prodMap (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) :
    ker (LinearMap.prodMap f g) = Submodule.prod (ker f) (ker g) := by
  dsimp only [ker]
  rw [← prodMap_comap_prod]; rw [Submodule.prod_bot]

@[simp]
/--
theorem `range_prodMap` / 定理 `range_prodMap`

English:
theorem range_prodMap
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  proof: by
  ext ⟨_, _⟩; simp

@[simp]

中文:
定理 range_prodMap
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄)
  证明: by
  ext ⟨_, _⟩; simp

@[simp]
-/
theorem range_prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) :
    (f.prodMap g).range = f.range.prod g.range := by
  ext ⟨_, _⟩; simp

@[simp]
/--
theorem `prodMap_id` / 定理 `prodMap_id`

English:
theorem prodMap_id
  statement: (id : M ->ₗ[R] M).prodMap (id : M₂ ->ₗ[R] M₂) = id
  proof: rfl

@[simp]

中文:
定理 prodMap_id
  结论: (id : M ->ₗ[R] M).prodMap (id : M₂ ->ₗ[R] M₂) = id
  证明: rfl

@[simp]
-/
theorem prodMap_id : (id : M ->ₗ[R] M).prodMap (id : M₂ ->ₗ[R] M₂) = id :=
  rfl

@[simp]
/--
theorem `prodMap_one` / 定理 `prodMap_one`

English:
theorem prodMap_one
  statement: (1 : M ->ₗ[R] M).prodMap (1 : M₂ ->ₗ[R] M₂) = 1
  proof: rfl

中文:
定理 prodMap_one
  结论: (1 : M ->ₗ[R] M).prodMap (1 : M₂ ->ₗ[R] M₂) = 1
  证明: rfl
-/
theorem prodMap_one : (1 : M ->ₗ[R] M).prodMap (1 : M₂ ->ₗ[R] M₂) = 1 :=
  rfl

/--
theorem `prodMap_comp` / 定理 `prodMap_comp`

English:
theorem prodMap_comp
  statement: (f₁₂ : M ->ₗ[R] M₂) (f₂₃ : M₂ ->ₗ[R] M₃) (g₁₂ : M₄ ->ₗ[R] M₅)
  proof: rfl

中文:
定理 prodMap_comp
  结论: (f₁₂ : M ->ₗ[R] M₂) (f₂₃ : M₂ ->ₗ[R] M₃) (g₁₂ : M₄ ->ₗ[R] M₅)
  证明: rfl
-/
theorem prodMap_comp (f₁₂ : M ->ₗ[R] M₂) (f₂₃ : M₂ ->ₗ[R] M₃) (g₁₂ : M₄ ->ₗ[R] M₅)
    (g₂₃ : M₅ ->ₗ[R] M₆) :
    f₂₃.prodMap g₂₃ ∘ₗ f₁₂.prodMap g₁₂ = (f₂₃ ∘ₗ f₁₂).prodMap (g₂₃ ∘ₗ g₁₂) :=
  rfl

/--
theorem `prodMap_mul` / 定理 `prodMap_mul`

English:
theorem prodMap_mul
  given: (f₁₂ : M ->ₗ[R] M) (f₂₃ : M ->ₗ[R] M) (g₁₂ : M₂ ->ₗ[R] M₂) (g₂₃ : M₂ ->ₗ[R] M₂)
  proof: rfl

中文:
定理 prodMap_mul
  条件: (f₁₂ : M ->ₗ[R] M) (f₂₃ : M ->ₗ[R] M) (g₁₂ : M₂ ->ₗ[R] M₂) (g₂₃ : M₂ ->ₗ[R] M₂)
  证明: rfl
-/
theorem prodMap_mul (f₁₂ : M ->ₗ[R] M) (f₂₃ : M ->ₗ[R] M) (g₁₂ : M₂ ->ₗ[R] M₂) (g₂₃ : M₂ ->ₗ[R] M₂) :
    f₂₃.prodMap g₂₃ * f₁₂.prodMap g₁₂ = (f₂₃ * f₁₂).prodMap (g₂₃ * g₁₂) :=
  rfl

/--
theorem `prodMap_add` / 定理 `prodMap_add`

English:
theorem prodMap_add
  given: (f₁ : M ->ₗ[R] M₃) (f₂ : M ->ₗ[R] M₃) (g₁ : M₂ ->ₗ[R] M₄) (g₂ : M₂ ->ₗ[R] M₄)
  proof: rfl

@[simp]

中文:
定理 prodMap_add
  条件: (f₁ : M ->ₗ[R] M₃) (f₂ : M ->ₗ[R] M₃) (g₁ : M₂ ->ₗ[R] M₄) (g₂ : M₂ ->ₗ[R] M₄)
  证明: rfl

@[simp]
-/
theorem prodMap_add (f₁ : M ->ₗ[R] M₃) (f₂ : M ->ₗ[R] M₃) (g₁ : M₂ ->ₗ[R] M₄) (g₂ : M₂ ->ₗ[R] M₄) :
    (f₁ + f₂).prodMap (g₁ + g₂) = f₁.prodMap g₁ + f₂.prodMap g₂ :=
  rfl

@[simp]
/--
theorem `prodMap_zero` / 定理 `prodMap_zero`

English:
theorem prodMap_zero
  statement: (0 : M ->ₗ[R] M₂).prodMap (0 : M₃ ->ₗ[R] M₄) = 0
  proof: rfl

@[simp]

中文:
定理 prodMap_zero
  结论: (0 : M ->ₗ[R] M₂).prodMap (0 : M₃ ->ₗ[R] M₄) = 0
  证明: rfl

@[simp]
-/
theorem prodMap_zero : (0 : M ->ₗ[R] M₂).prodMap (0 : M₃ ->ₗ[R] M₄) = 0 :=
  rfl

@[simp]
/--
theorem `prodMap_smul` / 定理 `prodMap_smul`

English:
theorem prodMap_smul
  statement: [DistribMulAction S M₃] [DistribMulAction S M₄] [SMulCommClass R S M₃]
  proof: rfl

中文:
定理 prodMap_smul
  结论: [分配乘法作用 S M₃] [分配乘法作用 S M₄] [标量交换类 R S M₃]
  证明: rfl
-/
theorem prodMap_smul [DistribMulAction S M₃] [DistribMulAction S M₄] [SMulCommClass R S M₃]
    [SMulCommClass R S M₄] (s : S) (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) :
    prodMap (s • f) (s • g) = s • prodMap f g :=
  rfl

variable (R M M₂ M₃ M₄)

/-- `LinearMap.prodMap` as a `LinearMap` -/
@[simps]
/--
Definition of `prodMapLinear` / `prodMapLinear` 的定义

English:
definition prodMapLinear
  signature: [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulCommClass R S M₄]
  body: prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 prodMapLinear
  签名: [模 S M₃] [模 S M₄] [标量交换类 R S M₃] [标量交换类 R S M₄]
  定义体: prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: prodMap
-/
def prodMapLinear [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulCommClass R S M₄] :
    (M ->ₗ[R] M₃) × (M₂ ->ₗ[R] M₄) ->ₗ[S] M × M₂ ->ₗ[R] M₃ × M₄ where
  toFun f := prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LinearMap.prodMap` as a `RingHom` -/
@[simps]
/--
Definition of `prodMapRingHom` / `prodMapRingHom` 的定义

English:
definition prodMapRingHom
  signature: : (M ->ₗ[R] M) × (M₂ ->ₗ[R] M₂) ->+* M × M₂ ->ₗ[R] M × M₂ where
  body: prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 prodMapRingHom
  签名: : (M ->ₗ[R] M) × (M₂ ->ₗ[R] M₂) ->+* M × M₂ ->ₗ[R] M × M₂ where
  定义体: prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: prodMap
-/
def prodMapRingHom : (M ->ₗ[R] M) × (M₂ ->ₗ[R] M₂) ->+* M × M₂ ->ₗ[R] M × M₂ where
  toFun f := prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {R M M₂ M₃ M₄}

section map_mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
variable {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]

/--
theorem `inl_map_mul` / 定理 `inl_map_mul`

English:
theorem inl_map_mul
  given: (a₁ a₂ : A)
  proof: Prod.ext rfl (by simp)

中文:
定理 inl_map_mul
  条件: (a₁ a₂ : A)
  证明: Prod.ext rfl (by simp)

Depends on / 依赖: Prod.ext
-/
theorem inl_map_mul (a₁ a₂ : A) :
    LinearMap.inl R A B (a₁ * a₂) = LinearMap.inl R A B a₁ * LinearMap.inl R A B a₂ :=
  Prod.ext rfl (by simp)

/--
theorem `inr_map_mul` / 定理 `inr_map_mul`

English:
theorem inr_map_mul
  given: (b₁ b₂ : B)
  proof: Prod.ext (by simp) rfl

中文:
定理 inr_map_mul
  条件: (b₁ b₂ : B)
  证明: Prod.ext (by simp) rfl

Depends on / 依赖: Prod.ext
-/
theorem inr_map_mul (b₁ b₂ : B) :
    LinearMap.inr R A B (b₁ * b₂) = LinearMap.inr R A B b₁ * LinearMap.inr R A B b₂ :=
  Prod.ext (by simp) rfl

end map_mul

end LinearMap

end Prod

namespace LinearMap

variable (R M M₂)
variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- `LinearMap.prodMap` as an `AlgHom` -/
@[simps!]
/--
Definition of `prodMapAlgHom` / `prodMapAlgHom` 的定义

English:
definition prodMapAlgHom
  signature: : Module.End R M × Module.End R M₂ ->ₐ[R] Module.End R (M × M₂)
  body: { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

中文:
定义 prodMapAlgHom
  签名: : 模.End R M × 模.End R M₂ ->ₐ[R] 模.End R (M × M₂)
  定义体: { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

Depends on / 依赖: commutes, prodMapRingHom
-/
def prodMapAlgHom : Module.End R M × Module.End R M₂ ->ₐ[R] Module.End R (M × M₂) :=
  { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

end LinearMap

namespace LinearMap

open Submodule

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

/--
theorem `range_coprod` / 定理 `range_coprod`

English:
theorem range_coprod
  given: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  statement: range (f.coprod g) = range f ⊔ range g
  proof: Submodule.ext fun x => by simp [mem_sup]

中文:
定理 range_coprod
  条件: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
  结论: range (f.coprod g) = range f ⊔ range g
  证明: Submodule.ext fun x => by simp [mem_sup]

Depends on / 依赖: Submodule, Submodule.ext, mem_sup
-/
theorem range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : range (f.coprod g) = range f ⊔ range g :=
  Submodule.ext fun x => by simp [mem_sup]

/--
theorem `isCompl_range_inl_inr` / 定理 `isCompl_range_inl_inr`

English:
theorem isCompl_range_inl_inr
  statement: IsCompl (range <| inl R M M₂) (range <| inr R M M₂)
  proof: by
  constructor
  · rw [disjoint_def]
    rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.ext_iff, inl_apply, inr_apply] at hx hy ⊢
    exact ⟨hy.1.symm, hx.2.symm⟩
  · rw [codisjoint_iff_le_sup]
    rintro ⟨x, y⟩ -
    simp only [mem_sup, mem_range]
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
    simp

中文:
定理 isCompl_range_inl_inr
  结论: 是补集 (range <| inl R M M₂) (range <| inr R M M₂)
  证明: by
  constructor
  · rw [disjoint_def]
    rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.ext_iff, inl_apply, inr_apply] at hx hy ⊢
    exact ⟨hy.1.symm, hx.2.symm⟩
  · rw [codisjoint_iff_le_sup]
    rintro ⟨x, y⟩ -
    simp only [mem_sup, mem_range]
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
    simp

Depends on / 依赖: Prod.ext_iff, codisjoint_iff_le_sup, disjoint_def, ext_iff, inl_apply, inr_apply, mem_range, mem_sup
-/
theorem isCompl_range_inl_inr : IsCompl (range <| inl R M M₂) (range <| inr R M M₂) := by
  constructor
  · rw [disjoint_def]
    rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.ext_iff, inl_apply, inr_apply] at hx hy ⊢
    exact ⟨hy.1.symm, hx.2.symm⟩
  · rw [codisjoint_iff_le_sup]
    rintro ⟨x, y⟩ -
    simp only [mem_sup, mem_range]
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
    simp

/--
theorem `sup_range_inl_inr` / 定理 `sup_range_inl_inr`

English:
theorem sup_range_inl_inr
  statement: (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤
  proof: IsCompl.sup_eq_top isCompl_range_inl_inr

中文:
定理 sup_range_inl_inr
  结论: (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤
  证明: IsCompl.sup_eq_top isCompl_range_inl_inr

Depends on / 依赖: IsCompl, IsCompl.sup_eq_top, isCompl_range_inl_inr, sup_eq_top
-/
theorem sup_range_inl_inr : (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤ :=
  IsCompl.sup_eq_top isCompl_range_inl_inr

/--
theorem `disjoint_inl_inr` / 定理 `disjoint_inl_inr`

English:
theorem disjoint_inl_inr
  statement: Disjoint (range <| inl R M M₂) (range <| inr R M M₂)
  proof: by
  simp +contextual [disjoint_def, @eq_comm M 0]

中文:
定理 disjoint_inl_inr
  结论: Disjoint (range <| inl R M M₂) (range <| inr R M M₂)
  证明: by
  simp +contextual [disjoint_def, @eq_comm M 0]

Depends on / 依赖: contextual, disjoint_def, eq_comm
-/
theorem disjoint_inl_inr : Disjoint (range <| inl R M M₂) (range <| inr R M M₂) := by
  simp +contextual [disjoint_def, @eq_comm M 0]

/--
theorem `map_coprod_prod` / 定理 `map_coprod_prod`

English:
theorem map_coprod_prod
  statement: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (p : Submodule R M)
  proof: coprod_map_prod f g p q

中文:
定理 map_coprod_prod
  结论: (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (p : 子模 R M)
  证明: coprod_map_prod f g p q

Depends on / 依赖: coprod_map_prod
-/
theorem map_coprod_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (p : Submodule R M)
    (q : Submodule R M₂) : map (coprod f g) (p.prod q) = map f p ⊔ map g q :=
  coprod_map_prod f g p q

/--
theorem `comap_prod_prod` / 定理 `comap_prod_prod`

English:
theorem comap_prod_prod
  statement: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) (p : Submodule R M₂)
  proof: Submodule.ext fun _x => Iff.rfl

中文:
定理 comap_prod_prod
  结论: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) (p : 子模 R M₂)
  证明: Submodule.ext fun _x => Iff.rfl

Depends on / 依赖: Iff.rfl, Submodule, Submodule.ext
-/
theorem comap_prod_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) (p : Submodule R M₂)
    (q : Submodule R M₃) : comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
  Submodule.ext fun _x => Iff.rfl

/--
theorem `prod_eq_inf_comap` / 定理 `prod_eq_inf_comap`

English:
theorem prod_eq_inf_comap
  given: (p : Submodule R M) (q : Submodule R M₂)
  proof: Submodule.ext fun _x => Iff.rfl

中文:
定理 prod_eq_inf_comap
  条件: (p : 子模 R M) (q : 子模 R M₂)
  证明: Submodule.ext fun _x => Iff.rfl

Depends on / 依赖: Iff.rfl, Submodule, Submodule.ext
-/
theorem prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.comap (LinearMap.fst R M M₂) ⊓ q.comap (LinearMap.snd R M M₂) :=
  Submodule.ext fun _x => Iff.rfl

/--
theorem `prod_eq_sup_map` / 定理 `prod_eq_sup_map`

English:
theorem prod_eq_sup_map
  given: (p : Submodule R M) (q : Submodule R M₂)
  proof: by
  rw [← map_coprod_prod]; rw [coprod_inl_inr]; rw [map_id]

中文:
定理 prod_eq_sup_map
  条件: (p : 子模 R M) (q : 子模 R M₂)
  证明: by
  rw [← map_coprod_prod]; rw [coprod_inl_inr]; rw [map_id]

Depends on / 依赖: coprod_inl_inr, map_coprod_prod, map_id
-/
theorem prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.map (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M M₂) := by
  rw [← map_coprod_prod]; rw [coprod_inl_inr]; rw [map_id]

/--
theorem `span_inl_union_inr` / 定理 `span_inl_union_inr`

English:
theorem span_inl_union_inr
  given: {s : Set M} {t : Set M₂}
  proof: by
  rw [span_union]; rw [prod_eq_sup_map]; rw [← span_image]; rw [← span_image]

@[simp]

中文:
定理 span_inl_union_inr
  条件: {s : 集合 M} {t : 集合 M₂}
  证明: by
  rw [span_union]; rw [prod_eq_sup_map]; rw [← span_image]; rw [← span_image]

@[simp]

Depends on / 依赖: prod_eq_sup_map, span_image, span_union
-/
theorem span_inl_union_inr {s : Set M} {t : Set M₂} :
    span R (inl R M M₂ '' s union inr R M M₂ '' t) = (span R s).prod (span R t) := by
  rw [span_union]; rw [prod_eq_sup_map]; rw [← span_image]; rw [← span_image]

@[simp]
/--
theorem `ker_prod` / 定理 `ker_prod`

English:
theorem ker_prod
  given: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  statement: ker (prod f g) = ker f ⊓ ker g
  proof: by
  rw [ker]; rw [← prod_bot]; rw [comap_prod_prod]; rfl

中文:
定理 ker_prod
  条件: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  结论: ker (乘积 f g) = ker f ⊓ ker g
  证明: by
  rw [ker]; rw [← prod_bot]; rw [comap_prod_prod]; rfl

Depends on / 依赖: comap_prod_prod, prod_bot
-/
theorem ker_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ker (prod f g) = ker f ⊓ ker g := by
  rw [ker]; rw [← prod_bot]; rw [comap_prod_prod]; rfl

/--
theorem `range_prod_le` / 定理 `range_prod_le`

English:
theorem range_prod_le
  given: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  proof: by
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp]
  rintro _ x rfl
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

中文:
定理 range_prod_le
  条件: (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃)
  证明: by
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp]
  rintro _ x rfl
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

Depends on / 依赖: SetLike, SetLike.le_def, exists_imp, le_def, mem_prod, mem_range, prod_apply
-/
theorem range_prod_le (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) :
    range (prod f g) <= (range f).prod (range g) := by
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp]
  rintro _ x rfl
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

/--
theorem `ker_prod_ker_le_ker_coprod` / 定理 `ker_prod_ker_le_ker_coprod`

English:
theorem ker_prod_ker_le_ker_coprod
  statement: {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*}
  proof: by
  rintro ⟨y, z⟩
  simp +contextual

中文:
定理 ker_prod_ker_le_ker_coprod
  结论: {M₂ : 类型} [加法交换幺半群 M₂] [模 R M₂] {M₃ : 类型}
  证明: by
  rintro ⟨y, z⟩
  simp +contextual

Depends on / 依赖: contextual
-/
theorem ker_prod_ker_le_ker_coprod {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*}
    [AddCommMonoid M₃] [Module R M₃] (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) :
    (ker f).prod (ker g) <= ker (f.coprod g) := by
  rintro ⟨y, z⟩
  simp +contextual

/--
theorem `ker_coprod_of_disjoint_range` / 定理 `ker_coprod_of_disjoint_range`

English:
theorem ker_coprod_of_disjoint_range
  statement: {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*}
  proof: by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
  have : f y in (range f) ⊓ (range g) := by
    simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot]; rw [mem_bot] at this
  rw [this] at h
  simpa [this] using h

中文:
定理 ker_coprod_of_disjoint_range
  结论: {M₂ : 类型} [加法交换群 M₂] [模 R M₂] {M₃ : 类型}
  证明: by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
  have : f y in (range f) ⊓ (range g) := by
    simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot]; rw [mem_bot] at this
  rw [this] at h
  simpa [this] using h

Depends on / 依赖: coprod_apply, eq_bot, eq_comm, exists_apply_eq_apply, hd.eq_bot, ker_prod_ker_le_ker_coprod, le_antisymm, map_neg, mem_bot, mem_inf, mem_ker, mem_prod, mem_range, sub_eq_zero, sub_neg_eq_add, true_and
-/
theorem ker_coprod_of_disjoint_range {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*}
    [AddCommGroup M₃] [Module R M₃] (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃)
    (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g) := by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
  have : f y in (range f) ⊓ (range g) := by
    simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot]; rw [mem_bot] at this
  rw [this] at h
  simpa [this] using h

set_option backward.isDefEq.respectTransparency false in
/-- Given a linear map `f : E →ₗ[R] F` and a complement `C` of its kernel, we get a linear
equivalence between `C` and `range f`. -/
@[simps!]
/--
Definition of `kerComplementEquivRange` / `kerComplementEquivRange` 的定义

English:
definition kerComplementEquivRange
  signature: {R M M₂ : Type*} [Ring R] [AddCommGroup M]
  body: .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
  ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
   by
    rintro ⟨-, x, rfl⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp h.codisjoint x
    use ⟨y, hy⟩
    simpa [Subtype.ext_iff]⟩

中文:
定义 kerComplementEquivRange
  签名: {R M M₂ : 类型} [环 R] [加法交换群 M]
  定义体: .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
  ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
   by
    rintro ⟨-, x, rfl⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp h.codisjoint x
    use ⟨y, hy⟩
    simpa [Subtype.ext_iff]⟩

Depends on / 依赖: C.subtype, Subtype, Subtype.ext_iff, codRestrict, codisjoint, codisjoint_iff_exists_add_eq, codisjoint_iff_exists_add_eq.mp, disjoint, disjoint_iff_comap_eq_bot, ext_iff, h.codisjoint, h.disjoint, ker_codRestrict, ker_comp, ker_eq_bot, mem_range_self, ofBijective, subtype
-/
noncomputable def kerComplementEquivRange {R M M₂ : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) {C : Submodule R M}
    (h : IsCompl C (LinearMap.ker f)) : C ≃ₗ[R] range f :=
  .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
  ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
   by
    rintro ⟨-, x, rfl⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp h.codisjoint x
    use ⟨y, hy⟩
    simpa [Subtype.ext_iff]⟩

end LinearMap

namespace Submodule

open LinearMap

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/--
theorem `sup_eq_range` / 定理 `sup_eq_range`

English:
theorem sup_eq_range
  given: (p q : Submodule R M)
  statement: p ⊔ q = range (p.subtype.coprod q.subtype)
  proof: Submodule.ext fun x => by simp [Submodule.mem_sup]

中文:
定理 sup_eq_range
  条件: (p q : 子模 R M)
  结论: p ⊔ q = range (p.subtype.coprod q.subtype)
  证明: Submodule.ext fun x => by simp [Submodule.mem_sup]

Depends on / 依赖: Submodule, Submodule.ext, Submodule.mem_sup, mem_sup
-/
theorem sup_eq_range (p q : Submodule R M) : p ⊔ q = range (p.subtype.coprod q.subtype) :=
  Submodule.ext fun x => by simp [Submodule.mem_sup]

variable (p : Submodule R M) (q : Submodule R M₂)

@[simp]
/--
theorem `map_inl` / 定理 `map_inl`

English:
theorem map_inl
  statement: p.map (inl R M M₂) = prod p ⊥
  proof: by
  ext ⟨x, y⟩
  simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
    mem_prod]

@[simp]

中文:
定理 map_inl
  结论: p.map (inl R M M₂) = 乘积 p ⊥
  证明: by
  ext ⟨x, y⟩
  simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
    mem_prod]

@[simp]

Depends on / 依赖: Prod.mk_inj, and_left_comm, eq_comm, exists_eq_left, inl_apply, mem_bot, mem_map, mem_prod, mk_inj
-/
theorem map_inl : p.map (inl R M M₂) = prod p ⊥ := by
  ext ⟨x, y⟩
  simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
    mem_prod]

@[simp]
/--
theorem `map_inr` / 定理 `map_inr`

English:
theorem map_inr
  statement: q.map (inr R M M₂) = prod ⊥ q
  proof: by
  ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

@[simp]

中文:
定理 map_inr
  结论: q.map (inr R M M₂) = 乘积 ⊥ q
  证明: by
  ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

@[simp]

Depends on / 依赖: and_comm, and_left_comm, eq_comm
-/
theorem map_inr : q.map (inr R M M₂) = prod ⊥ q := by
  ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

@[simp]
/--
theorem `comap_fst` / 定理 `comap_fst`

English:
theorem comap_fst
  statement: p.comap (fst R M M₂) = prod p ⊤
  proof: by ext ⟨x, y⟩; simp

@[simp]

中文:
定理 comap_fst
  结论: p.comap (fst R M M₂) = 乘积 p ⊤
  证明: by ext ⟨x, y⟩; simp

@[simp]
-/
theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ := by ext ⟨x, y⟩; simp

@[simp]
/--
theorem `comap_snd` / 定理 `comap_snd`

English:
theorem comap_snd
  statement: q.comap (snd R M M₂) = prod ⊤ q
  proof: by ext ⟨x, y⟩; simp

@[simp]

中文:
定理 comap_snd
  结论: q.comap (snd R M M₂) = 乘积 ⊤ q
  证明: by ext ⟨x, y⟩; simp

@[simp]
-/
theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q := by ext ⟨x, y⟩; simp

@[simp]
/--
theorem `prod_comap_inl` / 定理 `prod_comap_inl`

English:
theorem prod_comap_inl
  statement: (prod p q).comap (inl R M M₂) = p
  proof: by ext; simp

@[simp]

中文:
定理 prod_comap_inl
  结论: (乘积 p q).comap (inl R M M₂) = p
  证明: by ext; simp

@[simp]
-/
theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp]
/--
theorem `prod_comap_inr` / 定理 `prod_comap_inr`

English:
theorem prod_comap_inr
  statement: (prod p q).comap (inr R M M₂) = q
  proof: by ext; simp

@[simp]

中文:
定理 prod_comap_inr
  结论: (乘积 p q).comap (inr R M M₂) = q
  证明: by ext; simp

@[simp]
-/
theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp]
/--
theorem `prod_map_fst` / 定理 `prod_map_fst`

English:
theorem prod_map_fst
  statement: (prod p q).map (fst R M M₂) = p
  proof: by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in q)]

@[simp]

中文:
定理 prod_map_fst
  结论: (乘积 p q).map (fst R M M₂) = p
  证明: by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in q)]

@[simp]

Depends on / 依赖: zero_mem
-/
theorem prod_map_fst : (prod p q).map (fst R M M₂) = p := by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in q)]

@[simp]
/--
theorem `prod_map_snd` / 定理 `prod_map_snd`

English:
theorem prod_map_snd
  statement: (prod p q).map (snd R M M₂) = q
  proof: by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in p)]

@[simp]

中文:
定理 prod_map_snd
  结论: (乘积 p q).map (snd R M M₂) = q
  证明: by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in p)]

@[simp]

Depends on / 依赖: zero_mem
-/
theorem prod_map_snd : (prod p q).map (snd R M M₂) = q := by
  ext x; simp [(⟨0, zero_mem _⟩ : exists x, x in p)]

@[simp]
/--
theorem `ker_inl` / 定理 `ker_inl`

English:
theorem ker_inl
  statement: ker (inl R M M₂) = ⊥
  proof: by rw [ker, ← prod_bot, prod_comap_inl]

@[simp]

中文:
定理 ker_inl
  结论: ker (inl R M M₂) = ⊥
  证明: by rw [ker, ← prod_bot, prod_comap_inl]

@[simp]

Depends on / 依赖: prod_bot, prod_comap_inl
-/
theorem ker_inl : ker (inl R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inl]

@[simp]
/--
theorem `ker_inr` / 定理 `ker_inr`

English:
theorem ker_inr
  statement: ker (inr R M M₂) = ⊥
  proof: by rw [ker, ← prod_bot, prod_comap_inr]

@[simp]

中文:
定理 ker_inr
  结论: ker (inr R M M₂) = ⊥
  证明: by rw [ker, ← prod_bot, prod_comap_inr]

@[simp]

Depends on / 依赖: prod_bot, prod_comap_inr
-/
theorem ker_inr : ker (inr R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inr]

@[simp]
/--
theorem `range_fst` / 定理 `range_fst`

English:
theorem range_fst
  statement: range (fst R M M₂) = ⊤
  proof: by rw [range_eq_map, ← prod_top, prod_map_fst]

@[simp]

中文:
定理 range_fst
  结论: range (fst R M M₂) = ⊤
  证明: by rw [range_eq_map, ← prod_top, prod_map_fst]

@[simp]

Depends on / 依赖: prod_map_fst, prod_top, range_eq_map
-/
theorem range_fst : range (fst R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_fst]

@[simp]
/--
theorem `range_snd` / 定理 `range_snd`

English:
theorem range_snd
  statement: range (snd R M M₂) = ⊤
  proof: by rw [range_eq_map, ← prod_top, prod_map_snd]

中文:
定理 range_snd
  结论: range (snd R M M₂) = ⊤
  证明: by rw [range_eq_map, ← prod_top, prod_map_snd]

Depends on / 依赖: prod_map_snd, prod_top, range_eq_map
-/
theorem range_snd : range (snd R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_snd]

variable (R M M₂)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : Submodule R (M × M₂)
  body: (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

中文:
定义 fst
  签名: : 子模 R (M × M₂)
  定义体: (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

Depends on / 依赖: LinearMap, LinearMap.snd, Submodule
-/
def fst : Submodule R (M × M₂) :=
  (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

/-- `M` as a submodule of `M × N` is isomorphic to `M`. -/
@[simps]
/--
Definition of `fstEquiv` / `fstEquiv` 的定义

English:
definition fstEquiv
  signature: : Submodule.fst R M M₂ ≃ₗ[R] M where
  body: x.1.1
  invFun m := ⟨⟨m, 0⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.fst)
  right_inv x := by simp

中文:
定义 fstEquiv
  签名: : 子模.fst R M M₂ ≃ₗ[R] M where
  定义体: x.1.1
  invFun m := ⟨⟨m, 0⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.fst)
  right_inv x := by simp
-/
def fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where
  toFun x := x.1.1
  invFun m := ⟨⟨m, 0⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.fst)
  right_inv x := by simp

/--
theorem `fst_map_fst` / 定理 `fst_map_fst`

English:
theorem fst_map_fst
  statement: (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤
  proof: by
  aesop

中文:
定理 fst_map_fst
  结论: (子模.fst R M M₂).map (线性映射.fst R M M₂) = ⊤
  证明: by
  aesop
-/
theorem fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤ := by
  aesop

/--
theorem `fst_map_snd` / 定理 `fst_map_snd`

English:
theorem fst_map_snd
  statement: (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥
  proof: by
  aesop (add simp fst)

中文:
定理 fst_map_snd
  结论: (子模.fst R M M₂).map (线性映射.snd R M M₂) = ⊥
  证明: by
  aesop (add simp fst)
-/
theorem fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥ := by
  aesop (add simp fst)

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : Submodule R (M × M₂)
  body: (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

中文:
定义 snd
  签名: : 子模 R (M × M₂)
  定义体: (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

Depends on / 依赖: LinearMap, LinearMap.fst, Submodule
-/
def snd : Submodule R (M × M₂) :=
  (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

/-- `N` as a submodule of `M × N` is isomorphic to `N`. -/
@[simps]
/--
Definition of `sndEquiv` / `sndEquiv` 的定义

English:
definition sndEquiv
  signature: : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
  body: x.1.2
  invFun n := ⟨⟨0, n⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.snd)

中文:
定义 sndEquiv
  签名: : 子模.snd R M M₂ ≃ₗ[R] M₂ where
  定义体: x.1.2
  invFun n := ⟨⟨0, n⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.snd)
-/
def sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
  toFun x := x.1.2
  invFun n := ⟨⟨0, n⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.snd)

/--
theorem `snd_map_fst` / 定理 `snd_map_fst`

English:
theorem snd_map_fst
  statement: (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥
  proof: by
  aesop (add simp snd)

中文:
定理 snd_map_fst
  结论: (子模.snd R M M₂).map (线性映射.fst R M M₂) = ⊥
  证明: by
  aesop (add simp snd)
-/
theorem snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥ := by
  aesop (add simp snd)

/--
theorem `snd_map_snd` / 定理 `snd_map_snd`

English:
theorem snd_map_snd
  statement: (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤
  proof: by
  aesop

中文:
定理 snd_map_snd
  结论: (子模.snd R M M₂).map (线性映射.snd R M M₂) = ⊤
  证明: by
  aesop
-/
theorem snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤ := by
  aesop

/--
theorem `fst_sup_snd` / 定理 `fst_sup_snd`

English:
theorem fst_sup_snd
  statement: Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤
  proof: by
  rw [eq_top_iff]
  rintro ⟨m, n⟩ -
  rw [show (m]; rw [n) = (m]; rw [0) + (0]; rw [n) by simp]
  apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
  · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
  · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))

中文:
定理 fst_sup_snd
  结论: 子模.fst R M M₂ ⊔ 子模.snd R M M₂ = ⊤
  证明: by
  rw [eq_top_iff]
  rintro ⟨m, n⟩ -
  rw [show (m]; rw [n) = (m]; rw [0) + (0]; rw [n) by simp]
  apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
  · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
  · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))

Depends on / 依赖: Submodule, Submodule.add_mem, Submodule.fst, Submodule.mem_comap.mpr, Submodule.mem_sup_left, Submodule.mem_sup_right, Submodule.snd, add_mem, eq_top_iff, mem_comap, mem_sup_left, mem_sup_right
-/
theorem fst_sup_snd : Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨m, n⟩ -
  rw [show (m]; rw [n) = (m]; rw [0) + (0]; rw [n) by simp]
  apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
  · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
  · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))

/--
theorem `fst_inf_snd` / 定理 `fst_inf_snd`

English:
theorem fst_inf_snd
  statement: Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥
  proof: by
  aesop

中文:
定理 fst_inf_snd
  结论: 子模.fst R M M₂ ⊓ 子模.snd R M M₂ = ⊥
  证明: by
  aesop
-/
theorem fst_inf_snd : Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥ := by
  aesop

/--
theorem `le_prod_iff` / 定理 `le_prod_iff`

English:
theorem le_prod_iff
  given: {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)}
  proof: by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

中文:
定理 le_prod_iff
  条件: {p₁ : 子模 R M} {p₂ : 子模 R M₂} {q : 子模 R (M × M₂)}
  证明: by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
-/
theorem le_prod_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    q <= p₁.prod p₂ ↔ map (LinearMap.fst R M M₂) q <= p₁ ∧ map (LinearMap.snd R M M₂) q <= p₂ := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

/--
theorem `prod_le_iff` / 定理 `prod_le_iff`

English:
theorem prod_le_iff
  given: {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)}
  proof: by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, zero_mem p₂⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨zero_mem p₁, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : (LinearMap.inl R _ _) x1 in q := by
      apply hH
      simpa using h1
    have h2' : (LinearMap.inr R _ _) x2 in q := by
      apply hK
      simpa using h2
    simpa using add_mem h1' h2'

中文:
定理 prod_le_iff
  条件: {p₁ : 子模 R M} {p₂ : 子模 R M₂} {q : 子模 R (M × M₂)}
  证明: by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, zero_mem p₂⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨zero_mem p₁, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : (LinearMap.inl R _ _) x1 in q := by
      apply hH
      simpa using h1
    have h2' : (LinearMap.inr R _ _) x2 in q := by
      apply hK
      simpa using h2
    simpa using add_mem h1' h2'

Depends on / 依赖: LinearMap, LinearMap.inl, LinearMap.inr, add_mem, zero_mem
-/
theorem prod_le_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    p₁.prod p₂ <= q ↔ map (LinearMap.inl R M M₂) p₁ <= q ∧ map (LinearMap.inr R M M₂) p₂ <= q := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, zero_mem p₂⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨zero_mem p₁, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : (LinearMap.inl R _ _) x1 in q := by
      apply hH
      simpa using h1
    have h2' : (LinearMap.inr R _ _) x2 in q := by
      apply hK
      simpa using h2
    simpa using add_mem h1' h2'

/--
theorem `prod_eq_bot_iff` / 定理 `prod_eq_bot_iff`

English:
theorem prod_eq_bot_iff
  given: {p₁ : Submodule R M} {p₂ : Submodule R M₂}
  proof: by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]

中文:
定理 prod_eq_bot_iff
  条件: {p₁ : 子模 R M} {p₂ : 子模 R M₂}
  证明: by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]

Depends on / 依赖: comap_bot, eq_bot_iff, gc_map_comap, ker_inl, ker_inr, le_iff_le, prod_le_iff
-/
theorem prod_eq_bot_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊥ ↔ p₁ = ⊥ ∧ p₂ = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]

/--
theorem `prod_eq_top_iff` / 定理 `prod_eq_top_iff`

English:
theorem prod_eq_top_iff
  given: {p₁ : Submodule R M} {p₂ : Submodule R M₂}
  proof: by
  simp only [eq_top_iff, le_prod_iff, map_top, range_fst, range_snd]

中文:
定理 prod_eq_top_iff
  条件: {p₁ : 子模 R M} {p₂ : 子模 R M₂}
  证明: by
  simp only [eq_top_iff, le_prod_iff, map_top, range_fst, range_snd]

Depends on / 依赖: eq_top_iff, le_prod_iff, map_top, range_fst, range_snd
-/
theorem prod_eq_top_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊤ ↔ p₁ = ⊤ ∧ p₂ = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, map_top, range_fst, range_snd]

variable {M M₂} in
/--
theorem `span_prod_eq` / 定理 `span_prod_eq`

English:
theorem span_prod_eq
  given: {s : Set M} {t : Set M₂} (hs : 0 in s) (ht : 0 in t)
  proof: by
  refine le_antisymm (span_prod_le s t) ?_
  simp [Submodule.prod_le_iff, map_span]
  grind [span_mono]

中文:
定理 span_prod_eq
  条件: {s : 集合 M} {t : 集合 M₂} (hs : 0 in s) (ht : 0 in t)
  证明: by
  refine le_antisymm (span_prod_le s t) ?_
  simp [Submodule.prod_le_iff, map_span]
  grind [span_mono]

Depends on / 依赖: Submodule, Submodule.prod_le_iff, le_antisymm, map_span, prod_le_iff, span_mono, span_prod_le
-/
theorem span_prod_eq {s : Set M} {t : Set M₂} (hs : 0 in s) (ht : 0 in t) :
    span R (s ×ˢ t) = (span R s).prod (span R t) := by
  refine le_antisymm (span_prod_le s t) ?_
  simp [Submodule.prod_le_iff, map_span]
  grind [span_mono]

end Submodule

namespace LinearEquiv

/-- Product of modules is commutative up to linear isomorphism. -/
@[simps apply]
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  body: { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

中文:
定义 prodComm
  签名: (R M N : 类型) [半环 R] [加法交换幺半群 M] [加法交换幺半群 N] [模 R M]
  定义体: { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

Depends on / 依赖: AddEquiv, AddEquiv.prodComm, Prod.swap, map_smul, prodComm
-/
def prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] : (M × N) ≃ₗ[R] N × M :=
  { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodComm

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]

/--
theorem `fst_comp_prodComm` / 定理 `fst_comp_prodComm`

English:
theorem fst_comp_prodComm
  proof: by
  ext <;> simp

中文:
定理 fst_comp_prodComm
  证明: by
  ext <;> simp
-/
theorem fst_comp_prodComm :
    (LinearMap.fst R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.snd R M M₂) := by
  ext <;> simp

/--
theorem `snd_comp_prodComm` / 定理 `snd_comp_prodComm`

English:
theorem snd_comp_prodComm
  proof: by
  ext <;> simp

@[simp]

中文:
定理 snd_comp_prodComm
  证明: by
  ext <;> simp

@[simp]
-/
theorem snd_comp_prodComm :
    (LinearMap.snd R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.fst R M M₂) := by
  ext <;> simp

@[simp]
/--
theorem `symm_prodComm` / 定理 `symm_prodComm`

English:
theorem symm_prodComm
  statement: (prodComm R M M₂).symm = prodComm R M₂ M
  proof: rfl

中文:
定理 symm_prodComm
  结论: (prodComm R M M₂).symm = prodComm R M₂ M
  证明: rfl
-/
theorem symm_prodComm : (prodComm R M M₂).symm = prodComm R M₂ M := rfl

end prodComm

/-- Product of modules is associative up to linear isomorphism. -/
@[simps apply]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: (R M₁ M₂ M₃ : Type*) [Semiring R]
  body: { AddEquiv.prodAssoc with
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

中文:
定义 prodAssoc
  签名: (R M₁ M₂ M₃ : 类型) [半环 R]
  定义体: { AddEquiv.prodAssoc with
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

Depends on / 依赖: AddEquiv, AddEquiv.prodAssoc, map_smul, prodAssoc
-/
def prodAssoc (R M₁ M₂ M₃ : Type*) [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃] : ((M₁ × M₂) × M₃) ≃ₗ[R] (M₁ × (M₂ × M₃)) :=
  { AddEquiv.prodAssoc with
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodAssoc

variable {M₁ : Type*}
variable [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]

/--
theorem `fst_comp_prodAssoc` / 定理 `fst_comp_prodAssoc`

English:
theorem fst_comp_prodAssoc
  proof: by
  ext <;> simp

中文:
定理 fst_comp_prodAssoc
  证明: by
  ext <;> simp
-/
theorem fst_comp_prodAssoc :
    (LinearMap.fst R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.fst R M₁ M₂).comp (LinearMap.fst R (M₁ × M₂) M₃) := by
  ext <;> simp

/--
theorem `snd_comp_prodAssoc` / 定理 `snd_comp_prodAssoc`

English:
theorem snd_comp_prodAssoc
  proof: by
  ext <;> simp

中文:
定理 snd_comp_prodAssoc
  证明: by
  ext <;> simp
-/
theorem snd_comp_prodAssoc :
    (LinearMap.snd R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.snd R M₁ M₂).prodMap (LinearMap.id : M₃ ->ₗ[R] M₃) := by
  ext <;> simp

end prodAssoc

section SkewSwap

variable (R M N)
variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/--
Definition of `skewSwap` / `skewSwap` 的定义

English:
definition skewSwap
  signature: : (M × N) ≃ₗ[R] (N × M) where
  body: (-x.2, x.1)
  invFun x := (x.2, -x.1)
  map_add' _ _ := by
    simp [add_comm]
  map_smul' _ _ := by
    simp
  left_inv _ := by
    simp
  right_inv _ := by
    simp

中文:
定义 skewSwap
  签名: : (M × N) ≃ₗ[R] (N × M) where
  定义体: (-x.2, x.1)
  invFun x := (x.2, -x.1)
  map_add' _ _ := by
    simp [add_comm]
  map_smul' _ _ := by
    simp
  left_inv _ := by
    simp
  right_inv _ := by
    simp
-/
protected def skewSwap : (M × N) ≃ₗ[R] (N × M) where
  toFun x := (-x.2, x.1)
  invFun x := (x.2, -x.1)
  map_add' _ _ := by
    simp [add_comm]
  map_smul' _ _ := by
    simp
  left_inv _ := by
    simp
  right_inv _ := by
    simp

variable {R M N}

@[simp]
/--
theorem `skewSwap_apply` / 定理 `skewSwap_apply`

English:
theorem skewSwap_apply
  given: (x : M × N)
  statement: LinearEquiv.skewSwap R M N x = (-x.2, x.1)
  proof: rfl

@[simp]

中文:
定理 skewSwap_apply
  条件: (x : M × N)
  结论: 线性等价.skewSwap R M N x = (-x.2, x.1)
  证明: rfl

@[simp]
-/
theorem skewSwap_apply (x : M × N) : LinearEquiv.skewSwap R M N x = (-x.2, x.1) := rfl

@[simp]
/--
theorem `skewSwap_symm_apply` / 定理 `skewSwap_symm_apply`

English:
theorem skewSwap_symm_apply
  given: (x : N × M)
  statement: (LinearEquiv.skewSwap R M N).symm x = (x.2, -x.1)
  proof: rfl

中文:
定理 skewSwap_symm_apply
  条件: (x : N × M)
  结论: (线性等价.skewSwap R M N).symm x = (x.2, -x.1)
  证明: rfl
-/
theorem skewSwap_symm_apply (x : N × M) : (LinearEquiv.skewSwap R M N).symm x = (x.2, -x.1) := rfl

end SkewSwap

section

variable (R M M₂ M₃ M₄)
variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄
  body: { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }

@[simp]

中文:
定义 prodProdProdComm
  签名: : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄
  定义体: { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.prodProdProdComm, _mnmn, invFun, map_smul, prodProdProdComm
-/
def prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄ :=
  { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }

@[simp]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_symm
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_symm :
    (prodProdProdComm R M M₂ M₃ M₄).symm = prodProdProdComm R M M₃ M₂ M₄ :=
  rfl

@[simp]
/--
theorem `prodProdProdComm_toAddEquiv` / 定理 `prodProdProdComm_toAddEquiv`

English:
theorem prodProdProdComm_toAddEquiv
  proof: rfl

中文:
定理 prodProdProdComm_toAddEquiv
  证明: rfl
-/
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R M M₂ M₃ M₄ : _ ≃+ _) = AddEquiv.prodProdProdComm M M₂ M₃ M₄ :=
  rfl

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: : (M × M₃) ≃ₗ[R] M₂ × M₄
  body: { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

@[simp]

中文:
定义 prodCongr
  签名: : (M × M₃) ≃ₗ[R] M₂ × M₄
  定义体: { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

@[simp]
-/
protected def prodCongr : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  statement: (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
  proof: rfl

@[simp]

中文:
定理 prodCongr_symm
  结论: (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
  证明: rfl

@[simp]
-/
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
/--
theorem `prodCongr_apply` / 定理 `prodCongr_apply`

English:
theorem prodCongr_apply
  given: (p)
  statement: e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
  proof: rfl

@[simp, norm_cast]

中文:
定理 prodCongr_apply
  条件: (p)
  结论: e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
  证明: rfl

@[simp, norm_cast]
-/
theorem prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  proof: rfl

中文:
定理 coe_prodCongr
  证明: rfl
-/
theorem coe_prodCongr :
    (e₁.prodCongr e₂ : M × M₃ ->ₗ[R] M₂ × M₄) = (e₁ : M ->ₗ[R] M₂).prodMap (e₂ : M₃ ->ₗ[R] M₄) :=
  rfl

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommGroup M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/--
Definition of `skewProd` / `skewProd` 的定义

English:
definition skewProd
  signature: (f : M ->ₗ[R] M₄)
  body: { ((e₁ : M ->ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ ->ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }

@[simp]

中文:
定义 skewProd
  签名: (f : M ->ₗ[R] M₄)
  定义体: { ((e₁ : M ->ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ ->ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }

@[simp]
-/
protected def skewProd (f : M ->ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { ((e₁ : M ->ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ ->ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }

@[simp]
/--
theorem `skewProd_apply` / 定理 `skewProd_apply`

English:
theorem skewProd_apply
  given: (f : M ->ₗ[R] M₄) (x)
  statement: e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1)
  proof: rfl

@[simp]

中文:
定理 skewProd_apply
  条件: (f : M ->ₗ[R] M₄) (x)
  结论: e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1)
  证明: rfl

@[simp]
-/
theorem skewProd_apply (f : M ->ₗ[R] M₄) (x) : e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) :=
  rfl

@[simp]
/--
theorem `skewProd_symm_apply` / 定理 `skewProd_symm_apply`

English:
theorem skewProd_symm_apply
  given: (f : M ->ₗ[R] M₄) (x)
  proof: rfl

中文:
定理 skewProd_symm_apply
  条件: (f : M ->ₗ[R] M₄) (x)
  证明: rfl
-/
theorem skewProd_symm_apply (f : M ->ₗ[R] M₄) (x) :
    (e₁.skewProd e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) :=
  rfl

end

section Unique

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂] [Unique M₂]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying by the trivial module from the left does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.uniqueProd`. -/
@[simps!]
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: : (M₂ × M) ≃ₗ[R] M
  body: AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])

中文:
定义 uniqueProd
  签名: : (M₂ × M) ≃ₗ[R] M
  定义体: AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])

Depends on / 依赖: AddEquiv, AddEquiv.uniqueProd, AddEquiv.uniqueProd.toLinearEquiv, toLinearEquiv, uniqueProd
-/
def uniqueProd : (M₂ × M) ≃ₗ[R] M :=
  AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])

/--
lemma `coe_uniqueProd` / 引理 `coe_uniqueProd`

English:
lemma coe_uniqueProd
  proof: rfl

中文:
引理 coe_uniqueProd
  证明: rfl

Depends on / 依赖: Equiv.uniqueProd, uniqueProd
-/
lemma coe_uniqueProd :
    (uniqueProd (R := R) (M := M) (M₂ := M₂) : (M₂ × M) ≃ M) = Equiv.uniqueProd M M₂ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying by the trivial module from the right does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.prodUnique`. -/
@[simps!]
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: : (M × M₂) ≃ₗ[R] M
  body: AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])

中文:
定义 prodUnique
  签名: : (M × M₂) ≃ₗ[R] M
  定义体: AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])

Depends on / 依赖: AddEquiv, AddEquiv.prodUnique, AddEquiv.prodUnique.toLinearEquiv, prodUnique, toLinearEquiv
-/
def prodUnique : (M × M₂) ≃ₗ[R] M :=
  AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])

/--
lemma `coe_prodUnique` / 引理 `coe_prodUnique`

English:
lemma coe_prodUnique
  proof: rfl

中文:
引理 coe_prodUnique
  证明: rfl

Depends on / 依赖: Equiv.prodUnique, prodUnique
-/
lemma coe_prodUnique :
    (prodUnique (R := R) (M := M) (M₂ := M₂) : (M × M₂) ≃ M) = Equiv.prodUnique M M₂ := rfl

end Unique

end LinearEquiv

namespace LinearMap

open Submodule

variable [Ring R]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/--
theorem `range_prod_eq` / 定理 `range_prod_eq`

English:
theorem range_prod_eq
  given: {f : M ->ₗ[R] M₂} {g : M ->ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤)
  proof: by
  refine le_antisymm (f.range_prod_le g) ?_
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp, and_imp,
    Prod.forall, Function.prod_apply]
  rintro _ _ x rfl y rfl
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
  simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
  have : y - x in ker f ⊔ ker g := by simp only [h, mem_top]
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
  refine ⟨x' + x, ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · simp [← eq_sub_iff_add_eq.1 H, map_add, mem_ker.mp hy']

中文:
定理 range_prod_eq
  条件: {f : M ->ₗ[R] M₂} {g : M ->ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤)
  证明: by
  refine le_antisymm (f.range_prod_le g) ?_
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp, and_imp,
    Prod.forall, Function.prod_apply]
  rintro _ _ x rfl y rfl
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
  simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
  have : y - x in ker f ⊔ ker g := by simp only [h, mem_top]
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
  refine ⟨x' + x, ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · simp [← eq_sub_iff_add_eq.1 H, map_add, mem_ker.mp hy']

Depends on / 依赖: Function, Function.prod_apply, Prod.forall, SetLike, SetLike.le_def, and_imp, exists_imp, f.range_prod_le, le_antisymm, le_def, mem_prod, mem_range, prod_apply, range_prod_le
-/
theorem range_prod_eq {f : M ->ₗ[R] M₂} {g : M ->ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (prod f g) = (range f).prod (range g) := by
  refine le_antisymm (f.range_prod_le g) ?_
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp, and_imp,
    Prod.forall, Function.prod_apply]
  rintro _ _ x rfl y rfl
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
  simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
  have : y - x in ker f ⊔ ker g := by simp only [h, mem_top]
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
  refine ⟨x' + x, ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · simp [← eq_sub_iff_add_eq.1 H, map_add, mem_ker.mp hy']

end LinearMap

namespace LinearMap

section Graph

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommGroup M₃] [AddCommGroup M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄] (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄)

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: : Submodule R (M × M₂) where
  body: { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add]; rw [ha]; rw [hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul]; rw [hx]

@[simp]

中文:
定义 graph
  签名: : 子模 R (M × M₂) where
  定义体: { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add]; rw [ha]; rw [hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul]; rw [hx]

@[simp]
-/
def graph : Submodule R (M × M₂) where
  carrier := { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add]; rw [ha]; rw [hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul]; rw [hx]

@[simp]
/--
theorem `mem_graph_iff` / 定理 `mem_graph_iff`

English:
theorem mem_graph_iff
  given: (x : M × M₂)
  statement: x in f.graph ↔ x.2 = f x.1
  proof: Iff.rfl

中文:
定理 mem_graph_iff
  条件: (x : M × M₂)
  结论: x in f.graph ↔ x.2 = f x.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_graph_iff (x : M × M₂) : x in f.graph ↔ x.2 = f x.1 :=
  Iff.rfl

/--
theorem `graph_eq_ker_coprod` / 定理 `graph_eq_ker_coprod`

English:
theorem graph_eq_ker_coprod
  statement: g.graph = ker ((-g).coprod LinearMap.id)
  proof: by
  ext x
  change _ = _ ↔ -g x.1 + x.2 = _
  rw [add_comm]; rw [add_neg_eq_zero]

中文:
定理 graph_eq_ker_coprod
  结论: g.graph = ker ((-g).coprod 线性映射.id)
  证明: by
  ext x
  change _ = _ ↔ -g x.1 + x.2 = _
  rw [add_comm]; rw [add_neg_eq_zero]

Depends on / 依赖: add_comm, add_neg_eq_zero
-/
theorem graph_eq_ker_coprod : g.graph = ker ((-g).coprod LinearMap.id) := by
  ext x
  change _ = _ ↔ -g x.1 + x.2 = _
  rw [add_comm]; rw [add_neg_eq_zero]

/--
theorem `graph_eq_range_prod` / 定理 `graph_eq_range_prod`

English:
theorem graph_eq_range_prod
  statement: f.graph = range (LinearMap.id.prod f)
  proof: by
  ext x
  exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

中文:
定理 graph_eq_range_prod
  结论: f.graph = range (线性映射.id.乘积 f)
  证明: by
  ext x
  exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

Depends on / 依赖: Prod.ext, hx.symm
-/
theorem graph_eq_range_prod : f.graph = range (LinearMap.id.prod f) := by
  ext x
  exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

end Graph

end LinearMap

section LineTest

open Set Function

variable {R S G H I : Type*}
  [Semiring R] [Semiring S] {σ : R ->+* S} [RingHomSurjective σ]
  [AddCommMonoid G] [Module R G]
  [AddCommMonoid H] [Module S H]
  [AddCommMonoid I] [Module S I]

/--
lemma `LinearMap.exists_range_eq_graph` / 引理 `LinearMap.exists_range_eq_graph`

English:
lemma LinearMap.exists_range_eq_graph
  statement: {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  obtain ⟨f', hf'⟩ :=
    AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
  simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
    AddMonoidHom.mem_mgraph] at hf'
  use
  { toFun := f'.toFun
    map_add' := f'.map_add'
    map_smul' := by
      intro s h
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      refine (hf' (s • h, _)).mp ?_
      rw [← Prod.smul_mk]; rw [← LinearMap.mem_range]
      apply Submodule.smul_mem
      rw [LinearMap.mem_range]; rw [hf'] }
  ext x
  simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
    coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

中文:
引理 线性映射.存在_range_eq_graph
  结论: {f : G ->ₛₗ[σ] H × I} (hf₁ : 满射 (积类型.fst ∘ f))
  证明: by
  obtain ⟨f', hf'⟩ :=
    AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
  simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
    AddMonoidHom.mem_mgraph] at hf'
  use
  { toFun := f'.toFun
    map_add' := f'.map_add'
    map_smul' := by
      intro s h
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      refine (hf' (s • h, _)).mp ?_
      rw [← Prod.smul_mk]; rw [← LinearMap.mem_range]
      apply Submodule.smul_mem
      rw [LinearMap.mem_range]; rw [hf'] }
  ext x
  simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
    coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.exists_mrange_eq_mgraph, AddMonoidHom.mem_mgraph, AddMonoidHom.mem_mrange, AddMonoidHom.toZeroHom_coe, LinearMap, LinearMap.mem_range, Prod.smul_mk, RingHom, RingHom.id_apply, SetLike, SetLike.ext_iff, Submodule, Submodule.smul_mem, ZeroHom, ZeroHom.toFun_eq_coe, coe_coe, exists_mrange_eq_mgraph, ext_iff
-/
lemma LinearMap.exists_range_eq_graph {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) :
    exists f' : H ->ₗ[S] I, LinearMap.range f = LinearMap.graph f' := by
  obtain ⟨f', hf'⟩ :=
    AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
  simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
    AddMonoidHom.mem_mgraph] at hf'
  use
  { toFun := f'.toFun
    map_add' := f'.map_add'
    map_smul' := by
      intro s h
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      refine (hf' (s • h, _)).mp ?_
      rw [← Prod.smul_mk]; rw [← LinearMap.mem_range]
      apply Submodule.smul_mem
      rw [LinearMap.mem_range]; rw [hf'] }
  ext x
  simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
    coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

/--
lemma `Submodule.exists_eq_graph` / 引理 `Submodule.exists_eq_graph`

English:
lemma Submodule.exists_eq_graph
  given: {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype))
  proof: by
  simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
      (fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

中文:
引理 子模.存在_eq_graph
  条件: {G : 子模 S (H × I)} (hf₁ : 双射 (积类型.fst ∘ G.subtype))
  证明: by
  simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
      (fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

Depends on / 依赖: G.subtype, LinearMap, LinearMap.exists_range_eq_graph, Prod.snd, congr_arg, exists_range_eq_graph, injective, range_subtype, subtype, surjective
-/
lemma Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
    exists f : H ->ₗ[S] I, G = LinearMap.graph f := by
  simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
      (fun a b h => congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

/--
lemma `LinearMap.exists_linearEquiv_eq_graph` / 引理 `LinearMap.exists_linearEquiv_eq_graph`

English:
lemma LinearMap.exists_linearEquiv_eq_graph
  statement: {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ => (hf _ _).1
  obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
(by simpa) by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
    rw [Eq.comm]; rw [← he₁ (h]; rw [i)]; rw [Eq.comm]; rw [← he₂ (i]; rw [h)]
    simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
  exact ⟨
  { toFun := e₁
    map_smul' := e₁.map_smul'
    map_add' := e₁.map_add'
    invFun := e₂
    left_inv := fun h => by rw [← he₁₂]
    right_inv := fun i => by rw [he₁₂] }, he₁⟩

中文:
引理 线性映射.存在_linearEquiv_eq_graph
  结论: {f : G ->ₛₗ[σ] H × I} (hf₁ : 满射 (积类型.fst ∘ f))
  证明: by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ => (hf _ _).1
  obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
(by simpa) by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
    rw [Eq.comm]; rw [← he₁ (h]; rw [i)]; rw [Eq.comm]; rw [← he₂ (i]; rw [h)]
    simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
  exact ⟨
  { toFun := e₁
    map_smul' := e₁.map_smul'
    map_add' := e₁.map_add'
    invFun := e₂
    left_inv := fun h => by rw [← he₁₂]
    right_inv := fun i => by rw [he₁₂] }, he₁⟩

Depends on / 依赖: Eq.comm, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.prodComm, LinearEquiv.prodComm_apply, LinearMap, LinearMap.mem_graph_iff, Prod.swap_eq_iff_eq_swap, SetLike, SetLike.ext_iff, coe_coe, coe_comp, comp_apply, exists_range_eq_graph, ext_iff, f.exists_range_eq_graph, mem_graph_iff, mem_range
-/
lemma LinearMap.exists_linearEquiv_eq_graph {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    exists e : H ≃ₗ[S] I, range f = e.toLinearMap.graph := by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ => (hf _ _).1
  obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
(by simpa) by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
    rw [Eq.comm]; rw [← he₁ (h]; rw [i)]; rw [Eq.comm]; rw [← he₂ (i]; rw [h)]
    simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
  exact ⟨
  { toFun := e₁
    map_smul' := e₁.map_smul'
    map_add' := e₁.map_add'
    invFun := e₂
    left_inv := fun h => by rw [← he₁₂]
    right_inv := fun i => by rw [he₁₂] }, he₁⟩

/--
lemma `Submodule.exists_equiv_eq_graph` / 引理 `Submodule.exists_equiv_eq_graph`

English:
lemma Submodule.exists_equiv_eq_graph
  statement: {G : Submodule S (H × I)}
  proof: by
  simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
    hG₁.surjective hG₂.surjective fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

中文:
引理 子模.存在_equiv_eq_graph
  结论: {G : 子模 S (H × I)}
  证明: by
  simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
    hG₁.surjective hG₂.surjective fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

Depends on / 依赖: LinearMap, LinearMap.exists_linearEquiv_eq_graph, eq_iff, exists_linearEquiv_eq_graph, injective, injective.eq_iff.symm, injective.eq_iff.trans, range_subtype, surjective
-/
lemma Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    exists e : H ≃ₗ[S] I, G = e.toLinearMap.graph := by
  simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
    hG₁.surjective hG₂.surjective fun _ _ => hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end LineTest
