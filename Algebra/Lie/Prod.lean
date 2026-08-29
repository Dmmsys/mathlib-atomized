/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module
public import Mathlib.Algebra.Lie.Ideal

/-! ### Products of Lie algebras

This file defines the Lie algebra structure the Product of two Lie algebras

## Main definitions

- products in the domain:
  - `LieHom.fst` The first projection of a product is a Lie algebra map.
  - `LieHom.snd` The second projection of a product is a Lie algebra map.
  - `LieHom.prod_ext` Split equality of Lie algebra homomorphisms from a product into Lie algebra
  homomorphism over each component,
- products in the codomain:
  - `LieHom.inl` The left injection into a product is a Lie algebra map.
  - `LieHom.inr` The right injection into a product is a Lie algebra map.
  - `LieHom.prod` The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism.
- products in both domain and codomain:
  - `LieHom.prodMap` the `Prod.map` of two Lie algebra homomorphisms is a Lie algebra homomorphism.

## Todo: Extend to further functionality from LinearMap.prod e.g.
- Lie Equivalences related to products
- Lie Submodule statements

-/

@[expose] public section

variable {R L₁ L₂ L L₃ L₄ L₅ L₆ : Type*}
  [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  [LieRing L] [LieAlgebra R L] [LieRing L₃] [LieAlgebra R L₃] [LieRing L₄] [LieAlgebra R L₄]
  [LieRing L₅] [LieAlgebra R L₅] [LieRing L₆] [LieAlgebra R L₆]

namespace LieAlgebra.Prod

/--
Instance `instLieRing` / 实例 `instLieRing`

English:
instance instLieRing
  signature: : LieRing (L₁ × L₂) where
  body: ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]

中文:
实例 instLieRing
  签名: : Lie环 (L₁ × L₂) where
  定义体: ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
-/
instance instLieRing : LieRing (L₁ × L₂) where
  bracket x y := ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
/--
theorem `bracket_apply` / 定理 `bracket_apply`

English:
theorem bracket_apply
  given: (x y : L₁ × L₂)
  statement: ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  proof: rfl

中文:
定理 bracket_apply
  条件: (x y : L₁ × L₂)
  结论: ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩
  证明: rfl
-/
theorem bracket_apply (x y : L₁ × L₂) : ⁅x, y⁆ = ⟨⁅x.1, y.1⁆, ⁅x.2, y.2⁆⟩ := rfl

/--
Instance `instLieAlgebra` / 实例 `instLieAlgebra`

English:
instance instLieAlgebra
  signature: : LieAlgebra R (L₁ × L₂) where
  body: by simp

中文:
实例 instLieAlgebra
  签名: : Lie代数 R (L₁ × L₂) where
  定义体: by simp
-/
instance instLieAlgebra : LieAlgebra R (L₁ × L₂) where
  lie_smul _ _ _ := by simp

end LieAlgebra.Prod

namespace LieHom

section
variable (R L₁ L₂)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : L₁ × L₂ ->ₗ⁅R⁆ L₁ where
  body: LinearMap.fst R L₁ L₂
  map_lie' := by simp

中文:
定义 fst
  签名: : L₁ × L₂ ->ₗ⁅R⁆ L₁ where
  定义体: LinearMap.fst R L₁ L₂
  map_lie' := by simp

Depends on / 依赖: LinearMap, LinearMap.fst
-/
def fst : L₁ × L₂ ->ₗ⁅R⁆ L₁ where
  toLinearMap := LinearMap.fst R L₁ L₂
  map_lie' := by simp

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : L₁ × L₂ ->ₗ⁅R⁆ L₂ where
  body: LinearMap.snd R L₁ L₂
  map_lie' := by simp

中文:
定义 snd
  签名: : L₁ × L₂ ->ₗ⁅R⁆ L₂ where
  定义体: LinearMap.snd R L₁ L₂
  map_lie' := by simp

Depends on / 依赖: LinearMap, LinearMap.snd
-/
def snd : L₁ × L₂ ->ₗ⁅R⁆ L₂ where
  toLinearMap := LinearMap.snd R L₁ L₂
  map_lie' := by simp

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : L₁ ->ₗ⁅R⁆ L₁ × L₂ where
  body: LinearMap.inl R L₁ L₂
  map_lie' := by simp

中文:
定义 inl
  签名: : L₁ ->ₗ⁅R⁆ L₁ × L₂ where
  定义体: LinearMap.inl R L₁ L₂
  map_lie' := by simp

Depends on / 依赖: LinearMap, LinearMap.inl
-/
def inl : L₁ ->ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inl R L₁ L₂
  map_lie' := by simp

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : L₂ ->ₗ⁅R⁆ L₁ × L₂ where
  body: LinearMap.inr R L₁ L₂
  map_lie' := by simp

中文:
定义 inr
  签名: : L₂ ->ₗ⁅R⁆ L₁ × L₂ where
  定义体: LinearMap.inr R L₁ L₂
  map_lie' := by simp

Depends on / 依赖: LinearMap, LinearMap.inr
-/
def inr : L₂ ->ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.inr R L₁ L₂
  map_lie' := by simp

end

/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: (x : L₁ × L₂)
  statement: fst R L₁ L₂ x = x.1
  proof: rfl

中文:
定理 fst_apply
  条件: (x : L₁ × L₂)
  结论: fst R L₁ L₂ x = x.1
  证明: rfl
-/
@[simp] theorem fst_apply (x : L₁ × L₂) : fst R L₁ L₂ x = x.1 := rfl

/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: (x : L₁ × L₂)
  statement: snd R L₁ L₂ x = x.2
  proof: rfl

中文:
定理 snd_apply
  条件: (x : L₁ × L₂)
  结论: snd R L₁ L₂ x = x.2
  证明: rfl
-/
@[simp] theorem snd_apply (x : L₁ × L₂) : snd R L₁ L₂ x = x.2 := rfl

/--
lemma `coe_fst` / 引理 `coe_fst`

English:
lemma coe_fst
  statement: ⇑(fst R L₁ L₂) = Prod.fst
  proof: rfl

中文:
引理 coe_fst
  结论: ⇑(fst R L₁ L₂) = 积类型.fst
  证明: rfl
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst R L₁ L₂) = Prod.fst := rfl

/--
lemma `coe_snd` / 引理 `coe_snd`

English:
lemma coe_snd
  statement: ⇑(snd R L₁ L₂) = Prod.snd
  proof: rfl

中文:
引理 coe_snd
  结论: ⇑(snd R L₁ L₂) = 积类型.snd
  证明: rfl
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd R L₁ L₂) = Prod.snd := rfl

/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  statement: Function.Surjective (fst R L₁ L₂)
  proof: fun x => ⟨(x, 0), rfl⟩

中文:
定理 fst_surjective
  结论: 函数.满射 (fst R L₁ L₂)
  证明: fun x => ⟨(x, 0), rfl⟩
-/
theorem fst_surjective : Function.Surjective (fst R L₁ L₂) := fun x => ⟨(x, 0), rfl⟩

/--
theorem `snd_surjective` / 定理 `snd_surjective`

English:
theorem snd_surjective
  statement: Function.Surjective (snd R L₁ L₂)
  proof: fun x => ⟨(0, x), rfl⟩

中文:
定理 snd_surjective
  结论: 函数.满射 (snd R L₁ L₂)
  证明: fun x => ⟨(0, x), rfl⟩
-/
theorem snd_surjective : Function.Surjective (snd R L₁ L₂) := fun x => ⟨(0, x), rfl⟩

/-- The prod of two Lie algebra homomorphisms is a Lie algebra homomorphism. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  body: LinearMap.prod f g
  map_lie' := by simp

中文:
定义 乘积
  签名: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  定义体: LinearMap.prod f g
  map_lie' := by simp

Depends on / 依赖: LinearMap, LinearMap.prod
-/
def prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : L ->ₗ⁅R⁆ L₁ × L₂ where
  toLinearMap := LinearMap.prod f g
  map_lie' := by simp

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  结论: ⇑(f.乘积 g) = 函数.乘积 f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  statement: (fst R L₁ L₂).comp (prod f g) = f
  proof: rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  结论: (fst R L₁ L₂).comp (乘积 f g) = f
  证明: rfl

@[simp]
-/
theorem fst_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : (fst R L₁ L₂).comp (prod f g) = f := rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  statement: (snd R L₁ L₂).comp (prod f g) = g
  proof: rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂)
  结论: (snd R L₁ L₂).comp (乘积 f g) = g
  证明: rfl

@[simp]
-/
theorem snd_prod (f : L ->ₗ⁅R⁆ L₁) (g : L ->ₗ⁅R⁆ L₂) : (snd R L₁ L₂).comp (prod f g) = g := rfl

@[simp]
/--
theorem `pair_fst_snd` / 定理 `pair_fst_snd`

English:
theorem pair_fst_snd
  statement: prod (fst R L₁ L₂) (snd R L₁ L₂) = LieHom.id
  proof: rfl

中文:
定理 pair_fst_snd
  结论: 乘积 (fst R L₁ L₂) (snd R L₁ L₂) = Lie态射.id
  证明: rfl
-/
theorem pair_fst_snd : prod (fst R L₁ L₂) (snd R L₁ L₂) = LieHom.id := rfl

/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  statement: (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₁ ->ₗ⁅R⁆ L)
  proof: rfl

中文:
定理 prod_comp
  结论: (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₁ ->ₗ⁅R⁆ L)
  证明: rfl
-/
theorem prod_comp (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₁ ->ₗ⁅R⁆ L)
    (h : L ->ₗ⁅R⁆ L₁) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl

/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x : L₁)
  statement: inl R L₁ L₂ x = (x, 0)
  proof: rfl

中文:
定理 inl_apply
  条件: (x : L₁)
  结论: inl R L₁ L₂ x = (x, 0)
  证明: rfl
-/
theorem inl_apply (x : L₁) : inl R L₁ L₂ x = (x, 0) := rfl

/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (x : L₂)
  statement: inr R L₁ L₂ x = (0, x)
  proof: rfl

中文:
定理 inr_apply
  条件: (x : L₂)
  结论: inr R L₁ L₂ x = (0, x)
  证明: rfl
-/
theorem inr_apply (x : L₂) : inr R L₁ L₂ x = (0, x) := rfl

/--
theorem `coe_inl` / 定理 `coe_inl`

English:
theorem coe_inl
  statement: (inl R L₁ L₂ : L₁ -> L₁ × L₂) = fun x => (x, 0)
  proof: rfl

中文:
定理 coe_inl
  结论: (inl R L₁ L₂ : L₁ -> L₁ × L₂) = fun x => (x, 0)
  证明: rfl
-/
@[simp] theorem coe_inl : (inl R L₁ L₂ : L₁ -> L₁ × L₂) = fun x => (x, 0) := rfl

/--
theorem `coe_inr` / 定理 `coe_inr`

English:
theorem coe_inr
  statement: (inr R L₁ L₂ : L₂ -> L₁ × L₂) = Prod.mk 0
  proof: rfl

中文:
定理 coe_inr
  结论: (inr R L₁ L₂ : L₂ -> L₁ × L₂) = 积类型.mk 0
  证明: rfl
-/
@[simp] theorem coe_inr : (inr R L₁ L₂ : L₂ -> L₁ × L₂) = Prod.mk 0 := rfl

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Function.Injective (inl R L₁ L₂)
  proof: fun _ => by simp

中文:
定理 inl_injective
  结论: 函数.单射 (inl R L₁ L₂)
  证明: fun _ => by simp
-/
theorem inl_injective : Function.Injective (inl R L₁ L₂) := fun _ => by simp

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Function.Injective (inr R L₁ L₂)
  proof: fun _ => by simp

中文:
定理 inr_injective
  结论: 函数.单射 (inr R L₁ L₂)
  证明: fun _ => by simp
-/
theorem inr_injective : Function.Injective (inr R L₁ L₂) := fun _ => by simp

section
variable (R L₁ L₂)

/--
theorem `range_inl` / 定理 `range_inl`

English:
theorem range_inl
  statement: range (inl R L₁ L₂) = ker (snd R L₁ L₂)
  proof: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inl R L₁ L₂

中文:
定理 range_inl
  结论: range (inl R L₁ L₂) = ker (snd R L₁ L₂)
  证明: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inl R L₁ L₂

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LieSubalgebra, LieSubalgebra.toSubmodule_inj, LinearMap, LinearMap.range_inl, ker_toSubmodule, range_inl, range_toSubmodule, toLieSubalgebra_toSubmodule, toSubmodule_inj
-/
theorem range_inl : range (inl R L₁ L₂) = ker (snd R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inl R L₁ L₂

/--
theorem `ker_snd` / 定理 `ker_snd`

English:
theorem ker_snd
  statement: ker (snd R L₁ L₂) = range (inl R L₁ L₂)
  proof: Eq.symm range_inl R L₁ L₂

中文:
定理 ker_snd
  结论: ker (snd R L₁ L₂) = range (inl R L₁ L₂)
  证明: Eq.symm range_inl R L₁ L₂

Depends on / 依赖: Eq.symm, range_inl
-/
theorem ker_snd : ker (snd R L₁ L₂) = range (inl R L₁ L₂) :=
Eq.symm range_inl R L₁ L₂

/--
theorem `range_inr` / 定理 `range_inr`

English:
theorem range_inr
  statement: range (inr R L₁ L₂) = ker (fst R L₁ L₂)
  proof: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂

中文:
定理 range_inr
  结论: range (inr R L₁ L₂) = ker (fst R L₁ L₂)
  证明: by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LieSubalgebra, LieSubalgebra.toSubmodule_inj, LinearMap, LinearMap.range_inr, ker_toSubmodule, range_inr, range_toSubmodule, toLieSubalgebra_toSubmodule, toSubmodule_inj
-/
theorem range_inr : range (inr R L₁ L₂) = ker (fst R L₁ L₂) := by
  rw [← LieSubalgebra.toSubmodule_inj]; rw [range_toSubmodule]; rw [LieIdeal.toLieSubalgebra_toSubmodule]; rw [ker_toSubmodule]
  exact LinearMap.range_inr R L₁ L₂

/--
theorem `ker_fst` / 定理 `ker_fst`

English:
theorem ker_fst
  statement: ker (fst R L₁ L₂) = range (inr R L₁ L₂)
  proof: Eq.symm range_inr R L₁ L₂

中文:
定理 ker_fst
  结论: ker (fst R L₁ L₂) = range (inr R L₁ L₂)
  证明: Eq.symm range_inr R L₁ L₂

Depends on / 依赖: Eq.symm, range_inr
-/
theorem ker_fst : ker (fst R L₁ L₂) = range (inr R L₁ L₂) :=
Eq.symm range_inr R L₁ L₂

/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: (fst R L₁ L₂).comp (inl R L₁ L₂) = id
  proof: rfl

中文:
定理 fst_comp_inl
  结论: (fst R L₁ L₂).comp (inl R L₁ L₂) = id
  证明: rfl
-/
@[simp] theorem fst_comp_inl : (fst R L₁ L₂).comp (inl R L₁ L₂) = id := rfl

/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: (snd R L₁ L₂).comp (inl R L₁ L₂) = 0
  proof: rfl

中文:
定理 snd_comp_inl
  结论: (snd R L₁ L₂).comp (inl R L₁ L₂) = 0
  证明: rfl
-/
@[simp] theorem snd_comp_inl : (snd R L₁ L₂).comp (inl R L₁ L₂) = 0 := rfl

/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: (fst R L₁ L₂).comp (inr R L₁ L₂) = 0
  proof: rfl

中文:
定理 fst_comp_inr
  结论: (fst R L₁ L₂).comp (inr R L₁ L₂) = 0
  证明: rfl
-/
@[simp] theorem fst_comp_inr : (fst R L₁ L₂).comp (inr R L₁ L₂) = 0 := rfl

/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: (snd R L₁ L₂).comp (inr R L₁ L₂) = id
  proof: rfl

中文:
定理 snd_comp_inr
  结论: (snd R L₁ L₂).comp (inr R L₁ L₂) = id
  证明: rfl
-/
@[simp] theorem snd_comp_inr : (snd R L₁ L₂).comp (inr R L₁ L₂) = id := rfl

/--
theorem `inl_eq_prod` / 定理 `inl_eq_prod`

English:
theorem inl_eq_prod
  statement: inl R L₁ L₂ = prod LieHom.id 0
  proof: rfl

中文:
定理 inl_eq_prod
  结论: inl R L₁ L₂ = 乘积 Lie态射.id 0
  证明: rfl
-/
theorem inl_eq_prod : inl R L₁ L₂ = prod LieHom.id 0 :=
  rfl

/--
theorem `inr_eq_prod` / 定理 `inr_eq_prod`

English:
theorem inr_eq_prod
  statement: inr R L₁ L₂ = prod 0 LieHom.id
  proof: rfl

中文:
定理 inr_eq_prod
  结论: inr R L₁ L₂ = 乘积 0 Lie态射.id
  证明: rfl
-/
theorem inr_eq_prod : inr R L₁ L₂ = prod 0 LieHom.id :=
  rfl

/--
theorem `prod_ext_iff` / 定理 `prod_ext_iff`

English:
theorem prod_ext_iff
  given: {f g : L₁ × L₂ ->ₗ⁅R⁆ L}
  proof: by
  simp_rw [LieHom.ext_iff]
  have h := LinearMap.prod_ext_iff (f := f.toLinearMap) (g := g.toLinearMap)
  simp_rw [LinearMap.ext_iff] at h
  exact h

中文:
定理 prod_ext_iff
  条件: {f g : L₁ × L₂ ->ₗ⁅R⁆ L}
  证明: by
  simp_rw [LieHom.ext_iff]
  have h := LinearMap.prod_ext_iff (f := f.toLinearMap) (g := g.toLinearMap)
  simp_rw [LinearMap.ext_iff] at h
  exact h

Depends on / 依赖: LieHom, LieHom.ext_iff, LinearMap, LinearMap.ext_iff, LinearMap.prod_ext_iff, ext_iff, f.toLinearMap, g.toLinearMap, prod_ext_iff, simp_rw, toLinearMap
-/
theorem prod_ext_iff {f g : L₁ × L₂ ->ₗ⁅R⁆ L} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp_rw [LieHom.ext_iff]
  have h := LinearMap.prod_ext_iff (f := f.toLinearMap) (g := g.toLinearMap)
  simp_rw [LinearMap.ext_iff] at h
  exact h

/--
Split equality of Lie algebra homomorphisms from a product into Lie algebra homomorphism over
each component, to allow `ext` to apply lemmas specific to `L₁ →ₗ L` and `L₂ →ₗ L`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/--
theorem `prod_ext` / 定理 `prod_ext`

English:
theorem prod_ext
  statement: {f g : L₁ × L₂ ->ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  proof: by
  refine (prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

中文:
定理 prod_ext
  结论: {f g : L₁ × L₂ ->ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  证明: by
  refine (prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

Depends on / 依赖: prod_ext_iff
-/
theorem prod_ext {f g : L₁ × L₂ ->ₗ⁅R⁆ L} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g := by
  refine (prod_ext_iff R L₁ L₂).mpr ⟨hl,hr⟩

end

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄)
  body: (f.comp (fst R L₁ L₂)).prod (g.comp (snd R L₁ L₂))

中文:
定义 prodMap
  签名: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄)
  定义体: (f.comp (fst R L₁ L₂)).prod (g.comp (snd R L₁ L₂))

Depends on / 依赖: f.comp, g.comp
-/
def prodMap (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) : L₁ × L₂ ->ₗ⁅R⁆ L₃ × L₄ :=
  (f.comp (fst R L₁ L₂)).prod (g.comp (snd R L₁ L₂))

/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  given: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄)
  statement: ⇑(prodMap f g) = Prod.map f g
  proof: rfl

@[simp]

中文:
定理 coe_prodMap
  条件: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄)
  结论: ⇑(prodMap f g) = 积类型.map f g
  证明: rfl

@[simp]
-/
theorem coe_prodMap (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[simp]
/--
theorem `prodMap_apply` / 定理 `prodMap_apply`

English:
theorem prodMap_apply
  given: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) (x)
  statement: f.prodMap g x = (f x.1, g x.2)
  proof: rfl

@[simp]

中文:
定理 prodMap_apply
  条件: (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) (x)
  结论: f.prodMap g x = (f x.1, g x.2)
  证明: rfl

@[simp]
-/
theorem prodMap_apply (f : L₁ ->ₗ⁅R⁆ L₃) (g : L₂ ->ₗ⁅R⁆ L₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

@[simp]
/--
theorem `prodMap_id` / 定理 `prodMap_id`

English:
theorem prodMap_id
  statement: (id : L ->ₗ⁅R⁆ L).prodMap (id : L₁ ->ₗ⁅R⁆ L₁) = id
  proof: rfl

@[simp]

中文:
定理 prodMap_id
  结论: (id : L ->ₗ⁅R⁆ L).prodMap (id : L₁ ->ₗ⁅R⁆ L₁) = id
  证明: rfl

@[simp]
-/
theorem prodMap_id : (id : L ->ₗ⁅R⁆ L).prodMap (id : L₁ ->ₗ⁅R⁆ L₁) = id :=
  rfl

@[simp]
/--
theorem `prodMap_one` / 定理 `prodMap_one`

English:
theorem prodMap_one
  statement: (1 : L ->ₗ⁅R⁆ L).prodMap (1 : L₁ ->ₗ⁅R⁆ L₁) = 1
  proof: rfl

中文:
定理 prodMap_one
  结论: (1 : L ->ₗ⁅R⁆ L).prodMap (1 : L₁ ->ₗ⁅R⁆ L₁) = 1
  证明: rfl
-/
theorem prodMap_one : (1 : L ->ₗ⁅R⁆ L).prodMap (1 : L₁ ->ₗ⁅R⁆ L₁) = 1 :=
  rfl

/--
theorem `prodMap_comp` / 定理 `prodMap_comp`

English:
theorem prodMap_comp
  statement: (f₁₂ : L₁ ->ₗ⁅R⁆ L₂) (f₂₃ : L₂ ->ₗ⁅R⁆ L₃) (g₁₂ : L₄ ->ₗ⁅R⁆ L₅)
  proof: rfl

@[simp]

中文:
定理 prodMap_comp
  结论: (f₁₂ : L₁ ->ₗ⁅R⁆ L₂) (f₂₃ : L₂ ->ₗ⁅R⁆ L₃) (g₁₂ : L₄ ->ₗ⁅R⁆ L₅)
  证明: rfl

@[simp]
-/
theorem prodMap_comp (f₁₂ : L₁ ->ₗ⁅R⁆ L₂) (f₂₃ : L₂ ->ₗ⁅R⁆ L₃) (g₁₂ : L₄ ->ₗ⁅R⁆ L₅)
    (g₂₃ : L₅ ->ₗ⁅R⁆ L₆) :
    (f₂₃.prodMap g₂₃).comp (f₁₂.prodMap g₁₂) = (f₂₃.comp f₁₂).prodMap (g₂₃.comp g₁₂) :=
  rfl

@[simp]
/--
theorem `prodMap_zero` / 定理 `prodMap_zero`

English:
theorem prodMap_zero
  statement: (0 : L₁ ->ₗ⁅R⁆ L₃).prodMap (0 : L₂ ->ₗ⁅R⁆ L₄) = 0
  proof: rfl

中文:
定理 prodMap_zero
  结论: (0 : L₁ ->ₗ⁅R⁆ L₃).prodMap (0 : L₂ ->ₗ⁅R⁆ L₄) = 0
  证明: rfl
-/
theorem prodMap_zero : (0 : L₁ ->ₗ⁅R⁆ L₃).prodMap (0 : L₂ ->ₗ⁅R⁆ L₄) = 0 :=
  rfl

end LieHom

variable (R L₁ L₂) in
/--
Definition of `LieEquiv.prodComm` / `LieEquiv.prodComm` 的定义

English:
definition LieEquiv.prodComm
  signature: : (L₁ × L₂) ≃ₗ⁅R⁆ L₂ × L₁ where
  body: LinearEquiv.prodComm R L₁ L₂
  map_lie' := by simp

中文:
定义 Lie等价.prodComm
  签名: : (L₁ × L₂) ≃ₗ⁅R⁆ L₂ × L₁ where
  定义体: LinearEquiv.prodComm R L₁ L₂
  map_lie' := by simp
-/
@[simps!] def LieEquiv.prodComm : (L₁ × L₂) ≃ₗ⁅R⁆ L₂ × L₁ where
  __ := LinearEquiv.prodComm R L₁ L₂
  map_lie' := by simp

end
