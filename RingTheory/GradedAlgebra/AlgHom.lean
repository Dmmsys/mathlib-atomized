/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# `R`-linear homomorphisms of graded algebras

This file defines bundled `R`-linear homomorphisms of graded `R`-algebras.

## Main definitions

* `GradedAlgHom R 𝒜 ℬ`: the type of `R`-linear homomorphisms of `R`-graded algebras `𝒜` to `ℬ`.

## Notation

* `𝒜 →ₐᵍ[R] ℬ` : `R`-linear graded homomorphism from `𝒜` to `ℬ`.
-/

@[expose] public section

/--
Definition of `GradedAlgHom` / `GradedAlgHom` 的定义

English:
structure GradedAlgHom
  parameters: (R : Type*) {A B ι : Type*}
  extends: A ->ₐ[R] B, 𝒜 ->+*ᵍ ℬ
  (no additional axioms)

中文:
结构 GradedAlg态射
  参数: (R : 类型) {A B ι : 类型}
  继承: A ->ₐ[R] B, 𝒜 ->+*ᵍ ℬ
  (无附加公理)
-/
structure GradedAlgHom (R : Type*) {A B ι : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι -> Submodule R A) (ℬ : ι -> Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A ->ₐ[R] B, 𝒜 ->+*ᵍ ℬ

/-- Reinterpret a graded algebra homomorphism as a graded ring homomorphism. -/
add_decl_doc GradedAlgHom.toGradedRingHom

@[inherit_doc]
notation:25 𝒜 " ->ₐᵍ[" R "] " ℬ => GradedAlgHom R 𝒜 ℬ

namespace GradedAlgHom

variable {R S T U V A B C D ι : Type*}
  [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι -> Submodule R A} {ℬ : ι -> Submodule R B} {𝒞 : ι -> Submodule R C} {𝒟 : ι -> Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]

section ofClass
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [AlgHomClass F R A B]

/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: (f : F)
  body: { (AlgHomClass.toAlgHom f : A ->ₐ[R] B), (.ofClass f : 𝒜 ->+*ᵍ ℬ) with }

中文:
定义 ofClass
  签名: (f : F)
  定义体: { (AlgHomClass.toAlgHom f : A ->ₐ[R] B), (.ofClass f : 𝒜 ->+*ᵍ ℬ) with }

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, ofClass, toAlgHom
-/
def ofClass (f : F) : 𝒜 ->ₐᵍ[R] ℬ :=
  { (AlgHomClass.toAlgHom f : A ->ₐ[R] B), (.ofClass f : 𝒜 ->+*ᵍ ℬ) with }

end ofClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (𝒜 ->ₐᵍ[R] ℬ) A B
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr

中文:
实例 :
  签名: 函数状 (𝒜 ->ₐᵍ[R] ℬ) A B
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (𝒜 ->ₐᵍ[R] ℬ) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩, _⟩
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GradedFunLike (𝒜 ->ₐᵍ[R] ℬ) 𝒜 ℬ
  body: f.map_mem

中文:
实例 :
  签名: GradedFunLike (𝒜 ->ₐᵍ[R] ℬ) 𝒜 ℬ
  定义体: f.map_mem

Depends on / 依赖: f.map_mem, map_mem
-/
instance : GradedFunLike (𝒜 ->ₐᵍ[R] ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlgHomClass (𝒜 ->ₐᵍ[R] ℬ) R A B
  body: f.map_add
  map_zero f := f.map_zero
  map_mul f := f.map_mul
  map_one f := f.map_one
  commutes f := f.commutes

中文:
实例 :
  签名: 代数态射类 (𝒜 ->ₐᵍ[R] ℬ) R A B
  定义体: f.map_add
  map_zero f := f.map_zero
  map_mul f := f.map_mul
  map_one f := f.map_one
  commutes f := f.commutes

Depends on / 依赖: f.map_add, map_add
-/
instance : AlgHomClass (𝒜 ->ₐᵍ[R] ℬ) R A B where
  map_add f := f.map_add
  map_zero f := f.map_zero
  map_mul f := f.map_mul
  map_one f := f.map_one
  commutes f := f.commutes

attribute [coe] GradedAlgHom.toAlgHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (𝒜 ->ₐᵍ[R] ℬ) (A ->ₐ[R] B)
  body: ⟨toAlgHom⟩

中文:
实例 :
  签名: CoeOut (𝒜 ->ₐᵍ[R] ℬ) (A ->ₐ[R] B)
  定义体: ⟨toAlgHom⟩

Depends on / 依赖: toAlgHom
-/
instance : CoeOut (𝒜 ->ₐᵍ[R] ℬ) (A ->ₐ[R] B) := ⟨toAlgHom⟩

/--
lemma `toAlgHom_ofClass` / 引理 `toAlgHom_ofClass`

English:
lemma toAlgHom_ofClass
  statement: {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
  proof: rfl

中文:
引理 toAlgHom_ofClass
  结论: {F : 类型} [函数状 F A B] [GradedFunLike F 𝒜 ℬ]
  证明: rfl
-/
@[simp] lemma toAlgHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : (ofClass f : A ->ₐ[R] B) = AlgHomClass.toAlgHom f := rfl

/--
lemma `toGradedRingHom_ofClass` / 引理 `toGradedRingHom_ofClass`

English:
lemma toGradedRingHom_ofClass
  statement: {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
  proof: rfl

initialize_simps_projections GradedAlgHom (toFun -> apply)

中文:
引理 toGradedRingHom_ofClass
  结论: {F : 类型} [函数状 F A B] [GradedFunLike F 𝒜 ℬ]
  证明: rfl

initialize_simps_projections GradedAlgHom (toFun -> apply)
-/
@[simp] lemma toGradedRingHom_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) :
    ((ofClass f).toGradedRingHom : 𝒜 ->+*ᵍ ℬ) = GradedRingHom.ofClass f := rfl

initialize_simps_projections GradedAlgHom (toFun -> apply)

/--
theorem `coe_ofClass` / 定理 `coe_ofClass`

English:
theorem coe_ofClass
  statement: {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
  proof: rfl

中文:
定理 coe_ofClass
  结论: {F : 类型} [函数状 F A B] [GradedFunLike F 𝒜 ℬ]
  证明: rfl
-/
@[simp] theorem coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]
    [AlgHomClass F R A B] (f : F) : ⇑(.ofClass f : 𝒜 ->ₐᵍ[R] ℬ) = f := rfl

/--
theorem `coe_toAlgHom` / 定理 `coe_toAlgHom`

English:
theorem coe_toAlgHom
  given: (f : 𝒜 ->ₐᵍ[R] ℬ)
  statement: ⇑f.toAlgHom = f
  proof: rfl

中文:
定理 coe_toAlgHom
  条件: (f : 𝒜 ->ₐᵍ[R] ℬ)
  结论: ⇑f.toAlgHom = f
  证明: rfl
-/
@[simp] theorem coe_toAlgHom (f : 𝒜 ->ₐᵍ[R] ℬ) : ⇑f.toAlgHom = f := rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f : A ->ₐ[R] B} (h)
  statement: ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A -> B) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_mk
  条件: {f : A ->ₐ[R] B} (h)
  结论: ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A -> B) = f
  证明: rfl

@[norm_cast]
-/
@[simp] theorem coe_mk {f : A ->ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A -> B) = f := rfl

@[norm_cast]
/--
theorem `coe_mks` / 定理 `coe_mks`

English:
theorem coe_mks
  given: {f : A -> B} (h₁ h₂ h₃ h₄ h₅ h₆)
  proof: rfl

中文:
定理 coe_mks
  条件: {f : A -> B} (h₁ h₂ h₃ h₄ h₅ h₆)
  证明: rfl
-/
theorem coe_mks {f : A -> B} (h₁ h₂ h₃ h₄ h₅ h₆) :
    ⇑(⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 ->ₐᵍ[R] ℬ) = f := rfl

/--
theorem `coe_toAlgHom_mk` / 定理 `coe_toAlgHom_mk`

English:
theorem coe_toAlgHom_mk
  given: {f : A ->ₐ[R] B} (h)
  statement: ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A ->ₐ[R] B) = f
  proof: by
  dsimp only

@[deprecated (since := "2026-05-05")] alias coe_algHom_mk := coe_toAlgHom_mk

中文:
定理 coe_toAlgHom_mk
  条件: {f : A ->ₐ[R] B} (h)
  结论: ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A ->ₐ[R] B) = f
  证明: by
  dsimp only

@[deprecated (since := "2026-05-05")] alias coe_algHom_mk := coe_toAlgHom_mk
-/
theorem coe_toAlgHom_mk {f : A ->ₐ[R] B} (h) : ((⟨f, h⟩ : 𝒜 ->ₐᵍ[R] ℬ) : A ->ₐ[R] B) = f := by
  dsimp only

@[deprecated (since := "2026-05-05")] alias coe_algHom_mk := coe_toAlgHom_mk

variable (f : 𝒜 ->ₐᵍ[R] ℬ)

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
  proof: DFunLike.coe_injective

中文:
定理 coe_fn_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B))
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> (A -> B)) :=
  DFunLike.coe_injective

/--
theorem `coe_fn_inj` / 定理 `coe_fn_inj`

English:
theorem coe_fn_inj
  given: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ}
  statement: (f₁ : A -> B) = f₂ ↔ f₁ = f₂
  proof: DFunLike.coe_fn_eq

中文:
定理 coe_fn_inj
  条件: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ}
  结论: (f₁ : A -> B) = f₂ ↔ f₁ = f₂
  证明: DFunLike.coe_fn_eq

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_fn_inj {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} : (f₁ : A -> B) = f₂ ↔ f₁ = f₂ :=
  DFunLike.coe_fn_eq

/--
theorem `coe_toAlgHom_injective` / 定理 `coe_toAlgHom_injective`

English:
theorem coe_toAlgHom_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
  proof: fun _ _ h => coe_fn_injective congr($h)

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

中文:
定理 coe_toAlgHom_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B)
  证明: fun _ _ h => coe_fn_injective congr($h)

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

Depends on / 依赖: coe_fn_injective
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₐ[R] B) :=
  fun _ _ h => coe_fn_injective congr($h)

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

/--
theorem `toGradedRingHom_injective` / 定理 `toGradedRingHom_injective`

English:
theorem toGradedRingHom_injective
  statement: Function.Injective (toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ))
  proof: fun _ _ h => coe_fn_injective congr($h)

中文:
定理 toGradedRingHom_injective
  结论: 函数.单射 (toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ))
  证明: fun _ _ h => coe_fn_injective congr($h)
-/
theorem toGradedRingHom_injective : Function.Injective (toGradedRingHom (𝒜 := 𝒜) (ℬ := ℬ)) :=
  fun _ _ h => coe_fn_injective congr($h)

/--
theorem `coe_linearMap_injective` / 定理 `coe_linearMap_injective`

English:
theorem coe_linearMap_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₗ[R] B)
  proof: AlgHom.toLinearMap_injective.comp coe_toAlgHom_injective

中文:
定理 coe_linearMap_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₗ[R] B)
  证明: AlgHom.toLinearMap_injective.comp coe_toAlgHom_injective

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective.comp, coe_toAlgHom_injective, toLinearMap_injective
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->ₗ[R] B) :=
  AlgHom.toLinearMap_injective.comp coe_toAlgHom_injective

/--
theorem `coe_ringHom_injective` / 定理 `coe_ringHom_injective`

English:
theorem coe_ringHom_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+* B)
  proof: AlgHom.coe_ringHom_injective.comp coe_toAlgHom_injective

中文:
定理 coe_ringHom_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+* B)
  证明: AlgHom.coe_ringHom_injective.comp coe_toAlgHom_injective

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective.comp, coe_ringHom_injective, coe_toAlgHom_injective
-/
theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+* B) :=
  AlgHom.coe_ringHom_injective.comp coe_toAlgHom_injective

/--
theorem `coe_monoidHom_injective` / 定理 `coe_monoidHom_injective`

English:
theorem coe_monoidHom_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->* B)
  proof: AlgHom.coe_monoidHom_injective.comp coe_toAlgHom_injective

中文:
定理 coe_monoidHom_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->* B)
  证明: AlgHom.coe_monoidHom_injective.comp coe_toAlgHom_injective

Depends on / 依赖: AlgHom, AlgHom.coe_monoidHom_injective.comp, coe_monoidHom_injective, coe_toAlgHom_injective
-/
theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->* B) :=
  AlgHom.coe_monoidHom_injective.comp coe_toAlgHom_injective

/--
theorem `coe_addMonoidHom_injective` / 定理 `coe_addMonoidHom_injective`

English:
theorem coe_addMonoidHom_injective
  statement: Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+ B)
  proof: AlgHom.coe_addMonoidHom_injective.comp coe_toAlgHom_injective

中文:
定理 coe_addMonoidHom_injective
  结论: 函数.单射 ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+ B)
  证明: AlgHom.coe_addMonoidHom_injective.comp coe_toAlgHom_injective

Depends on / 依赖: AlgHom, AlgHom.coe_addMonoidHom_injective.comp, coe_addMonoidHom_injective, coe_toAlgHom_injective
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 ->ₐᵍ[R] ℬ) -> A ->+ B) :=
  AlgHom.coe_addMonoidHom_injective.comp coe_toAlgHom_injective

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : f₁ = f₂) (x : A)
  statement: f₁ x = f₂ x
  proof: DFunLike.congr_fun H x

中文:
定理 congr_fun
  条件: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : f₁ = f₂) (x : A)
  结论: f₁ x = f₂ x
  证明: DFunLike.congr_fun H x
-/
protected theorem congr_fun {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : f₁ = f₂) (x : A) : f₁ x = f₂ x :=
  DFunLike.congr_fun H x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : 𝒜 ->ₐᵍ[R] ℬ) {x y : A} (h : x = y)
  statement: f x = f y
  proof: DFunLike.congr_arg f h

@[ext]

中文:
定理 congr_arg
  条件: (f : 𝒜 ->ₐᵍ[R] ℬ) {x y : A} (h : x = y)
  结论: f x = f y
  证明: DFunLike.congr_arg f h

@[ext]
-/
protected theorem congr_arg (f : 𝒜 ->ₐᵍ[R] ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : forall x, f₁ x = f₂ x)
  statement: f₁ = f₂
  proof: DFunLike.ext _ _ H

@[simp]

中文:
定理 ext
  条件: {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : 对任意 x, f₁ x = f₂ x)
  结论: f₁ = f₂
  证明: DFunLike.ext _ _ H

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f₁ f₂ : 𝒜 ->ₐᵍ[R] ℬ} (H : forall x, f₁ x = f₂ x) : f₁ = f₂ :=
  DFunLike.ext _ _ H

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {f : 𝒜 ->ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆)
  proof: rfl

@[simp]

中文:
定理 mk_coe
  条件: {f : 𝒜 ->ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆)
  证明: rfl

@[simp]
-/
theorem mk_coe {f : 𝒜 ->ₐᵍ[R] ℬ} (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : 𝒜 ->ₐᵍ[R] ℬ) = f :=
  rfl

@[simp]
/--
theorem `commutes` / 定理 `commutes`

English:
theorem commutes
  given: (r : R)
  statement: f (algebraMap R A r) = algebraMap R B r
  proof: f.commutes' r

中文:
定理 commutes
  条件: (r : R)
  结论: f (algebraMap R A r) = algebraMap R B r
  证明: f.commutes' r

Depends on / 依赖: commutes, f.commutes
-/
theorem commutes (r : R) : f (algebraMap R A r) = algebraMap R B r :=
  f.commutes' r

/--
theorem `comp_ofId` / 定理 `comp_ofId`

English:
theorem comp_ofId
  statement: (f : A ->ₐ[R] B).comp (Algebra.ofId R A) = Algebra.ofId R B
  proof: AlgHom.ext f.commutes

中文:
定理 comp_ofId
  结论: (f : A ->ₐ[R] B).comp (代数.ofId R A) = 代数.ofId R B
  证明: AlgHom.ext f.commutes

Depends on / 依赖: AlgHom, AlgHom.ext, commutes, f.commutes
-/
theorem comp_ofId : (f : A ->ₐ[R] B).comp (Algebra.ofId R A) = Algebra.ofId R B :=
  AlgHom.ext f.commutes

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x)
  body: { AlgHom.mk' _ h, f with }

@[simp]

中文:
定义 mk'
  签名: (f : 𝒜 ->+*ᵍ ℬ) (h : 对任意 (c : R) (x), f (c • x) = c • f x)
  定义体: { AlgHom.mk' _ h, f with }

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk
-/
def mk' (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x) : 𝒜 ->ₐᵍ[R] ℬ :=
  { AlgHom.mk' _ h, f with }

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x)
  statement: ⇑(mk' f h) = f
  proof: rfl

中文:
定理 coe_mk'
  条件: (f : 𝒜 ->+*ᵍ ℬ) (h : 对任意 (c : R) (x), f (c • x) = c • f x)
  结论: ⇑(mk' f h) = f
  证明: rfl
-/
theorem coe_mk' (f : 𝒜 ->+*ᵍ ℬ) (h : forall (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section id
variable (R 𝒜)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : 𝒜 ->ₐᵍ[R] 𝒜
  body: { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]

中文:
定义 id
  签名: : 𝒜 ->ₐᵍ[R] 𝒜
  定义体: { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]
-/
@[simps!] protected def id : 𝒜 ->ₐᵍ[R] 𝒜 :=
  { AlgHom.id R A, GradedRingHom.id 𝒜 with }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(GradedAlgHom.id R 𝒜) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(GradedAlg态射.id R 𝒜) = id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(GradedAlgHom.id R 𝒜) = id := rfl

@[simp]
/--
theorem `id_toAlgHom` / 定理 `id_toAlgHom`

English:
theorem id_toAlgHom
  statement: (GradedAlgHom.id R 𝒜 : A ->ₐ[R] A) = AlgHom.id R A
  proof: rfl

中文:
定理 id_toAlgHom
  结论: (GradedAlg态射.id R 𝒜 : A ->ₐ[R] A) = 代数态射.id R A
  证明: rfl
-/
theorem id_toAlgHom : (GradedAlgHom.id R 𝒜 : A ->ₐ[R] A) = AlgHom.id R A := rfl

end id

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  body: { (g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B),
    (g.toGradedRingHom : ℬ ->+*ᵍ 𝒞).comp (f.toGradedRingHom : 𝒜 ->+*ᵍ ℬ) with }

@[simp]

中文:
定义 comp
  签名: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  定义体: { (g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B),
    (g.toGradedRingHom : ℬ ->+*ᵍ 𝒞).comp (f.toGradedRingHom : 𝒜 ->+*ᵍ ℬ) with }

@[simp]
-/
@[simps!] def comp (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ) : 𝒜 ->ₐᵍ[R] 𝒞 :=
  { (g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B),
    (g.toGradedRingHom : ℬ ->+*ᵍ 𝒞).comp (f.toGradedRingHom : 𝒜 ->+*ᵍ ℬ) with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : B ->ₐ[R] C) (f : 𝒜 ->ₐᵍ[R] ℬ)
  statement: ⇑(g.comp f) = g ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: (g : B ->ₐ[R] C) (f : 𝒜 ->ₐᵍ[R] ℬ)
  结论: ⇑(g.comp f) = g ∘ f
  证明: rfl
-/
theorem coe_comp (g : B ->ₐ[R] C) (f : 𝒜 ->ₐᵍ[R] ℬ) : ⇑(g.comp f) = g ∘ f := rfl

/--
theorem `comp_toGradedRingHom` / 定理 `comp_toGradedRingHom`

English:
theorem comp_toGradedRingHom
  given: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  proof: rfl

中文:
定理 comp_toGradedRingHom
  条件: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  证明: rfl
-/
theorem comp_toGradedRingHom (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ) :
    (g.comp f).toGradedRingHom = g.toGradedRingHom.comp f.toGradedRingHom := rfl

/--
theorem `comp_toAlgHom` / 定理 `comp_toAlgHom`

English:
theorem comp_toAlgHom
  given: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  proof: rfl

@[simp]

中文:
定理 comp_toAlgHom
  条件: (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ)
  证明: rfl

@[simp]
-/
theorem comp_toAlgHom (g : ℬ ->ₐᵍ[R] 𝒞) (f : 𝒜 ->ₐᵍ[R] ℬ) :
    (g.comp f : A ->ₐ[R] C) = (g : B ->ₐ[R] C).comp f := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: f.comp (.id R 𝒜) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  结论: f.comp (.id R 𝒜) = f
  证明: rfl

@[simp]
-/
theorem comp_id : f.comp (.id R 𝒜) = f := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (GradedAlgHom.id R ℬ).comp f = f
  proof: rfl

中文:
定理 id_comp
  结论: (GradedAlg态射.id R ℬ).comp f = f
  证明: rfl
-/
theorem id_comp : (GradedAlgHom.id R ℬ).comp f = f := rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (fCD : 𝒞 ->ₐᵍ[R] 𝒟) (fBC : ℬ ->ₐᵍ[R] 𝒞) (fAB : 𝒜 ->ₐᵍ[R] ℬ)
  proof: rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]

中文:
定理 comp_assoc
  条件: (fCD : 𝒞 ->ₐᵍ[R] 𝒟) (fBC : ℬ ->ₐᵍ[R] 𝒞) (fAB : 𝒜 ->ₐᵍ[R] ℬ)
  证明: rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
-/
theorem comp_assoc (fCD : 𝒞 ->ₐᵍ[R] 𝒟) (fBC : ℬ ->ₐᵍ[R] 𝒞) (fAB : 𝒜 ->ₐᵍ[R] ℬ) :
    (fCD.comp fBC).comp fAB = fCD.comp (fBC.comp fAB) := rfl

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (𝒜 ->ₐᵍ[R] 𝒜)
  body: comp
  one := .id R 𝒜
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

中文:
实例 :
  签名: 幺半群 (𝒜 ->ₐᵍ[R] 𝒜)
  定义体: comp
  one := .id R 𝒜
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
-/
instance : Monoid (𝒜 ->ₐᵍ[R] 𝒜) where
  mul := comp
  one := .id R 𝒜
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : 𝒜 ->ₐᵍ[R] 𝒜) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : 𝒜 ->ₐᵍ[R] 𝒜) = id
  证明: rfl
-/
@[simp] theorem coe_one : ⇑(1 : 𝒜 ->ₐᵍ[R] 𝒜) = id := rfl

/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : 𝒜 ->ₐᵍ[R] 𝒜)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : 𝒜 ->ₐᵍ[R] 𝒜)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp] theorem coe_mul (f g : 𝒜 ->ₐᵍ[R] 𝒜) : ⇑(f * g) = f ∘ g := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : 𝒜 ->ₐᵍ[R] 𝒜) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

中文:
定理 coe_pow
  条件: (f : 𝒜 ->ₐᵍ[R] 𝒜) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]
-/
@[simp] theorem coe_pow (f : 𝒜 ->ₐᵍ[R] 𝒜) (n : Nat) : ⇑(f ^ n) = f^[n] :=
  n.rec (by ext; simp) fun _ ih => by ext; simp [pow_succ, ih]

/--
lemma `cancel_right` / 引理 `cancel_right`

English:
lemma cancel_right
  given: {g₁ g₂ : ℬ ->ₐᵍ[R] 𝒞} {f : 𝒜 ->ₐᵍ[R] ℬ} (hf : Function.Surjective f)
  proof: ⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_right hf).1 congr($h), fun h => h ▸ rfl⟩

中文:
引理 cancel_right
  条件: {g₁ g₂ : ℬ ->ₐᵍ[R] 𝒞} {f : 𝒜 ->ₐᵍ[R] ℬ} (hf : 函数.满射 f)
  证明: ⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_right hf).1 congr($h), fun h => h ▸ rfl⟩

Depends on / 依赖: AlgHom, AlgHom.cancel_right, cancel_right, coe_toAlgHom_injective
-/
lemma cancel_right {g₁ g₂ : ℬ ->ₐᵍ[R] 𝒞} {f : 𝒜 ->ₐᵍ[R] ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_right hf).1 congr($h), fun h => h ▸ rfl⟩

/--
lemma `cancel_left` / 引理 `cancel_left`

English:
lemma cancel_left
  given: {g₁ g₂ : 𝒜 ->ₐᵍ[R] ℬ} {f : ℬ ->ₐᵍ[R] 𝒞} (hf : Function.Injective f)
  proof: ⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_left hf).1 congr($h), fun h => h ▸ rfl⟩

中文:
引理 cancel_left
  条件: {g₁ g₂ : 𝒜 ->ₐᵍ[R] ℬ} {f : ℬ ->ₐᵍ[R] 𝒞} (hf : 函数.单射 f)
  证明: ⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_left hf).1 congr($h), fun h => h ▸ rfl⟩

Depends on / 依赖: AlgHom, AlgHom.cancel_left, cancel_left, coe_toAlgHom_injective
-/
lemma cancel_left {g₁ g₂ : 𝒜 ->ₐᵍ[R] ℬ} {f : ℬ ->ₐᵍ[R] 𝒞} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨fun h => coe_toAlgHom_injective (AlgHom.cancel_left hf).1 congr($h), fun h => h ▸ rfl⟩

/--
Definition of `toEnd` / `toEnd` 的定义

English:
definition toEnd
  signature: : (𝒜 ->ₐᵍ[R] 𝒜) ->* (A ->ₐ[R] A) where
  body: toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toEnd
  签名: : (𝒜 ->ₐᵍ[R] 𝒜) ->* (A ->ₐ[R] A) where
  定义体: toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl
-/
@[simps] def toEnd : (𝒜 ->ₐᵍ[R] 𝒜) ->* (A ->ₐ[R] A) where
  toFun := toAlgHom
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Subsingleton B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (𝒜 ->ₐᵍ[R] ℬ)
  body: { (default : A ->ₐ[R] B) with map_mem hx := by aesop }
  uniq _ := ext fun _ => Subsingleton.elim _ _

@[simp]

中文:
实例 :
  签名: 唯一 (𝒜 ->ₐᵍ[R] ℬ)
  定义体: { (default : A ->ₐ[R] B) with map_mem hx := by aesop }
  uniq _ := ext fun _ => Subsingleton.elim _ _

@[simp]

Depends on / 依赖: map_mem
-/
instance : Unique (𝒜 ->ₐᵍ[R] ℬ) where
  default := { (default : A ->ₐ[R] B) with map_mem hx := by aesop }
  uniq _ := ext fun _ => Subsingleton.elim _ _

@[simp]
/--
lemma `default_apply` / 引理 `default_apply`

English:
lemma default_apply
  given: (x : A)
  statement: (default : 𝒜 ->ₐᵍ[R] ℬ) x = 0
  proof: rfl

中文:
引理 default_apply
  条件: (x : A)
  结论: (default : 𝒜 ->ₐᵍ[R] ℬ) x = 0
  证明: rfl
-/
lemma default_apply (x : A) : (default : 𝒜 ->ₐᵍ[R] ℬ) x = 0 :=
  rfl

end

section restrictScalars

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
  body: { f.toAlgHom.restrictScalars R₀, f with }

中文:
定义 restrictScalars
  签名: (R₀ : 类型) [交换半环 R₀] [代数 R₀ R]
  定义体: { f.toAlgHom.restrictScalars R₀, f with }
-/
@[coe, simps!] def restrictScalars (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 ->ₐᵍ[R] ℬ) : (𝒜 · |>.restrictScalars R₀) ->ₐᵍ[R₀] (ℬ · |>.restrictScalars R₀) :=
  { f.toAlgHom.restrictScalars R₀, f with }

variable (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R]
    [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ R A] [IsScalarTower R₀ R B]
    (f : 𝒜 ->ₐᵍ[R] ℬ)

/--
lemma `coe_restrictScalars` / 引理 `coe_restrictScalars`

English:
lemma coe_restrictScalars
  statement: ⇑(f.restrictScalars R₀) = f
  proof: rfl

中文:
引理 coe_restrictScalars
  结论: ⇑(f.restrictScalars R₀) = f
  证明: rfl
-/
@[simp] lemma coe_restrictScalars : ⇑(f.restrictScalars R₀) = f := rfl

/--
lemma `restrictScalars_toAlgHom` / 引理 `restrictScalars_toAlgHom`

English:
lemma restrictScalars_toAlgHom
  proof: rfl

@[deprecated (since := "2026-05-05")]
alias restrictScalars_coe_algHom := restrictScalars_toAlgHom

中文:
引理 restrictScalars_toAlgHom
  证明: rfl

@[deprecated (since := "2026-05-05")]
alias restrictScalars_coe_algHom := restrictScalars_toAlgHom
-/
@[simp] lemma restrictScalars_toAlgHom :
    (f : A ->ₐ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

@[deprecated (since := "2026-05-05")]
alias restrictScalars_coe_algHom := restrictScalars_toAlgHom

/--
lemma `restrictScalars_coe_linearMap` / 引理 `restrictScalars_coe_linearMap`

English:
lemma restrictScalars_coe_linearMap
  proof: rfl

中文:
引理 restrictScalars_coe_linearMap
  证明: rfl
-/
@[simp] lemma restrictScalars_coe_linearMap :
    (f : A ->ₗ[R] B).restrictScalars R₀ = f.restrictScalars R₀ := rfl

/--
lemma `restrictScalars_injective` / 引理 `restrictScalars_injective`

English:
lemma restrictScalars_injective
  proof: fun _ _ h => coe_fn_injective congr($h)

中文:
引理 restrictScalars_injective
  证明: fun _ _ h => coe_fn_injective congr($h)

Depends on / 依赖: coe_fn_injective
-/
lemma restrictScalars_injective :
    Function.Injective (restrictScalars R₀ : (𝒜 ->ₐᵍ[R] ℬ) -> _) :=
  fun _ _ h => coe_fn_injective congr($h)

end restrictScalars

end GradedAlgHom
