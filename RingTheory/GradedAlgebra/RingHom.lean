/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.FunLike.Graded
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homomorphisms of graded (semi)rings

This file defines bundled homomorphisms of graded (semi)rings. We use the same structure
`GradedRingHom 𝒜 ℬ`, a.k.a. `𝒜 →+*ᵍ ℬ`, for both types of homomorphisms.

We do **not** define a separate class of graded ring homomorphisms; instead, we use
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.

## Main definitions

* `GradedRingHom`: Graded (semi)ring homomorphisms. Ring homomorphism which preserves the grading.

## Notation

* `→+*ᵍ`: Graded (semi)ring hom.

## Implementation notes

* We don't really need the fact that they are graded rings until the theorem
  `DirectSum.decompose_map` which describes how the decomposition interacts with the map.
-/

@[expose] public section

variable {ι A B C D σ τ ψ ω : Type*}
  [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [SetLike σ A] [SetLike τ B] [SetLike ψ C] [SetLike ω D]

open Graded

section SetLike

/--
Definition of `GradedRingHom` / `GradedRingHom` 的定义

English:
structure GradedRingHom
  parameters: (𝒜 : ι -> σ) (ℬ : ι -> τ)
  extends: A ->+* B
  axioms and operations (1):
    - map_mem({i : ι} {x : A}) : x in 𝒜 i -> toRingHom x in ℬ i

中文:
结构 分次环态射
  参数: (𝒜 : ι -> σ) (ℬ : ι -> τ)
  继承: A ->+* B
  公理与运算 (1 个):
    - map_mem({i : ι} {x : A}) : x in 𝒜 i -> toRingHom x in ℬ i
-/
structure GradedRingHom (𝒜 : ι -> σ) (ℬ : ι -> τ) extends A ->+* B where
  protected map_mem {i : ι} {x : A} : x in 𝒜 i -> toRingHom x in ℬ i

variable {𝒜 : ι -> σ} {ℬ : ι -> τ} {𝒞 : ι -> ψ} {𝒟 : ι -> ω}

@[inherit_doc]
notation:25 𝒜 " ->+*ᵍ " ℬ => GradedRingHom 𝒜 ℬ

namespace GradedRingHom

section ofClass
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- Turn an element of a type `F` satisfying
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]` into an actual `GradedRingHom`.

This should not be used directly. In the future, Mathlib will prefer structural projections over
these general constructions from hom classes. -/
@[coe]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: (f : F)
  body: (f : A ->+* B)
  map_mem := map_mem f

中文:
定义 ofClass
  签名: (f : F)
  定义体: (f : A ->+* B)
  map_mem := map_mem f
-/
def ofClass (f : F) : 𝒜 ->+*ᵍ ℬ where
  __ := (f : A ->+* B)
  map_mem := map_mem f

end ofClass

section coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (𝒜 ->+*ᵍ ℬ) A B
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

中文:
实例 :
  签名: 函数状 (𝒜 ->+*ᵍ ℬ) A B
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

Depends on / 依赖: f.toFun
-/
instance : FunLike (𝒜 ->+*ᵍ ℬ) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GradedFunLike (𝒜 ->+*ᵍ ℬ) 𝒜 ℬ
  body: f.map_mem

中文:
实例 :
  签名: GradedFunLike (𝒜 ->+*ᵍ ℬ) 𝒜 ℬ
  定义体: f.map_mem

Depends on / 依赖: f.map_mem, map_mem
-/
instance : GradedFunLike (𝒜 ->+*ᵍ ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingHomClass (𝒜 ->+*ᵍ ℬ) A B
  body: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections GradedRingHom (toFun -> apply)

中文:
实例 :
  签名: 环态射类 (𝒜 ->+*ᵍ ℬ) A B
  定义体: f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections GradedRingHom (toFun -> apply)

Depends on / 依赖: f.map_add, map_add
-/
instance : RingHomClass (𝒜 ->+*ᵍ ℬ) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections GradedRingHom (toFun -> apply)

attribute [coe] GradedRingHom.toRingHom

@[simp]
/--
theorem `toRingHom_eq_toRingHom` / 定理 `toRingHom_eq_toRingHom`

English:
theorem toRingHom_eq_toRingHom
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: RingHomClass.toRingHom f = f.toRingHom
  proof: rfl

@[simp]

中文:
定理 toRingHom_eq_toRingHom
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: 环态射类.toRingHom f = f.toRingHom
  证明: rfl

@[simp]
-/
theorem toRingHom_eq_toRingHom (f : 𝒜 ->+*ᵍ ℬ) : RingHomClass.toRingHom f = f.toRingHom := rfl

@[simp]
/--
theorem `coe_toRingHom` / 定理 `coe_toRingHom`

English:
theorem coe_toRingHom
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: ⇑f.toRingHom = f
  proof: rfl

@[simp]

中文:
定理 coe_toRingHom
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: ⇑f.toRingHom = f
  证明: rfl

@[simp]
-/
theorem coe_toRingHom (f : 𝒜 ->+*ᵍ ℬ) : ⇑f.toRingHom = f := rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A ->+* B) (h)
  statement: ((⟨f, h⟩ : 𝒜 ->+*ᵍ ℬ) : A -> B) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : A ->+* B) (h)
  结论: ((⟨f, h⟩ : 𝒜 ->+*ᵍ ℬ) : A -> B) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : A ->+* B) (h) : ((⟨f, h⟩ : 𝒜 ->+*ᵍ ℬ) : A -> B) = f := rfl

@[simp]
/--
theorem `coe_ofClass` / 定理 `coe_ofClass`

English:
theorem coe_ofClass
  statement: {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]
  proof: rfl

中文:
定理 coe_ofClass
  结论: {F : 类型} [函数状 F A B] [GradedFunLike F 𝒜 ℬ] [环态射类 F A B]
  证明: rfl
-/
theorem coe_ofClass {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]
    (f : F) : ((.ofClass f : 𝒜 ->+*ᵍ ℬ) : A -> B) = f := rfl

/--
Instance `coeToRingHom` / 实例 `coeToRingHom`

English:
instance coeToRingHom
  signature: : CoeOut (𝒜 ->+*ᵍ ℬ) (A ->+* B)
  body: ⟨GradedRingHom.toRingHom⟩

中文:
实例 coeToRingHom
  签名: : CoeOut (𝒜 ->+*ᵍ ℬ) (A ->+* B)
  定义体: ⟨GradedRingHom.toRingHom⟩

Depends on / 依赖: GradedRingHom, GradedRingHom.toRingHom, toRingHom
-/
instance coeToRingHom : CoeOut (𝒜 ->+*ᵍ ℬ) (A ->+* B) :=
  ⟨GradedRingHom.toRingHom⟩

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  body: f.toRingHom.copy f' h
map_mem hx := congr($h _ in ℬ _).to_iff.mpr map_mem f hx

@[simp]

中文:
定义 copy
  签名: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  定义体: f.toRingHom.copy f' h
map_mem hx := congr($h _ in ℬ _).to_iff.mpr map_mem f hx

@[simp]

Depends on / 依赖: f.toRingHom.copy, toRingHom
-/
def copy (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : 𝒜 ->+*ᵍ ℬ where
  __ := f.toRingHom.copy f' h
map_mem hx := congr($h _ in ℬ _).to_iff.mpr map_mem f hx

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : 𝒜 ->+*ᵍ ℬ) (f' : A -> B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable (f : 𝒜 ->+*ᵍ ℬ)

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : 𝒜 ->+*ᵍ ℬ} (h : f = g) (x : A)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : 𝒜 ->+*ᵍ ℬ} (h : f = g) (x : A)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : 𝒜 ->+*ᵍ ℬ} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : 𝒜 ->+*ᵍ ℬ) {x y : A} (h : x = y)
  statement: f x = f y
  proof: DFunLike.congr_arg f h

中文:
定理 congr_arg
  条件: (f : 𝒜 ->+*ᵍ ℬ) {x y : A} (h : x = y)
  结论: f x = f y
  证明: DFunLike.congr_arg f h
-/
protected theorem congr_arg (f : 𝒜 ->+*ᵍ ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: ⦃f g
  statement: 𝒜 ->+*ᵍ ℬ⦄ (h : (f : A -> B) = g) : f = g
  proof: DFunLike.coe_injective h

@[ext]

中文:
定理 coe_inj
  条件: ⦃f g
  结论: 𝒜 ->+*ᵍ ℬ⦄ (h : (f : A -> B) = g) : f = g
  证明: DFunLike.coe_injective h

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_inj ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ (h : (f : A -> B) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = g
  proof: DFunLike.ext _ _

@[simp]

中文:
定理 ext
  条件: ⦃f g
  结论: 𝒜 ->+*ᵍ ℬ⦄ : (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext _ _

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : 𝒜 ->+*ᵍ ℬ⦄ : (forall x, f x = g x) -> f = g :=
  DFunLike.ext _ _

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : 𝒜 ->+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅)
  statement: .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ = f
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: (f : 𝒜 ->+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅)
  结论: .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ = f
  证明: ext fun _ => rfl
-/
theorem mk_coe (f : 𝒜 ->+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅) : .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ = f :=
  ext fun _ => rfl

/--
theorem `coe_ringHom_injective` / 定理 `coe_ringHom_injective`

English:
theorem coe_ringHom_injective
  statement: (fun f : 𝒜 ->+*ᵍ ℬ => (f : A ->+* B)).Injective
  proof: fun _ _ h =>
ext DFunLike.congr_fun (F := A ->+* B) h

中文:
定理 coe_ringHom_injective
  结论: (fun f : 𝒜 ->+*ᵍ ℬ => (f : A ->+* B)).单射
  证明: fun _ _ h =>
ext DFunLike.congr_fun (F := A ->+* B) h
-/
theorem coe_ringHom_injective : (fun f : 𝒜 ->+*ᵍ ℬ => (f : A ->+* B)).Injective := fun _ _ h =>
ext DFunLike.congr_fun (F := A ->+* B) h

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: f 0 = 0
  proof: map_zero f

中文:
定理 map_zero
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: f 0 = 0
  证明: map_zero f
-/
protected theorem map_zero (f : 𝒜 ->+*ᵍ ℬ) : f 0 = 0 :=
  map_zero f

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: f 1 = 1
  proof: map_one f

中文:
定理 map_one
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: f 1 = 1
  证明: map_one f
-/
protected theorem map_one (f : 𝒜 ->+*ᵍ ℬ) : f 1 = 1 :=
  map_one f

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : 𝒜 ->+*ᵍ ℬ) (a b : A)
  statement: f (a + b) = f a + f b
  proof: map_add ..

中文:
定理 map_add
  条件: (f : 𝒜 ->+*ᵍ ℬ) (a b : A)
  结论: f (a + b) = f a + f b
  证明: map_add ..
-/
protected theorem map_add (f : 𝒜 ->+*ᵍ ℬ) (a b : A) : f (a + b) = f a + f b :=
  map_add ..

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : 𝒜 ->+*ᵍ ℬ) (a b : A)
  statement: f (a * b) = f a * f b
  proof: map_mul ..

中文:
定理 map_mul
  条件: (f : 𝒜 ->+*ᵍ ℬ) (a b : A)
  结论: f (a * b) = f a * f b
  证明: map_mul ..
-/
protected theorem map_mul (f : 𝒜 ->+*ᵍ ℬ) (a b : A) : f (a * b) = f a * f b :=
  map_mul ..

end

section Ring
variable {A B σ τ : Type*}
variable [Ring A] [Ring B] [SetLike σ A] [SetLike τ B]
variable (𝒜 : ι -> σ) (ℬ : ι -> τ)

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : 𝒜 ->+*ᵍ ℬ) (x : A)
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  条件: (f : 𝒜 ->+*ᵍ ℬ) (x : A)
  结论: f (-x) = -f x
  证明: map_neg f x
-/
protected theorem map_neg (f : 𝒜 ->+*ᵍ ℬ) (x : A) : f (-x) = -f x :=
  map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : 𝒜 ->+*ᵍ ℬ) (x y : A)
  proof: map_sub f x y

中文:
定理 map_sub
  条件: (f : 𝒜 ->+*ᵍ ℬ) (x y : A)
  证明: map_sub f x y
-/
protected theorem map_sub (f : 𝒜 ->+*ᵍ ℬ) (x y : A) :
    f (x - y) = f x - f y :=
  map_sub f x y

end Ring

variable (𝒜) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : 𝒜 ->+*ᵍ 𝒜 where
  body: RingHom.id _
  map_mem h := h

@[simp, norm_cast]

中文:
定义 id
  签名: : 𝒜 ->+*ᵍ 𝒜 where
  定义体: RingHom.id _
  map_mem h := h

@[simp, norm_cast]

Depends on / 依赖: RingHom, RingHom.id
-/
def id : 𝒜 ->+*ᵍ 𝒜 where
  __ := RingHom.id _
  map_mem h := h

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(GradedRingHom.id 𝒜) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(分次环态射.id 𝒜) = _root_.id
  证明: rfl

@[simp]

Depends on / 依赖: Inhabited, Result
-/
theorem coe_id : ⇑(GradedRingHom.id 𝒜) = _root_.id := rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : A)
  statement: GradedRingHom.id 𝒜 x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (x : A)
  结论: 分次环态射.id 𝒜 x = x
  证明: rfl

@[simp]
-/
theorem id_apply (x : A) : GradedRingHom.id 𝒜 x = x :=
  rfl

@[simp]
/--
theorem `toRingHom_id` / 定理 `toRingHom_id`

English:
theorem toRingHom_id
  statement: (id 𝒜).toRingHom = RingHom.id A
  proof: rfl

中文:
定理 toRingHom_id
  结论: (id 𝒜).toRingHom = 环态射.id A
  证明: rfl
-/
theorem toRingHom_id : (id 𝒜).toRingHom = RingHom.id A :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ)
  body: g.toRingHom.comp f
  map_mem := g.map_mem ∘ f.map_mem

中文:
定义 comp
  签名: (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ)
  定义体: g.toRingHom.comp f
  map_mem := g.map_mem ∘ f.map_mem

Depends on / 依赖: g.toRingHom.comp, toRingHom
-/
def comp (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ) : 𝒜 ->+*ᵍ 𝒞 where
  __ := g.toRingHom.comp f
  map_mem := g.map_mem ∘ f.map_mem

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h : 𝒞 ->+*ᵍ 𝒟) (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (h : 𝒞 ->+*ᵍ 𝒟) (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ)
  证明: rfl

@[simp]
-/
theorem comp_assoc (h : 𝒞 ->+*ᵍ 𝒟) (g : ℬ ->+*ᵍ 𝒞) (f : 𝒜 ->+*ᵍ ℬ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ)
  statement: (hnp.comp hmn : A -> C) = hnp ∘ hmn
  proof: rfl

中文:
定理 coe_comp
  条件: (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ)
  结论: (hnp.comp hmn : A -> C) = hnp ∘ hmn
  证明: rfl
-/
theorem coe_comp (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) : (hnp.comp hmn : A -> C) = hnp ∘ hmn :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) (x : A)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) (x : A)
  证明: rfl

@[simp]
-/
theorem comp_apply (hnp : ℬ ->+*ᵍ 𝒞) (hmn : 𝒜 ->+*ᵍ ℬ) (x : A) :
    (hnp.comp hmn : A -> C) x = hnp (hmn x) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: f.comp (id 𝒜) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: f.comp (id 𝒜) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : 𝒜 ->+*ᵍ ℬ) : f.comp (id 𝒜) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : 𝒜 ->+*ᵍ ℬ)
  statement: (id ℬ).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : 𝒜 ->+*ᵍ ℬ)
  结论: (id ℬ).comp f = f
  证明: ext fun _ => rfl
-/
theorem id_comp (f : 𝒜 ->+*ᵍ ℬ) : (id ℬ).comp f = f :=
  ext fun _ => rfl

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (𝒜 ->+*ᵍ 𝒜) where one
  body: id _

中文:
实例 instOne
  签名: : 幺 (𝒜 ->+*ᵍ 𝒜) where one
  定义体: id _
-/
instance instOne : One (𝒜 ->+*ᵍ 𝒜) where one := id _
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (𝒜 ->+*ᵍ 𝒜) where mul
  body: comp

中文:
实例 instMul
  签名: : 乘法 (𝒜 ->+*ᵍ 𝒜) where mul
  定义体: comp
-/
instance instMul : Mul (𝒜 ->+*ᵍ 𝒜) where mul := comp

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : 𝒜 ->+*ᵍ 𝒜) = id 𝒜
  proof: rfl

中文:
引理 one_def
  结论: (1 : 𝒜 ->+*ᵍ 𝒜) = id 𝒜
  证明: rfl
-/
lemma one_def : (1 : 𝒜 ->+*ᵍ 𝒜) = id 𝒜 := rfl

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : 𝒜 ->+*ᵍ 𝒜)
  statement: f * g = f.comp g
  proof: rfl

中文:
引理 mul_def
  条件: (f g : 𝒜 ->+*ᵍ 𝒜)
  结论: f * g = f.comp g
  证明: rfl
-/
lemma mul_def (f g : 𝒜 ->+*ᵍ 𝒜) : f * g = f.comp g := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : 𝒜 ->+*ᵍ 𝒜) = _root_.id
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : 𝒜 ->+*ᵍ 𝒜) = _root_.id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : 𝒜 ->+*ᵍ 𝒜) = _root_.id := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : 𝒜 ->+*ᵍ 𝒜)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : 𝒜 ->+*ᵍ 𝒜)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (f g : 𝒜 ->+*ᵍ 𝒜) : ⇑(f * g) = f ∘ g := rfl

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (𝒜 ->+*ᵍ 𝒜) where
  body: comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

中文:
实例 instMonoid
  签名: : 幺半群 (𝒜 ->+*ᵍ 𝒜) where
  定义体: comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

Depends on / 依赖: comp_id
-/
instance instMonoid : Monoid (𝒜 ->+*ᵍ 𝒜) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (f : 𝒜 ->+*ᵍ 𝒜) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: rfl

@[simp]

中文:
引理 coe_pow
  条件: (f : 𝒜 ->+*ᵍ 𝒜) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_pow (f : 𝒜 ->+*ᵍ 𝒜) (n : Nat) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : ℬ ->+*ᵍ 𝒞} {f : 𝒜 ->+*ᵍ ℬ} (hf : Function.Surjective f)
  proof: ⟨fun h => ext hf.forall.2 (GradedRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : ℬ ->+*ᵍ 𝒞} {f : 𝒜 ->+*ᵍ ℬ} (hf : 函数.满射 f)
  证明: ⟨fun h => ext hf.forall.2 (GradedRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

Depends on / 依赖: GradedRingHom, GradedRingHom.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : ℬ ->+*ᵍ 𝒞} {f : 𝒜 ->+*ᵍ ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 (GradedRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : ℬ ->+*ᵍ 𝒞} {f₁ f₂ : 𝒜 ->+*ᵍ ℬ} (hg : Function.Injective g)
  proof: ⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

中文:
定理 cancel_left
  条件: {g : ℬ ->+*ᵍ 𝒞} {f₁ f₂ : 𝒜 ->+*ᵍ ℬ} (hg : 函数.单射 g)
  证明: ⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

Depends on / 依赖: comp_apply
-/
theorem cancel_left {g : ℬ ->+*ᵍ 𝒞} {f₁ f₂ : 𝒜 ->+*ᵍ ℬ} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

-- Note: if `GradedAddHom` is added later, then the assumptions can be relaxed.
/--
Definition of `gradedAddHom` / `gradedAddHom` 的定义

English:
definition gradedAddHom
  signature: [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
  body: ⟨f x, map_mem f x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

中文:
定义 gradedAddHom
  签名: [加法子幺半群类 σ A] [加法子幺半群类 τ B]
  定义体: ⟨f x, map_mem f x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
-/
@[simps!] def gradedAddHom [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
    (f : 𝒜 ->+*ᵍ ℬ) (i : ι) : 𝒜 i ->+ ℬ i where
  toFun x := ⟨f x, map_mem f x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/--
Definition of `gradedZeroRingHom` / `gradedZeroRingHom` 的定义

English:
definition gradedZeroRingHom
  signature: [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddMonoid ι]
  body: f.gradedAddHom 0
map_one' := Subtype.ext map_one _
map_mul' _ _ := Subtype.ext map_mul ..

中文:
定义 gradedZeroRingHom
  签名: [加法子幺半群类 σ A] [加法子幺半群类 τ B] [加法幺半群 ι]
  定义体: f.gradedAddHom 0
map_one' := Subtype.ext map_one _
map_mul' _ _ := Subtype.ext map_mul ..
-/
@[simps!] def gradedZeroRingHom [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddMonoid ι]
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ] (f : 𝒜 ->+*ᵍ ℬ) : 𝒜 0 ->+* ℬ 0 where
  __ := f.gradedAddHom 0
map_one' := Subtype.ext map_one _
map_mul' _ _ := Subtype.ext map_mul ..

end GradedRingHom

end SetLike

section GradedRing
variable [DecidableEq ι] [AddMonoid ι] [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
variable (𝒜 : ι -> σ) (ℬ : ι -> τ) [GradedRing 𝒜] [GradedRing ℬ]
variable {F : Type*} [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

-- not simp because `𝒜` cannot be inferred
/--
lemma `DirectSum.decompose_map` / 引理 `DirectSum.decompose_map`

English:
lemma DirectSum.decompose_map
  given: (f : F) {x : A}
  proof: by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]; rw [map_sum]; rw [DirectSum.decompose_sum]; rw [DirectSum.decompose_sum]; rw [map_sum]
  congr 1
  simp [DirectSum.decompose_of_mem _ (map_mem f (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of, Graded

中文:
引理 直和.decompose_map
  条件: (f : F) {x : A}
  证明: by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]; rw [map_sum]; rw [DirectSum.decompose_sum]; rw [DirectSum.decompose_sum]; rw [map_sum]
  congr 1
  simp [DirectSum.decompose_of_mem _ (map_mem f (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of, Graded

Depends on / 依赖: DirectSum, DirectSum.decompose_of_mem, DirectSum.decompose_sum, DirectSum.map_of, DirectSum.sum_support_decompose, GradedRingHom, GradedRingHom.gradedAddHom, Subtype, Subtype.prop, classical, decompose_of_mem, decompose_sum, gradedAddHom, map_mem, map_of, map_sum, sum_support_decompose
-/
lemma DirectSum.decompose_map (f : F) {x : A} :
    DirectSum.decompose ℬ (f x) =
      .map (GradedRingHom.gradedAddHom <| .ofClass f) (.decompose 𝒜 x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]; rw [map_sum]; rw [DirectSum.decompose_sum]; rw [DirectSum.decompose_sum]; rw [map_sum]
  congr 1
  simp [DirectSum.decompose_of_mem _ (map_mem f (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of, GradedRingHom.gradedAddHom]

-- not simp because `ℬ` cannot be inferred
-- for every concrete instance of GradedFunLike, we need one simp lemma
/--
lemma `map_directSumDecompose` / 引理 `map_directSumDecompose`

English:
lemma map_directSumDecompose
  given: (f : F) {x : A} {i : ι}
  proof: by
  simp [DirectSum.decompose_map 𝒜]

中文:
引理 map_directSumDecompose
  条件: (f : F) {x : A} {i : ι}
  证明: by
  simp [DirectSum.decompose_map 𝒜]

Depends on / 依赖: DirectSum, DirectSum.decompose_map, decompose_map
-/
lemma map_directSumDecompose (f : F) {x : A} {i : ι} :
    f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i := by
  simp [DirectSum.decompose_map 𝒜]

/--
lemma `GradedRingHom.map_directSumDecompose` / 引理 `GradedRingHom.map_directSumDecompose`

English:
lemma GradedRingHom.map_directSumDecompose
  given: (f : 𝒜 ->+*ᵍ ℬ) {x : A} {i : ι}
  proof: _root_.map_directSumDecompose ..

中文:
引理 分次环态射.map_directSumDecompose
  条件: (f : 𝒜 ->+*ᵍ ℬ) {x : A} {i : ι}
  证明: _root_.map_directSumDecompose ..
-/
@[simp] lemma GradedRingHom.map_directSumDecompose (f : 𝒜 ->+*ᵍ ℬ) {x : A} {i : ι} :
    f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i :=
  _root_.map_directSumDecompose ..

end GradedRing
