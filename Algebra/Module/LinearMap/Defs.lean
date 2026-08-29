/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# (Semi)linear maps

In this file we define

* `LinearMap σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `Module`s. Here,
  `σ` is a `RingHom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `RingHom.id R`.
  This is denoted by `M →ₗ[R] M₂`. We also add the notation `M →ₗ⋆[R] M₂` for star-linear maps.

* `IsLinearMap R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

We then provide `LinearMap` with the following instances:

* `LinearMap.addCommMonoid` and `LinearMap.addCommGroup`: the elementwise addition structures
  corresponding to addition in the codomain
* `LinearMap.distribMulAction` and `LinearMap.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Mathlib/Algebra/Ring/CompTypeclasses.lean`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `CompatibleSMul`)

## Tags

linear map
-/

@[expose] public section


assert_not_exists TrivialStar DomMulAct Pi.module WCovBy.image Field

open Function

universe u u' v w

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

/--
Definition of `IsLinearMap` / `IsLinearMap` 的定义

English:
structure IsLinearMap
  parameters: (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  axioms and operations (2):
    - map_add : forall x y, f (x + y) = f x + f y
    - map_smul : forall (c : R) (x), f (c • x) = c • f x

中文:
结构 是线性映射
  参数: (R : 类型u) {M : 类型v} {M₂ : 类型 w} [半环 R] [加法交换幺半群 M]
  公理与运算 (2 个):
    - map_add : 对任意 x y, f (x + y) = f x + f y
    - map_smul : 对任意 (c : R) (x), f (c • x) = c • f x
-/
structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M -> M₂) : Prop where
  /-- A linear map preserves addition. -/
  map_add : forall x y, f (x + y) = f x + f y
  /-- A linear map preserves scalar multiplication. -/
  map_smul : forall (c : R) (x), f (c • x) = c • f x

section

/--
Definition of `LinearMap` / `LinearMap` 的定义

English:
structure LinearMap
  parameters: {R S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S) (M : Type*)
  (no additional axioms)

中文:
结构 线性映射
  参数: {R S : 类型} [半环 R] [半环 S] (σ : R ->+* S) (M : 类型)
  (无附加公理)
-/
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R ->+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

/-- The `MulActionHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toMulActionHom

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom

/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " ->ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
notation:25 M " ->ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

/--
Definition of `SemilinearMapClass` / `SemilinearMapClass` 的定义

English:
class SemilinearMapClass
  parameters: (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  extends: AddHomClass F M M₂, MulActionSemiHomClass F σ M M₂
  (no additional axioms)

中文:
类 半线性映射类
  参数: (F : 类型) {R S : outParam 类型} [半环 R] [半环 S]
  继承: 加法态射类 F M M₂, MulActionSemi态射类 F σ M M₂
  (无附加公理)
-/
class SemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam (R ->+* S)) (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module S M₂] [FunLike F M M₂] : Prop
    extends AddHomClass F M M₂, MulActionSemiHomClass F σ M M₂

end

-- `map_smulₛₗ` should be `@[simp]` but doesn't fire due to https://github.com/leanprover/lean4/pull/3701.
-- attribute [simp] map_smulₛₗ

/--
Definition of `LinearMapClass` / `LinearMapClass` 的定义

English:
abbreviation LinearMapClass
  signature: (F : Type*) (R : outParam Type*) (M M₂ : Type*)
  body: SemilinearMapClass F (RingHom.id R) M M₂

中文:
缩写 线性映射类
  签名: (F : 类型) (R : outParam 类型) (M M₂ : 类型)
  定义体: SemilinearMapClass F (RingHom.id R) M M₂

Depends on / 依赖: RingHom, RingHom.id, SemilinearMapClass
-/
abbrev LinearMapClass (F : Type*) (R : outParam Type*) (M M₂ : Type*)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [FunLike F M M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂

/--
lemma `LinearMapClass.map_smul` / 引理 `LinearMapClass.map_smul`

English:
lemma LinearMapClass.map_smul
  statement: {R M M₂ : outParam Type*} [Semiring R] [AddCommMonoid M]
  proof: by rw [map_smul]

中文:
引理 线性映射类.map_smul
  结论: {R M M₂ : outParam 类型} [半环 R] [加法交换幺半群 M]
  证明: by rw [map_smul]
-/
protected lemma LinearMapClass.map_smul {R M M₂ : outParam Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂]
    {F : Type*} [FunLike F M M₂] [LinearMapClass F R M M₂] (f : F) (r : R) (x : M) :
    f (r • x) = r • f x := by rw [map_smul]

namespace SemilinearMapClass

variable (F : Type*)
variable [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R ->+* S}

instance (priority := 100) instAddMonoidHomClass [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    AddMonoidHomClass F M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_zero := fun f =>
      show f 0 = 0 by
        rw [← zero_smul R (0 : M)]; rw [map_smulₛₗ]
        simp }

instance (priority := 100) distribMulActionSemiHomClass
    [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    DistribMulActionSemiHomClass F σ M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_smulₛₗ := fun f c x => by rw [map_smulₛₗ] }

variable {F} (f : F) [FunLike F M M₃] [SemilinearMapClass F σ M M₃]

/--
theorem `map_smul_inv` / 定理 `map_smul_inv`

English:
theorem map_smul_inv
  given: {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M)
  proof: by simp [map_smulₛₗ _]

中文:
定理 map_smul_inv
  条件: {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M)
  证明: by simp [map_smulₛₗ _]
-/
theorem map_smul_inv {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp [map_smulₛₗ _]

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
@[coe]
/--
Definition of `semilinearMap` / `semilinearMap` 的定义

English:
definition semilinearMap
  signature: : M ->ₛₗ[σ] M₃ where
  body: f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

中文:
定义 semilinearMap
  签名: : M ->ₛₗ[σ] M₃ where
  定义体: f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f
-/
def semilinearMap : M ->ₛₗ[σ] M₃ where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

/--
Instance `instCoeToSemilinearMap` / 实例 `instCoeToSemilinearMap`

English:
instance instCoeToSemilinearMap
  signature: : CoeHead F (M ->ₛₗ[σ] M₃) where
  body: semilinearMap f

中文:
实例 instCoeToSemilinearMap
  签名: : CoeHead F (M ->ₛₗ[σ] M₃) where
  定义体: semilinearMap f

Depends on / 依赖: semilinearMap
-/
instance instCoeToSemilinearMap : CoeHead F (M ->ₛₗ[σ] M₃) where
  coe f := semilinearMap f

end SemilinearMapClass

namespace LinearMapClass
variable {F : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  (f : F) [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂]

/--
Definition of `linearMap` / `linearMap` 的定义

English:
abbreviation linearMap
  signature: : M₁ ->ₗ[R] M₂
  body: SemilinearMapClass.semilinearMap f

中文:
缩写 linearMap
  签名: : M₁ ->ₗ[R] M₂
  定义体: SemilinearMapClass.semilinearMap f

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.semilinearMap, semilinearMap
-/
abbrev linearMap : M₁ ->ₗ[R] M₂ := SemilinearMapClass.semilinearMap f

/--
Instance `instCoeToLinearMap` / 实例 `instCoeToLinearMap`

English:
instance instCoeToLinearMap
  signature: : CoeHead F (M₁ ->ₗ[R] M₂) where
  body: SemilinearMapClass.semilinearMap f

中文:
实例 instCoeToLinearMap
  签名: : CoeHead F (M₁ ->ₗ[R] M₂) where
  定义体: SemilinearMapClass.semilinearMap f

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.semilinearMap, semilinearMap
-/
instance instCoeToLinearMap : CoeHead F (M₁ ->ₗ[R] M₂) where
  coe f := SemilinearMapClass.semilinearMap f

end LinearMapClass

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R ->+* S}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (M ->ₛₗ[σ] M₃) M M₃ where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

中文:
实例 instFunLike
  签名: : 函数状 (M ->ₛₗ[σ] M₃) M M₃ where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (M ->ₛₗ[σ] M₃) M M₃ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/--
Instance `semilinearMapClass` / 实例 `semilinearMapClass`

English:
instance semilinearMapClass
  signature: : SemilinearMapClass (M ->ₛₗ[σ] M₃) σ M M₃ where
  body: f.map_add'
  map_smulₛₗ := LinearMap.map_smul'

@[simp, norm_cast]

中文:
实例 semilinearMapClass
  签名: : 半线性映射类 (M ->ₛₗ[σ] M₃) σ M M₃ where
  定义体: f.map_add'
  map_smulₛₗ := LinearMap.map_smul'

@[simp, norm_cast]

Depends on / 依赖: f.map_add, map_add
-/
instance semilinearMapClass : SemilinearMapClass (M ->ₛₗ[σ] M₃) σ M M₃ where
  map_add f := f.map_add'
  map_smulₛₗ := LinearMap.map_smul'

@[simp, norm_cast]
/--
lemma `coe_coe` / 引理 `coe_coe`

English:
lemma coe_coe
  given: {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] {f : F}
  proof: rfl

中文:
引理 coe_coe
  条件: {F : 类型} [函数状 F M M₃] [半线性映射类 F σ M M₃] {f : F}
  证明: rfl
-/
lemma coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] {f : F} :
    ⇑(f : M ->ₛₗ[σ] M₃) = f :=
  rfl

/--
Definition of `toDistribMulActionHom` / `toDistribMulActionHom` 的定义

English:
definition toDistribMulActionHom
  signature: (f : M ->ₛₗ[σ] M₃)
  body: { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]

中文:
定义 toDistribMulActionHom
  签名: (f : M ->ₛₗ[σ] M₃)
  定义体: { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]

Depends on / 依赖: map_zero
-/
def toDistribMulActionHom (f : M ->ₛₗ[σ] M₃) : DistribMulActionHom σ.toMonoidHom M M₃ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]
/--
theorem `coe_toAddHom` / 定理 `coe_toAddHom`

English:
theorem coe_toAddHom
  given: (f : M ->ₛₗ[σ] M₃)
  statement: ⇑f.toAddHom = f
  proof: rfl

@[simp]

中文:
定理 coe_toAddHom
  条件: (f : M ->ₛₗ[σ] M₃)
  结论: ⇑f.toAddHom = f
  证明: rfl

@[simp]
-/
theorem coe_toAddHom (f : M ->ₛₗ[σ] M₃) : ⇑f.toAddHom = f := rfl

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : M ->ₛₗ[σ] M₃}
  statement: f.toFun = (f : M -> M₃)
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : M ->ₛₗ[σ] M₃}
  结论: f.toFun = (f : M -> M₃)
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : M ->ₛₗ[σ] M₃} : f.toFun = (f : M -> M₃) := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : M ->ₛₗ[σ] M₃} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  body: f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

@[simp]

中文:
定义 copy
  签名: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  定义体: f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

@[simp]
-/
protected def copy (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f) : M ->ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

initialize_simps_projections LinearMap (toFun -> apply)

@[simp]

中文:
定理 copy_eq
  条件: (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

initialize_simps_projections LinearMap (toFun -> apply)

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

initialize_simps_projections LinearMap (toFun -> apply)

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {σ : R ->+* S} (f : AddHom M M₃) (h)
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: {σ : R ->+* S} (f : 加法半群态射 M M₃) (h)
  证明: rfl

@[simp]
-/
theorem coe_mk {σ : R ->+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M ->ₛₗ[σ] M₃) : M -> M₃) = f :=
  rfl

@[simp]
/--
theorem `coe_addHom_mk` / 定理 `coe_addHom_mk`

English:
theorem coe_addHom_mk
  given: {σ : R ->+* S} (f : AddHom M M₃) (h)
  proof: rfl

中文:
定理 coe_addHom_mk
  条件: {σ : R ->+* S} (f : 加法半群态射 M M₃) (h)
  证明: rfl
-/
theorem coe_addHom_mk {σ : R ->+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M ->ₛₗ[σ] M₃) : AddHom M M₃) = f :=
  rfl

/--
theorem `coe_semilinearMap` / 定理 `coe_semilinearMap`

English:
theorem coe_semilinearMap
  given: {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] (f : F)
  proof: rfl

中文:
定理 coe_semilinearMap
  条件: {F : 类型} [函数状 F M M₃] [半线性映射类 F σ M M₃] (f : F)
  证明: rfl
-/
theorem coe_semilinearMap {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] (f : F) :
    ((f : M ->ₛₗ[σ] M₃) : M -> M₃) = f :=
  rfl

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  statement: {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
  proof: by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

中文:
定理 toLinearMap_injective
  结论: {F : 类型} [函数状 F M M₃] [半线性映射类 F σ M M₃]
  证明: by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun
-/
theorem toLinearMap_injective {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
    {f g : F} (h : (f : M ->ₛₗ[σ] M₃) = (g : M ->ₛₗ[σ] M₃)) :
    f = g := by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

/-- Identity map as a `LinearMap` -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : M ->ₗ[R] M
  body: { DistribMulActionHom.id R with toFun x := x }

中文:
定义 id
  签名: : M ->ₗ[R] M
  定义体: { DistribMulActionHom.id R with toFun x := x }

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.id
-/
def id : M ->ₗ[R] M :=
  { DistribMulActionHom.id R with toFun x := x }

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : M)
  statement: @id R M _ _ _ x = x
  proof: rfl

@[simp, norm_cast]

中文:
定理 id_apply
  条件: (x : M)
  结论: @id R M _ _ _ x = x
  证明: rfl

@[simp, norm_cast]
-/
theorem id_apply (x : M) : @id R M _ _ _ x = x :=
  rfl

@[simp, norm_cast]
/--
theorem `id_coe` / 定理 `id_coe`

English:
theorem id_coe
  statement: ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _root_.id
  proof: rfl

中文:
定理 id_coe
  结论: ((线性映射.id : M ->ₗ[R] M) : M -> M) = _root_.id
  证明: rfl
-/
theorem id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _root_.id :=
  rfl

/-- A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the identity. -/
@[simps]
/--
Definition of `id'` / `id'` 的定义

English:
definition id'
  signature: {σ : R ->+* R} [RingHomId σ]
  body: x
  map_add' _ _ := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]

中文:
定义 id'
  签名: {σ : R ->+* R} [RingHomId σ]
  定义体: x
  map_add' _ _ := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]
-/
def id' {σ : R ->+* R} [RingHomId σ] : M ->ₛₗ[σ] M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]
/--
theorem `id'_coe` / 定理 `id'_coe`

English:
theorem id'_coe
  given: {σ : R ->+* R} [RingHomId σ]
  statement: ((id' : M ->ₛₗ[σ] M) : M -> M) = _root_.id
  proof: rfl

中文:
定理 id'_coe
  条件: {σ : R ->+* R} [RingHomId σ]
  结论: ((id' : M ->ₛₗ[σ] M) : M -> M) = _root_.id
  证明: rfl
-/
theorem id'_coe {σ : R ->+* R} [RingHomId σ] : ((id' : M ->ₛₗ[σ] M) : M -> M) = _root_.id :=
  rfl

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable (σ : R ->+* S)
variable (fₗ : M ->ₗ[R] M₂) (f g : M ->ₛₗ[σ] M₃)

/--
theorem `isLinear` / 定理 `isLinear`

English:
theorem isLinear
  statement: IsLinearMap R fₗ
  proof: ⟨fₗ.map_add', fₗ.map_smul'⟩

中文:
定理 isLinear
  结论: 是线性映射 R fₗ
  证明: ⟨fₗ.map_add', fₗ.map_smul'⟩

Depends on / 依赖: map_add, map_smul
-/
theorem isLinear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩

variable {fₗ f g σ}

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective (DFunLike.coe : (M ->ₛₗ[σ] M₃) -> _)
  proof: DFunLike.coe_injective

中文:
定理 coe_injective
  结论: 单射 (依赖函数状.coe : (M ->ₛₗ[σ] M₃) -> _)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : Injective (DFunLike.coe : (M ->ₛₗ[σ] M₃) -> _) :=
  DFunLike.coe_injective

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {x x' : M}
  statement: x = x' -> f x = f x'
  proof: DFunLike.congr_arg f

中文:
定理 congr_arg
  条件: {x x' : M}
  结论: x = x' -> f x = f x'
  证明: DFunLike.congr_arg f
-/
protected theorem congr_arg {x x' : M} : x = x' -> f x = f x' :=
  DFunLike.congr_arg f

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : f = g) (x : M)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: (h : f = g) (x : M)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

/--
lemma `mk_coe` / 引理 `mk_coe`

English:
lemma mk_coe
  given: (f : M ->ₛₗ[σ] M₃) (h)
  statement: (mk f h : M ->ₛₗ[σ] M₃) = f
  proof: rfl

中文:
引理 mk_coe
  条件: (f : M ->ₛₗ[σ] M₃) (h)
  结论: (mk f h : M ->ₛₗ[σ] M₃) = f
  证明: rfl
-/
@[simp] lemma mk_coe (f : M ->ₛₗ[σ] M₃) (h) : (mk f h : M ->ₛₗ[σ] M₃) = f := rfl
/--
lemma `mk_coe'` / 引理 `mk_coe'`

English:
lemma mk_coe'
  given: (f : M ->ₛₗ[σ] M₃) (h)
  statement: (mk f.toAddHom h : M ->ₛₗ[σ] M₃) = f
  proof: rfl

中文:
引理 mk_coe'
  条件: (f : M ->ₛₗ[σ] M₃) (h)
  结论: (mk f.toAddHom h : M ->ₛₗ[σ] M₃) = f
  证明: rfl
-/
@[simp] lemma mk_coe' (f : M ->ₛₗ[σ] M₃) (h) : (mk f.toAddHom h : M ->ₛₗ[σ] M₃) = f := rfl

variable (fₗ f g)

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (x y : M)
  statement: f (x + y) = f x + f y
  proof: map_add f x y

中文:
定理 map_add
  条件: (x y : M)
  结论: f (x + y) = f x + f y
  证明: map_add f x y
-/
protected theorem map_add (x y : M) : f (x + y) = f x + f y :=
  map_add f x y

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: f 0 = 0
  proof: map_zero f

中文:
定理 map_zero
  结论: f 0 = 0
  证明: map_zero f
-/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

-- Porting note: `simp` wasn't picking up `map_smulₛₗ` for `LinearMap`s without specifying
-- `map_smulₛₗ f`, so we marked this as `@[simp]` in Mathlib3.
-- For Mathlib4, let's try without the `@[simp]` attribute and hope it won't need to be re-enabled.
-- This has to be re-tagged as `@[simp]` in https://github.com/leanprover-community/mathlib4/pull/8386 (see also https://github.com/leanprover/lean4/issues/3107).
@[simp]
/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (c : R) (x : M)
  statement: f (c • x) = σ c • f x
  proof: map_smulₛₗ f c x

中文:
定理 map_smulₛₗ
  条件: (c : R) (x : M)
  结论: f (c • x) = σ c • f x
  证明: map_smulₛₗ f c x
-/
protected theorem map_smulₛₗ (c : R) (x : M) : f (c • x) = σ c • f x :=
  map_smulₛₗ f c x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (c : R) (x : M)
  statement: fₗ (c • x) = c • fₗ x
  proof: map_smul fₗ c x

中文:
定理 map_smul
  条件: (c : R) (x : M)
  结论: fₗ (c • x) = c • fₗ x
  证明: map_smul fₗ c x
-/
protected theorem map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  map_smul fₗ c x

/--
theorem `map_smul_inv` / 定理 `map_smul_inv`

English:
theorem map_smul_inv
  given: {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M)
  proof: by simp

@[simp]

中文:
定理 map_smul_inv
  条件: {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M)
  证明: by simp

@[simp]
-/
protected theorem map_smul_inv {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp

@[simp]
/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (h : Function.Injective f) {x : M}
  statement: f x = 0 ↔ x = 0
  proof: _root_.map_eq_zero_iff f h

中文:
定理 map_eq_zero_iff
  条件: (h : 函数.单射 f) {x : M}
  结论: f x = 0 ↔ x = 0
  证明: _root_.map_eq_zero_iff f h
-/
protected theorem map_eq_zero_iff (h : Function.Injective f) {x : M} : f x = 0 ↔ x = 0 :=
  _root_.map_eq_zero_iff f h

variable (M M₂)

/--
Definition of `CompatibleSMul` / `CompatibleSMul` 的定义

English:
class CompatibleSMul
  parameters: (R S : Type*) [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
  axioms and operations (1):
    - map_smul : forall (fₗ : M ->ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x

中文:
类 余mpatibleSMul
  参数: (R S : 类型) [半环 S] [标量乘法 R M] [模 S M] [标量乘法 R M₂]
  公理与运算 (1 个):
    - map_smul : 对任意 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x
-/
class CompatibleSMul (R S : Type*) [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
  [Module S M₂] : Prop where
  /-- Scalar multiplication by `R` of `M` can be moved through linear maps. -/
  map_smul : forall (fₗ : M ->ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x

variable {M M₂}

section

variable {R S : Type*} [Semiring S] [SMul R M] [Module S M] [SMul R M₂] [Module S M₂]

instance (priority := 100) IsScalarTower.compatibleSMul [SMul R S]
    [IsScalarTower R S M] [IsScalarTower R S M₂] :
    CompatibleSMul M M₂ R S :=
  ⟨fun fₗ c x => by rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩

/--
Instance `IsScalarTower.compatibleSMul'` / 实例 `IsScalarTower.compatibleSMul'`

English:
instance IsScalarTower.compatibleSMul'
  signature: [SMul R S] [IsScalarTower R S M]
  body: (IsScalarTower.smulHomClass R S M (S ->ₗ[S] M)).map_smulₛₗ

@[simp]

中文:
实例 标量塔.compatibleSMul'
  签名: [标量乘法 R S] [标量塔 R S M]
  定义体: (IsScalarTower.smulHomClass R S M (S ->ₗ[S] M)).map_smulₛₗ

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.smulHomClass, smulHomClass
-/
instance IsScalarTower.compatibleSMul' [SMul R S] [IsScalarTower R S M] :
    CompatibleSMul S M R S where
  map_smul := (IsScalarTower.smulHomClass R S M (S ->ₗ[S] M)).map_smulₛₗ

@[simp]
/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  given: [CompatibleSMul M M₂ R S] (fₗ : M ->ₗ[S] M₂) (c : R) (x : M)
  proof: CompatibleSMul.map_smul fₗ c x

中文:
定理 map_smul_of_tower
  条件: [余mpatibleSMul M M₂ R S] (fₗ : M ->ₗ[S] M₂) (c : R) (x : M)
  证明: CompatibleSMul.map_smul fₗ c x

Depends on / 依赖: CompatibleSMul, CompatibleSMul.map_smul, map_smul
-/
theorem map_smul_of_tower [CompatibleSMul M M₂ R S] (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  CompatibleSMul.map_smul fₗ c x

/--
theorem `_root_.LinearMapClass.map_smul_of_tower` / 定理 `_root_.LinearMapClass.map_smul_of_tower`

English:
theorem _root_.LinearMapClass.map_smul_of_tower
  statement: {F : Type*} [CompatibleSMul M M₂ R S]
  proof: LinearMap.CompatibleSMul.map_smul (fₗ : M ->ₗ[S] M₂) c x

中文:
定理 _root_.线性映射类.map_smul_of_tower
  结论: {F : 类型} [余mpatibleSMul M M₂ R S]
  证明: LinearMap.CompatibleSMul.map_smul (fₗ : M ->ₗ[S] M₂) c x

Depends on / 依赖: CompatibleSMul, LinearMap, LinearMap.CompatibleSMul.map_smul, map_smul
-/
theorem _root_.LinearMapClass.map_smul_of_tower {F : Type*} [CompatibleSMul M M₂ R S]
    [FunLike F M M₂] [LinearMapClass F S M M₂] (fₗ : F) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  LinearMap.CompatibleSMul.map_smul (fₗ : M ->ₗ[S] M₂) c x

variable (R R) in
/--
theorem `isScalarTower_of_injective` / 定理 `isScalarTower_of_injective`

English:
theorem isScalarTower_of_injective
  statement: [SMul R S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂]
  proof: hf by rw [f.map_smul_of_tower r, map_smul, map_smul, smul_assoc]

中文:
定理 isScalarTower_of_injective
  结论: [标量乘法 R S] [余mpatibleSMul M M₂ R S] [标量塔 R S M₂]
  证明: hf by rw [f.map_smul_of_tower r, map_smul, map_smul, smul_assoc]

Depends on / 依赖: f.map_smul_of_tower, map_smul, map_smul_of_tower, smul_assoc
-/
theorem isScalarTower_of_injective [SMul R S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂]
    (f : M ->ₗ[S] M₂) (hf : Function.Injective f) : IsScalarTower R S M where
smul_assoc r s _ := hf by rw [f.map_smul_of_tower r, map_smul, map_smul, smul_assoc]

/--
lemma `_root_.map_zsmul_unit` / 引理 `_root_.map_zsmul_unit`

English:
lemma _root_.map_zsmul_unit
  statement: {F M N : Type*}
  proof: by
  simp [Units.smul_def]

中文:
引理 _root_.map_zsmul_unit
  结论: {F M N : 类型}
  证明: by
  simp [Units.smul_def]
-/
@[simp] lemma _root_.map_zsmul_unit {F M N : Type*}
    [AddGroup M] [AddGroup N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (c : Intˣ) (m : M) :
    f (c • m) = c • f m := by
  simp [Units.smul_def]

end

variable (R) in
/--
theorem `isLinearMap_of_compatibleSMul` / 定理 `isLinearMap_of_compatibleSMul`

English:
theorem isLinearMap_of_compatibleSMul
  statement: [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]
  proof: map_add f
  map_smul := map_smul_of_tower f

中文:
定理 isLinearMap_of_compatibleSMul
  结论: [模 S M] [模 S M₂] [余mpatibleSMul M M₂ R S]
  证明: map_add f
  map_smul := map_smul_of_tower f

Depends on / 依赖: map_add
-/
theorem isLinearMap_of_compatibleSMul [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]
    (f : M ->ₗ[S] M₂) : IsLinearMap R f where
  map_add := map_add f
  map_smul := map_smul_of_tower f

-- See note [implicit instance arguments]
/--
Definition of `toAddMonoidHom` / `toAddMonoidHom` 的定义

English:
definition toAddMonoidHom
  signature: {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+* S} (f : M₁ ->ₛₗ[σ] M₂)
  body: f
  map_zero' := f.map_zero
  map_add' := f.map_add

omit [Module R M₂] in
@[simp]

中文:
定义 toAddMonoidHom
  签名: {modM₁ : 模 R M₁} {modM₂ : 模 S M₂} {σ : R ->+* S} (f : M₁ ->ₛₗ[σ] M₂)
  定义体: f
  map_zero' := f.map_zero
  map_add' := f.map_add

omit [Module R M₂] in
@[simp]
-/
def toAddMonoidHom {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+* S} (f : M₁ ->ₛₗ[σ] M₂) :
    M₁ ->+ M₂ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add

omit [Module R M₂] in
@[simp]
/--
lemma `toAddMonoidHom_coe` / 引理 `toAddMonoidHom_coe`

English:
lemma toAddMonoidHom_coe
  statement: {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+* S}
  proof: rfl

中文:
引理 toAddMonoidHom_coe
  结论: {modM₁ : 模 R M₁} {modM₂ : 模 S M₂} {σ : R ->+* S}
  证明: rfl
-/
lemma toAddMonoidHom_coe {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+* S}
    (f : M₁ ->ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f := rfl

section RestrictScalars

variable (R)
variable [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (fₗ : M ->ₗ[S] M₂)
  body: fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower

中文:
定义 restrictScalars
  签名: (fₗ : M ->ₗ[S] M₂)
  定义体: fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower
-/
@[coe] def restrictScalars (fₗ : M ->ₗ[S] M₂) : M ->ₗ[R] M₂ where
  toFun := fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower

/--
Instance `coeIsScalarTower` / 实例 `coeIsScalarTower`

English:
instance coeIsScalarTower
  signature: : CoeHTCT (M ->ₗ[S] M₂) (M ->ₗ[R] M₂)
  body: ⟨restrictScalars R⟩

@[simp, norm_cast]

中文:
实例 coeIsScalarTower
  签名: : CoeHTCT (M ->ₗ[S] M₂) (M ->ₗ[R] M₂)
  定义体: ⟨restrictScalars R⟩

@[simp, norm_cast]

Depends on / 依赖: restrictScalars
-/
instance coeIsScalarTower : CoeHTCT (M ->ₗ[S] M₂) (M ->ₗ[R] M₂) :=
  ⟨restrictScalars R⟩

@[simp, norm_cast]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : M ->ₗ[S] M₂)
  statement: ((f : M ->ₗ[R] M₂) : M -> M₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (f : M ->ₗ[S] M₂)
  结论: ((f : M ->ₗ[R] M₂) : M -> M₂) = f
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (f : M ->ₗ[S] M₂) : ((f : M ->ₗ[R] M₂) : M -> M₂) = f :=
  rfl

@[simp]
/--
lemma `restrictScalars_self` / 引理 `restrictScalars_self`

English:
lemma restrictScalars_self
  given: (f : M ->ₗ[R] M₂)
  statement: f.restrictScalars R = f
  proof: rfl

中文:
引理 restrictScalars_self
  条件: (f : M ->ₗ[R] M₂)
  结论: f.restrictScalars R = f
  证明: rfl
-/
lemma restrictScalars_self (f : M ->ₗ[R] M₂) : f.restrictScalars R = f := rfl

/--
theorem `restrictScalars_apply` / 定理 `restrictScalars_apply`

English:
theorem restrictScalars_apply
  given: (fₗ : M ->ₗ[S] M₂) (x)
  statement: restrictScalars R fₗ x = fₗ x
  proof: rfl

中文:
定理 restrictScalars_apply
  条件: (fₗ : M ->ₗ[S] M₂) (x)
  结论: restrictScalars R fₗ x = fₗ x
  证明: rfl
-/
theorem restrictScalars_apply (fₗ : M ->ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ x :=
  rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h =>
  ext (LinearMap.congr_fun h :)

@[simp]

中文:
定理 restrictScalars_injective
  证明: fun _ _ h =>
  ext (LinearMap.congr_fun h :)

@[simp]
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂) := fun _ _ h =>
  ext (LinearMap.congr_fun h :)

@[simp]
/--
theorem `restrictScalars_inj` / 定理 `restrictScalars_inj`

English:
theorem restrictScalars_inj
  given: (fₗ gₗ : M ->ₗ[S] M₂)
  proof: (restrictScalars_injective R).eq_iff

@[simp]

中文:
定理 restrictScalars_inj
  条件: (fₗ gₗ : M ->ₗ[S] M₂)
  证明: (restrictScalars_injective R).eq_iff

@[simp]

Depends on / 依赖: eq_iff, restrictScalars_injective
-/
theorem restrictScalars_inj (fₗ gₗ : M ->ₗ[S] M₂) :
    fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ :=
  (restrictScalars_injective R).eq_iff

@[simp]
/--
lemma `restrictScalars_id` / 引理 `restrictScalars_id`

English:
lemma restrictScalars_id
  given: [CompatibleSMul M M R S]
  proof: rfl

中文:
引理 restrictScalars_id
  条件: [余mpatibleSMul M M R S]
  证明: rfl

Depends on / 依赖: restrictScalars
-/
lemma restrictScalars_id [CompatibleSMul M M R S] :
    (id (R := S) (M := M)).restrictScalars R = id := rfl

end RestrictScalars

/--
theorem `toAddMonoidHom_injective` / 定理 `toAddMonoidHom_injective`

English:
theorem toAddMonoidHom_injective
  proof: fun fₗ gₗ h =>
ext (DFunLike.congr_fun h : forall x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)

中文:
定理 toAddMonoidHom_injective
  证明: fun fₗ gₗ h =>
ext (DFunLike.congr_fun h : forall x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)
-/
theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃) := fun fₗ gₗ h =>
ext (DFunLike.congr_fun h : forall x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext high]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1)
  statement: f = g
  proof: ext fun x => by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

中文:
定理 ext_ring
  条件: {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1)
  结论: f = g
  证明: ext fun x => by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

Depends on / 依赖: f.map_smul, g.map_smul, mul_one, smul_eq_mul
-/
theorem ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x => by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

end

/-- Interpret a `RingHom` `f` as an `f`-semilinear map. -/
@[simps]
/--
Definition of `_root_.RingHom.toSemilinearMap` / `_root_.RingHom.toSemilinearMap` 的定义

English:
definition _root_.RingHom.toSemilinearMap
  signature: (f : R ->+* S)
  body: { f with
    map_smul' := f.map_mul }

中文:
定义 _root_.环态射.toSemilinearMap
  签名: (f : R ->+* S)
  定义体: { f with
    map_smul' := f.map_mul }

Depends on / 依赖: f.map_mul, map_mul, map_smul
-/
def _root_.RingHom.toSemilinearMap (f : R ->+* S) : R ->ₛₗ[f] S :=
  { f with
    map_smul' := f.map_mul }

/--
theorem `_root_.RingHom.coe_toSemilinearMap` / 定理 `_root_.RingHom.coe_toSemilinearMap`

English:
theorem _root_.RingHom.coe_toSemilinearMap
  given: (f : R ->+* S)
  statement: ⇑f.toSemilinearMap = f
  proof: rfl

中文:
定理 _root_.环态射.coe_toSemilinearMap
  条件: (f : R ->+* S)
  结论: ⇑f.toSemilinearMap = f
  证明: rfl
-/
@[simp] theorem _root_.RingHom.coe_toSemilinearMap (f : R ->+* S) : ⇑f.toSemilinearMap = f := rfl

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃}

/-- Composition of two linear maps is a linear map -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₂] M₂)
  body: f (g x)
  map_add' := by simp only [map_add, forall_const]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]

中文:
定义 comp
  签名: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₂] M₂)
  定义体: f (g x)
  map_add' := by simp only [map_add, forall_const]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]
-/
def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₂] M₂) :
    M₁ ->ₛₗ[σ₁₃] M₃ where
  toFun x := f (g x)
  map_add' := by simp only [map_add, forall_const]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₂] M₂)

/-- `∘ₗ` is notation for composition of two linear (not semilinear!) maps into a linear map.
This is useful when Lean is struggling to infer the `RingHomCompTriple` instance. -/
notation3:80 (name := compNotation) f:81 " ∘ₗ " g:80 =>
  LinearMap.comp (σ₁₂ := RingHom.id _) (σ₂₃ := RingHom.id _) (σ₁₃ := RingHom.id _) f g

@[inherit_doc] infixr:90 " ∘ₛₗ " => comp

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (x : M₁)
  statement: f.comp g x = f (g x)
  proof: rfl

@[simp, norm_cast]

中文:
定理 comp_apply
  条件: (x : M₁)
  结论: f.comp g x = f (g x)
  证明: rfl

@[simp, norm_cast]
-/
theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  statement: (f.comp g : M₁ -> M₃) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  结论: (f.comp g : M₁ -> M₃) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: f.comp id = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  结论: f.comp id = f
  证明: rfl

@[simp]
-/
theorem comp_id : f.comp id = f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: id.comp f = f
  proof: rfl

中文:
定理 id_comp
  结论: id.comp f = f
  证明: rfl
-/
theorem id_comp : id.comp f = f :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  proof: rfl

中文:
定理 comp_assoc
  证明: rfl
-/
theorem comp_assoc
    {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
    {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄}
    [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
    (f : M₁ ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (h : M₃ ->ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ ->ₛₗ[σ₂₄] M₄).comp f : M₁ ->ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ ->ₛₗ[σ₁₃] M₃) :=
  rfl

variable {f g} {f' : M₂ ->ₛₗ[σ₂₃] M₃} {g' : M₁ ->ₛₗ[σ₁₂] M₂}

/--
lemma `_root_.Function.Surjective.injective_linearMapComp_right` / 引理 `_root_.Function.Surjective.injective_linearMapComp_right`

English:
lemma _root_.Function.Surjective.injective_linearMapComp_right
  given: (hg : Surjective g)
  proof: fun _ _ h => ext hg.forall.2 (LinearMap.ext_iff.1 h)

@[simp]

中文:
引理 _root_.函数.满射.injective_linearMapComp_right
  条件: (hg : 满射 g)
  证明: fun _ _ h => ext hg.forall.2 (LinearMap.ext_iff.1 h)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, hg.forall
-/
lemma _root_.Function.Surjective.injective_linearMapComp_right (hg : Surjective g) :
    Injective fun f : M₂ ->ₛₗ[σ₂₃] M₃ => f.comp g :=
fun _ _ h => ext hg.forall.2 (LinearMap.ext_iff.1 h)

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: (hg : Surjective g)
  statement: f.comp g = f'.comp g ↔ f = f'
  proof: hg.injective_linearMapComp_right.eq_iff

中文:
定理 cancel_right
  条件: (hg : 满射 g)
  结论: f.comp g = f'.comp g ↔ f = f'
  证明: hg.injective_linearMapComp_right.eq_iff

Depends on / 依赖: eq_iff, hg.injective_linearMapComp_right.eq_iff, injective_linearMapComp_right
-/
theorem cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  hg.injective_linearMapComp_right.eq_iff

/--
lemma `_root_.Function.Injective.injective_linearMapComp_left` / 引理 `_root_.Function.Injective.injective_linearMapComp_left`

English:
lemma _root_.Function.Injective.injective_linearMapComp_left
  given: (hf : Injective f)
  proof: fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) => ext fun x => hf by rw [← comp_apply, h, comp_apply]

中文:
引理 _root_.函数.单射.injective_linearMapComp_left
  条件: (hf : 单射 f)
  证明: fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) => ext fun x => hf by rw [← comp_apply, h, comp_apply]

Depends on / 依赖: comp_apply, f.comp
-/
lemma _root_.Function.Injective.injective_linearMapComp_left (hf : Injective f) :
    Injective fun g : M₁ ->ₛₗ[σ₁₂] M₂ => f.comp g :=
fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) => ext fun x => hf by rw [← comp_apply, h, comp_apply]

/--
theorem `surjective_comp_left_of_exists_rightInverse` / 定理 `surjective_comp_left_of_exists_rightInverse`

English:
theorem surjective_comp_left_of_exists_rightInverse
  statement: {σ₃₂ : R₃ ->+* R₂}
  proof: by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← comp_assoc, hf', id_comp]

@[simp]

中文:
定理 surjective_comp_left_of_存在_rightInverse
  结论: {σ₃₂ : R₃ ->+* R₂}
  证明: by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← comp_assoc, hf', id_comp]

@[simp]

Depends on / 依赖: comp_assoc, id_comp, simp_rw
-/
theorem surjective_comp_left_of_exists_rightInverse {σ₃₂ : R₃ ->+* R₂}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    (hf : exists f' : M₃ ->ₛₗ[σ₃₂] M₂, f.comp f' = .id) :
    Surjective fun g : M₁ ->ₛₗ[σ₁₂] M₂ => f.comp g := by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← comp_assoc, hf', id_comp]

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: (hf : Injective f)
  statement: f.comp g = f.comp g' ↔ g = g'
  proof: hf.injective_linearMapComp_left.eq_iff

中文:
定理 cancel_left
  条件: (hf : 单射 f)
  结论: f.comp g = f.comp g' ↔ g = g'
  证明: hf.injective_linearMapComp_left.eq_iff

Depends on / 依赖: eq_iff, hf.injective_linearMapComp_left.eq_iff, injective_linearMapComp_left
-/
theorem cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  hf.injective_linearMapComp_left.eq_iff

end

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module S M₂] {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ']

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
@[implicit_reducible]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : M ->ₛₗ[σ] M₂) (g : M₂ -> M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f)
  body: by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y => by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b => by
        rw [← h₁ (g (a • b))]; rw [← h₁ (σ' a • g b)]
        simp [h₂] }

中文:
定义 inverse
  签名: (f : M ->ₛₗ[σ] M₂) (g : M₂ -> M) (h₁ : 左逆 g f) (h₂ : 右逆 g f)
  定义体: by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y => by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b => by
        rw [← h₁ (g (a • b))]; rw [← h₁ (σ' a • g b)]
        simp [h₂] }

Depends on / 依赖: Function, Function.RightInverse, LeftInverse, RightInverse, map_add, map_smul
-/
def inverse (f : M ->ₛₗ[σ] M₂) (g : M₂ -> M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    M₂ ->ₛₗ[σ'] M := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y => by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b => by
        rw [← h₁ (g (a • b))]; rw [← h₁ (σ' a • g b)]
        simp [h₂] }

variable (f : M ->ₛₗ[σ] M₂) (g : M₂ ->ₛₗ[σ'] M) (h : g.comp f = .id)

include h

/--
theorem `injective_of_comp_eq_id` / 定理 `injective_of_comp_eq_id`

English:
theorem injective_of_comp_eq_id
  statement: Injective f
  proof: .of_comp (f := g) by simp_rw [← coe_comp, h, id_coe, bijective_id.1]

中文:
定理 injective_of_comp_eq_id
  结论: 单射 f
  证明: .of_comp (f := g) by simp_rw [← coe_comp, h, id_coe, bijective_id.1]

Depends on / 依赖: bijective_id, coe_comp, id_coe, of_comp, simp_rw
-/
theorem injective_of_comp_eq_id : Injective f :=
.of_comp (f := g) by simp_rw [← coe_comp, h, id_coe, bijective_id.1]

/--
theorem `surjective_of_comp_eq_id` / 定理 `surjective_of_comp_eq_id`

English:
theorem surjective_of_comp_eq_id
  statement: Surjective g
  proof: .of_comp (g := f) by simp_rw [← coe_comp, h, id_coe, bijective_id.2]

中文:
定理 surjective_of_comp_eq_id
  结论: 满射 g
  证明: .of_comp (g := f) by simp_rw [← coe_comp, h, id_coe, bijective_id.2]

Depends on / 依赖: bijective_id, coe_comp, id_coe, of_comp, simp_rw
-/
theorem surjective_of_comp_eq_id : Surjective g :=
.of_comp (g := f) by simp_rw [← coe_comp, h, id_coe, bijective_id.2]

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommGroup M₂]
variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R ->+* S}
variable (f : M ->ₛₗ[σ] M₂)

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (x : M)
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  条件: (x : M)
  结论: f (-x) = -f x
  证明: map_neg f x
-/
protected theorem map_neg (x : M) : f (-x) = -f x :=
  map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : M)
  statement: f (x - y) = f x - f y
  proof: map_sub f x y

中文:
定理 map_sub
  条件: (x y : M)
  结论: f (x - y) = f x - f y
  证明: map_sub f x y
-/
protected theorem map_sub (x y : M) : f (x - y) = f x - f y :=
  map_sub f x y

/--
Instance `CompatibleSMul.intModule` / 实例 `CompatibleSMul.intModule`

English:
instance CompatibleSMul.intModule
  signature: {S : Type*} [Semiring S] [Module S M] [Module S M₂]
  body: ⟨fun fₗ c x => by
    induction c with
    | zero => simp
    | succ n ih => simp [add_smul]
    | pred n ih => simp [sub_smul]⟩

中文:
实例 余mpatibleSMul.intModule
  签名: {S : 类型} [半环 S] [模 S M] [模 S M₂]
  定义体: ⟨fun fₗ c x => by
    induction c with
    | zero => simp
    | succ n ih => simp [add_smul]
    | pred n ih => simp [sub_smul]⟩

Depends on / 依赖: add_smul, sub_smul
-/
instance CompatibleSMul.intModule {S : Type*} [Semiring S] [Module S M] [Module S M₂] :
    CompatibleSMul M M₂ Int S :=
  ⟨fun fₗ c x => by
    induction c with
    | zero => simp
    | succ n ih => simp [add_smul]
    | pred n ih => simp [sub_smul]⟩

/--
Instance `CompatibleSMul.units` / 实例 `CompatibleSMul.units`

English:
instance CompatibleSMul.units
  signature: {R S : Type*} [Monoid R] [MulAction R M] [MulAction R M₂]
  body: ⟨fun fₗ c x => (CompatibleSMul.map_smul fₗ (c : R) x :)⟩

中文:
实例 余mpatibleSMul.units
  签名: {R S : 类型} [幺半群 R] [乘法作用 R M] [乘法作用 R M₂]
  定义体: ⟨fun fₗ c x => (CompatibleSMul.map_smul fₗ (c : R) x :)⟩

Depends on / 依赖: CompatibleSMul, CompatibleSMul.map_smul, map_smul
-/
instance CompatibleSMul.units {R S : Type*} [Monoid R] [MulAction R M] [MulAction R M₂]
    [Semiring S] [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S] : CompatibleSMul M M₂ Rˣ S :=
  ⟨fun fₗ c x => (CompatibleSMul.map_smul fₗ (c : R) x :)⟩

end AddCommGroup

end LinearMap

namespace Module

/-- `g : R →+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
/--
Definition of `compHom.toLinearMap` / `compHom.toLinearMap` 的定义

English:
definition compHom.toLinearMap
  signature: {R S : Type*} [Semiring R] [Semiring S] (g : R ->+* S)
  body: compHom S g; R ->ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R -> S)
    map_add' := g.map_add
    map_smul' := g.map_mul }

中文:
定义 compHom.toLinearMap
  签名: {R S : 类型} [半环 R] [半环 S] (g : R ->+* S)
  定义体: compHom S g; R ->ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R -> S)
    map_add' := g.map_add
    map_smul' := g.map_mul }

Depends on / 依赖: compHom
-/
def compHom.toLinearMap {R S : Type*} [Semiring R] [Semiring S] (g : R ->+* S) :
    letI := compHom S g; R ->ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R -> S)
    map_add' := g.map_add
    map_smul' := g.map_mul }

end Module

namespace DistribMulActionHom

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Semiring R] [Module R M] [Semiring S] [Module S M₂] [Module R M₃]
variable {σ : R ->+* S}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilinearMapClass (M ->ₑ+[σ.toMonoidHom] M₂) σ M M₂

中文:
实例 :
  签名: 半线性映射类 (M ->ₑ+[σ.toMonoidHom] M₂) σ M M₂
-/
instance : SemilinearMapClass (M ->ₑ+[σ.toMonoidHom] M₂) σ M M₂ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (M ->+[R] M₃) R M M₃

中文:
实例 :
  签名: 线性映射类 (M ->+[R] M₃) R M M₃
-/
instance : LinearMapClass (M ->+[R] M₃) R M M₃ where

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : M ->ₑ+[σ.toMonoidHom] M₂)
  statement: ((f : M ->ₛₗ[σ] M₂) : M -> M₂) = f
  proof: rfl

中文:
定理 coe_toLinearMap
  条件: (f : M ->ₑ+[σ.toMonoidHom] M₂)
  结论: ((f : M ->ₛₗ[σ] M₂) : M -> M₂) = f
  证明: rfl
-/
theorem coe_toLinearMap (f : M ->ₑ+[σ.toMonoidHom] M₂) : ((f : M ->ₛₗ[σ] M₂) : M -> M₂) = f :=
  rfl

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  statement: {f g : M ->ₑ+[σ.toMonoidHom] M₂}
  proof: by
  ext m
  exact LinearMap.congr_fun h m

中文:
定理 toLinearMap_injective
  结论: {f g : M ->ₑ+[σ.toMonoidHom] M₂}
  证明: by
  ext m
  exact LinearMap.congr_fun h m

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem toLinearMap_injective {f g : M ->ₑ+[σ.toMonoidHom] M₂}
    (h : (f : M ->ₛₗ[σ] M₂) = (g : M ->ₛₗ[σ] M₂)) :
    f = g := by
  ext m
  exact LinearMap.congr_fun h m

end DistribMulActionHom

namespace IsLinearMap

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : M -> M₂) (lin : IsLinearMap R f)
  body: f
  map_add' := lin.1
  map_smul' := lin.2

@[simp]

中文:
定义 mk'
  签名: (f : M -> M₂) (lin : 是线性映射 R f)
  定义体: f
  map_add' := lin.1
  map_smul' := lin.2

@[simp]
-/
def mk' (f : M -> M₂) (lin : IsLinearMap R f) : M ->ₗ[R] M₂ where
  toFun := f
  map_add' := lin.1
  map_smul' := lin.2

@[simp]
/--
theorem `mk'_apply` / 定理 `mk'_apply`

English:
theorem mk'_apply
  given: {f : M -> M₂} (lin : IsLinearMap R f) (x : M)
  statement: mk' f lin x = f x
  proof: rfl

中文:
定理 mk'_apply
  条件: {f : M -> M₂} (lin : 是线性映射 R f) (x : M)
  结论: mk' f lin x = f x
  证明: rfl
-/
theorem mk'_apply {f : M -> M₂} (lin : IsLinearMap R f) (x : M) : mk' f lin x = f x :=
  rfl

/--
theorem `isLinearMap_smul` / 定理 `isLinearMap_smul`

English:
theorem isLinearMap_smul
  given: {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R)
  proof: by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]

中文:
定理 isLinearMap_smul
  条件: {R M : 类型} [交换半环 R] [加法交换幺半群 M] [模 R M] (c : R)
  证明: by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, mul_comm, smul_add, smul_smul
-/
theorem isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R) :
    IsLinearMap R fun z : M => c • z := by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]

/--
theorem `isLinearMap_smul'` / 定理 `isLinearMap_smul'`

English:
theorem isLinearMap_smul'
  given: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M)
  proof: IsLinearMap.mk (fun x y => add_smul x y a) fun x y => mul_smul x y a

中文:
定理 isLinearMap_smul'
  条件: {R M : 类型} [半环 R] [加法交换幺半群 M] [模 R M] (a : M)
  证明: IsLinearMap.mk (fun x y => add_smul x y a) fun x y => mul_smul x y a

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, add_smul, mul_smul
-/
theorem isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M) :
    IsLinearMap R fun c : R => c • a :=
  IsLinearMap.mk (fun x y => add_smul x y a) fun x y => mul_smul x y a

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: {f : M -> M₂} (lin : IsLinearMap R f)
  statement: f (0 : M) = (0 : M₂)
  proof: (lin.mk' f).map_zero

中文:
定理 map_zero
  条件: {f : M -> M₂} (lin : 是线性映射 R f)
  结论: f (0 : M) = (0 : M₂)
  证明: (lin.mk' f).map_zero

Depends on / 依赖: lin.mk, map_zero
-/
theorem map_zero {f : M -> M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂) :=
  (lin.mk' f).map_zero

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂]

/--
theorem `isLinearMap_neg` / 定理 `isLinearMap_neg`

English:
theorem isLinearMap_neg
  statement: IsLinearMap R fun z : M => -z
  proof: IsLinearMap.mk neg_add fun x y => (smul_neg x y).symm

中文:
定理 isLinearMap_neg
  结论: 是线性映射 R fun z : M => -z
  证明: IsLinearMap.mk neg_add fun x y => (smul_neg x y).symm

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, neg_add, smul_neg
-/
theorem isLinearMap_neg : IsLinearMap R fun z : M => -z :=
  IsLinearMap.mk neg_add fun x y => (smul_neg x y).symm

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: {f : M -> M₂} (lin : IsLinearMap R f) (x : M)
  statement: f (-x) = -f x
  proof: (lin.mk' f).map_neg x

中文:
定理 map_neg
  条件: {f : M -> M₂} (lin : 是线性映射 R f) (x : M)
  结论: f (-x) = -f x
  证明: (lin.mk' f).map_neg x

Depends on / 依赖: lin.mk, map_neg
-/
theorem map_neg {f : M -> M₂} (lin : IsLinearMap R f) (x : M) : f (-x) = -f x :=
  (lin.mk' f).map_neg x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: {f : M -> M₂} (lin : IsLinearMap R f) (x y : M)
  statement: f (x - y) = f x - f y
  proof: (lin.mk' f).map_sub x y

中文:
定理 map_sub
  条件: {f : M -> M₂} (lin : 是线性映射 R f) (x y : M)
  结论: f (x - y) = f x - f y
  证明: (lin.mk' f).map_sub x y

Depends on / 依赖: lin.mk, map_sub
-/
theorem map_sub {f : M -> M₂} (lin : IsLinearMap R f) (x y : M) : f (x - y) = f x - f y :=
  (lin.mk' f).map_sub x y

end AddCommGroup

end IsLinearMap

/--
Definition of `AddMonoidHom.toNatLinearMap` / `AddMonoidHom.toNatLinearMap` 的定义

English:
definition AddMonoidHom.toNatLinearMap
  signature: [AddCommMonoid M] [AddCommMonoid M₂] (f : M ->+ M₂)
  body: f
  map_add' := f.map_add
  map_smul' := map_nsmul f

中文:
定义 加法幺半群态射.to自然数LinearMap
  签名: [加法交换幺半群 M] [加法交换幺半群 M₂] (f : M ->+ M₂)
  定义体: f
  map_add' := f.map_add
  map_smul' := map_nsmul f
-/
def AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M ->+ M₂) :
    M ->ₗ[Nat] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f

/--
theorem `AddMonoidHom.toNatLinearMap_injective` / 定理 `AddMonoidHom.toNatLinearMap_injective`

English:
theorem AddMonoidHom.toNatLinearMap_injective
  given: [AddCommMonoid M] [AddCommMonoid M₂]
  proof: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

中文:
定理 加法幺半群态射.to自然数LinearMap_injective
  条件: [加法交换幺半群 M] [加法交换幺半群 M₂]
  证明: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/--
theorem `AddMonoidHom.coe_toNatLinearMap` / 定理 `AddMonoidHom.coe_toNatLinearMap`

English:
theorem AddMonoidHom.coe_toNatLinearMap
  given: [AddCommMonoid M] [AddCommMonoid M₂] (f : M ->+ M₂)
  proof: rfl

中文:
定理 加法幺半群态射.coe_to自然数LinearMap
  条件: [加法交换幺半群 M] [加法交换幺半群 M₂] (f : M ->+ M₂)
  证明: rfl
-/
theorem AddMonoidHom.coe_toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M ->+ M₂) :
    ⇑f.toNatLinearMap = f :=
  rfl

/--
Definition of `AddMonoidHom.toIntLinearMap` / `AddMonoidHom.toIntLinearMap` 的定义

English:
definition AddMonoidHom.toIntLinearMap
  signature: [AddCommGroup M] [AddCommGroup M₂] (f : M ->+ M₂)
  body: f
  map_add' := f.map_add
  map_smul' := map_zsmul f

中文:
定义 加法幺半群态射.to整数LinearMap
  签名: [加法交换群 M] [加法交换群 M₂] (f : M ->+ M₂)
  定义体: f
  map_add' := f.map_add
  map_smul' := map_zsmul f
-/
def AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M ->+ M₂) : M ->ₗ[Int] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f

/--
theorem `AddMonoidHom.toIntLinearMap_injective` / 定理 `AddMonoidHom.toIntLinearMap_injective`

English:
theorem AddMonoidHom.toIntLinearMap_injective
  given: [AddCommGroup M] [AddCommGroup M₂]
  proof: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

中文:
定理 加法幺半群态射.to整数LinearMap_injective
  条件: [加法交换群 M] [加法交换群 M₂]
  证明: by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/--
theorem `AddMonoidHom.coe_toIntLinearMap` / 定理 `AddMonoidHom.coe_toIntLinearMap`

English:
theorem AddMonoidHom.coe_toIntLinearMap
  given: [AddCommGroup M] [AddCommGroup M₂] (f : M ->+ M₂)
  proof: rfl

中文:
定理 加法幺半群态射.coe_to整数LinearMap
  条件: [加法交换群 M] [加法交换群 M₂] (f : M ->+ M₂)
  证明: rfl
-/
theorem AddMonoidHom.coe_toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M ->+ M₂) :
    ⇑f.toIntLinearMap = f :=
  rfl

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R ->+* R₂}
variable [DistribSMul S M₂] [SMulCommClass R₂ S M₂]
variable [DistribSMul T M₂] [SMulCommClass R₂ T M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (M ->ₛₗ[σ₁₂] M₂)
  body: ⟨fun a f =>
    { toFun := a • (f : M -> M₂)
      map_add' := fun x y => by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]

中文:
实例 :
  签名: 标量乘法 S (M ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨fun a f =>
    { toFun := a • (f : M -> M₂)
      map_add' := fun x y => by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]

Depends on / 依赖: Pi.smul_apply, f.map_add, map_add, map_smul, smul_add, smul_apply, smul_comm
-/
instance : SMul S (M ->ₛₗ[σ₁₂] M₂) :=
  ⟨fun a f =>
    { toFun := a • (f : M -> M₂)
      map_add' := fun x y => by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x => by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M)
  statement: (a • f) x = a • f x
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M)
  结论: (a • f) x = a • f x
  证明: rfl

@[simp]
-/
theorem smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
  rfl

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (a : S) (f : M ->ₛₗ[σ₁₂] M₂)
  statement: (a • f : M ->ₛₗ[σ₁₂] M₂) = a • (f : M -> M₂)
  proof: rfl

中文:
定理 coe_smul
  条件: (a : S) (f : M ->ₛₗ[σ₁₂] M₂)
  结论: (a • f : M ->ₛₗ[σ₁₂] M₂) = a • (f : M -> M₂)
  证明: rfl
-/
theorem coe_smul (a : S) (f : M ->ₛₗ[σ₁₂] M₂) : (a • f : M ->ₛₗ[σ₁₂] M₂) = a • (f : M -> M₂) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T M₂] : SMulCommClass S T (M ->ₛₗ[σ₁₂] M₂)
  body: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

中文:
实例 [标量交换类
  签名: S T M₂] : 标量交换类 S T (M ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass S T M₂] : SMulCommClass S T (M ->ₛₗ[σ₁₂] M₂) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T M₂] : IsScalarTower S T (M ->ₛₗ[σ₁₂] M₂) where
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 [标量乘法
  签名: S T] [标量塔 S T M₂] : 标量塔 S T (M ->ₛₗ[σ₁₂] M₂) where
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul S T] [IsScalarTower S T M₂] : IsScalarTower S T (M ->ₛₗ[σ₁₂] M₂) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: Sᵐᵒᵖ M₂] [SMulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [分配标量乘法
  签名: Sᵐᵒᵖ M₂] [标量交换类 R₂ Sᵐᵒᵖ M₂] [中心标量 S M₂] :
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [DistribSMul Sᵐᵒᵖ M₂] [SMulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
    IsCentralScalar S (M ->ₛₗ[σ₁₂] M₂) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end SMul

/-! ### Arithmetic on the codomain -/

section Arithmetic

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommGroup N₂] [AddCommGroup N₃]
variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₂ N₂] [Module R₃ N₃]
variable {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ->ₛₗ[σ₁₂] M₂)
  body: ⟨{ toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩

中文:
实例 :
  签名: 零 (M ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨{ toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩

Depends on / 依赖: map_add, map_smul
-/
instance : Zero (M ->ₛₗ[σ₁₂] M₂) :=
  ⟨{ toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩

/--
lemma `coe_zero_iff` / 引理 `coe_zero_iff`

English:
lemma coe_zero_iff
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: ⇑f = 0 ↔ f = 0
  proof: by
  aesop

@[simp]

中文:
引理 coe_zero_iff
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: ⇑f = 0 ↔ f = 0
  证明: by
  aesop

@[simp]
-/
@[simp] lemma coe_zero_iff (f : M ->ₛₗ[σ₁₂] M₂) : ⇑f = 0 ↔ f = 0 := by
  aesop

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : M)
  statement: (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (x : M)
  结论: (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: (g : M₂ ->ₛₗ[σ₂₃] M₃)
  statement: (g.comp (0 : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
  proof: ext fun c => by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]

中文:
定理 comp_zero
  条件: (g : M₂ ->ₛₗ[σ₂₃] M₃)
  结论: (g.comp (0 : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
  证明: ext fun c => by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]

Depends on / 依赖: comp_apply, g.map_zero, map_zero, zero_apply
-/
theorem comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0 :=
  ext fun c => by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: ((0 : M₂ ->ₛₗ[σ₂₃] M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0
  proof: rfl

中文:
定理 zero_comp
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: ((0 : M₂ ->ₛₗ[σ₂₃] M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0
  证明: rfl
-/
theorem zero_comp (f : M ->ₛₗ[σ₁₂] M₂) : ((0 : M₂ ->ₛₗ[σ₂₃] M₃).comp f : M ->ₛₗ[σ₁₃] M₃) = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ->ₛₗ[σ₁₂] M₂)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (M ->ₛₗ[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
/--
theorem `default_def` / 定理 `default_def`

English:
theorem default_def
  statement: (default : M ->ₛₗ[σ₁₂] M₂) = 0
  proof: rfl

中文:
定理 default_def
  结论: (default : M ->ₛₗ[σ₁₂] M₂) = 0
  证明: rfl
-/
theorem default_def : (default : M ->ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

/--
Instance `uniqueOfLeft` / 实例 `uniqueOfLeft`

English:
instance uniqueOfLeft
  signature: [Subsingleton M]
  body: { (inferInstance : Inhabited (M ->ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }

中文:
实例 uniqueOfLeft
  签名: [子单例 M]
  定义体: { (inferInstance : Inhabited (M ->ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }

Depends on / 依赖: Inhabited, Subsingleton, Subsingleton.elim, map_zero
-/
instance uniqueOfLeft [Subsingleton M] : Unique (M ->ₛₗ[σ₁₂] M₂) :=
  { (inferInstance : Inhabited (M ->ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }

/--
Instance `uniqueOfRight` / 实例 `uniqueOfRight`

English:
instance uniqueOfRight
  signature: [Subsingleton M₂]
  body: coe_injective.unique

中文:
实例 uniqueOfRight
  签名: [子单例 M₂]
  定义体: coe_injective.unique

Depends on / 依赖: coe_injective, coe_injective.unique, unique
-/
instance uniqueOfRight [Subsingleton M₂] : Unique (M ->ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique

/--
theorem `ne_zero_of_injective` / 定理 `ne_zero_of_injective`

English:
theorem ne_zero_of_injective
  given: [Nontrivial M] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f)
  statement: f != 0
  proof: have ⟨x, ne⟩ := exists_ne (0 : M)
fun h => hf.ne ne by simp [h]

中文:
定理 ne_zero_of_injective
  条件: [非平凡 M] {f : M ->ₛₗ[σ₁₂] M₂} (hf : 单射 f)
  结论: f != 0
  证明: have ⟨x, ne⟩ := exists_ne (0 : M)
fun h => hf.ne ne by simp [h]

Depends on / 依赖: exists_ne, hf.ne
-/
theorem ne_zero_of_injective [Nontrivial M] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f) : f != 0 :=
  have ⟨x, ne⟩ := exists_ne (0 : M)
fun h => hf.ne ne by simp [h]

/--
theorem `ne_zero_of_surjective` / 定理 `ne_zero_of_surjective`

English:
theorem ne_zero_of_surjective
  given: [Nontrivial M₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Surjective f)
  statement: f != 0
  proof: by
  have ⟨y, ne⟩ := exists_ne (0 : M₂)
  obtain ⟨x, rfl⟩ := hf y
  exact fun h => ne congr($h x)

中文:
定理 ne_zero_of_surjective
  条件: [非平凡 M₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : 满射 f)
  结论: f != 0
  证明: by
  have ⟨y, ne⟩ := exists_ne (0 : M₂)
  obtain ⟨x, rfl⟩ := hf y
  exact fun h => ne congr($h x)

Depends on / 依赖: exists_ne
-/
theorem ne_zero_of_surjective [Nontrivial M₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Surjective f) : f != 0 := by
  have ⟨y, ne⟩ := exists_ne (0 : M₂)
  obtain ⟨x, rfl⟩ := hf y
  exact fun h => ne congr($h x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M ->ₛₗ[σ₁₂] M₂)
  body: ⟨fun f g =>
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]

中文:
实例 :
  签名: 加法 (M ->ₛₗ[σ₁₂] M₂)
  定义体: ⟨fun f g =>
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]

Depends on / 依赖: add_comm, add_left_comm, map_add, map_smul, smul_add
-/
instance : Add (M ->ₛₗ[σ₁₂] M₂) :=
  ⟨fun f g =>
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : M ->ₛₗ[σ₁₂] M₂) (x : M)
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
定理 add_apply
  条件: (f g : M ->ₛₗ[σ₁₂] M₂) (x : M)
  结论: (f + g) x = f x + g x
  证明: rfl
-/
theorem add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
  rfl

/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] M₃)
  proof: rfl

中文:
定理 add_comp
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] M₃)
  证明: rfl
-/
theorem add_comp (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] M₃) :
    ((h + g).comp f : M ->ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f :=
  rfl

/--
theorem `comp_add` / 定理 `comp_add`

English:
theorem comp_add
  given: (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃)
  proof: ext fun _ => h.map_add _ _

中文:
定理 comp_add
  条件: (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃)
  证明: ext fun _ => h.map_add _ _

Depends on / 依赖: h.map_add, map_add
-/
theorem comp_add (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃) :
    (h.comp (f + g) : M ->ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
  ext fun _ => h.map_add _ _

-- The `AddMonoid` instance exists to help speedup unification
/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid (M ->ₛₗ[σ₁₂] M₂)
  body: fast_instance%
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addMonoid
  签名: : 加法幺半群 (M ->ₛₗ[σ₁₂] M₂)
  定义体: fast_instance%
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance addMonoid : AddMonoid (M ->ₛₗ[σ₁₂] M₂) := fast_instance%
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (M ->ₛₗ[σ₁₂] M₂)
  body: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (M ->ₛₗ[σ₁₂] M₂)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance addCommMonoid : AddCommMonoid (M ->ₛₗ[σ₁₂] M₂) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M ->ₛₗ[σ₁₂] N₂)
  body: ⟨fun f =>
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩

中文:
实例 :
  签名: 取负 (M ->ₛₗ[σ₁₂] N₂)
  定义体: ⟨fun f =>
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩

Depends on / 依赖: add_comm, map_add, map_smul
-/
instance : Neg (M ->ₛₗ[σ₁₂] N₂) :=
  ⟨fun f =>
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : M ->ₛₗ[σ₁₂] N₂)
  statement: ⇑(-f) = -⇑f
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (f : M ->ₛₗ[σ₁₂] N₂)
  结论: ⇑(-f) = -⇑f
  证明: rfl

@[simp]
-/
@[simp] protected theorem coe_neg (f : M ->ₛₗ[σ₁₂] N₂) : ⇑(-f) = -⇑f := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : M ->ₛₗ[σ₁₂] N₂) (x : M)
  statement: (-f) x = -f x
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: (f : M ->ₛₗ[σ₁₂] N₂) (x : M)
  结论: (-f) x = -f x
  证明: rfl

@[simp]
-/
theorem neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x :=
  rfl

@[simp]
/--
theorem `neg_comp` / 定理 `neg_comp`

English:
theorem neg_comp
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] N₃)
  statement: (-g).comp f = -g.comp f
  proof: rfl

@[simp]

中文:
定理 neg_comp
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] N₃)
  结论: (-g).comp f = -g.comp f
  证明: rfl

@[simp]
-/
theorem neg_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.comp f :=
  rfl

@[simp]
/--
theorem `comp_neg` / 定理 `comp_neg`

English:
theorem comp_neg
  given: (f : M ->ₛₗ[σ₁₂] N₂) (g : N₂ ->ₛₗ[σ₂₃] N₃)
  statement: g.comp (-f) = -g.comp f
  proof: ext fun _ => g.map_neg _

中文:
定理 comp_neg
  条件: (f : M ->ₛₗ[σ₁₂] N₂) (g : N₂ ->ₛₗ[σ₂₃] N₃)
  结论: g.comp (-f) = -g.comp f
  证明: ext fun _ => g.map_neg _

Depends on / 依赖: g.map_neg, map_neg
-/
theorem comp_neg (f : M ->ₛₗ[σ₁₂] N₂) (g : N₂ ->ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.comp f :=
  ext fun _ => g.map_neg _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (M ->ₛₗ[σ₁₂] N₂)
  body: ⟨fun f g =>
    { toFun := f - g
      map_add' := fun x y => by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x => by simp [Pi.sub_apply, smul_sub] }⟩

@[simp]

中文:
实例 :
  签名: 减法 (M ->ₛₗ[σ₁₂] N₂)
  定义体: ⟨fun f g =>
    { toFun := f - g
      map_add' := fun x y => by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x => by simp [Pi.sub_apply, smul_sub] }⟩

@[simp]

Depends on / 依赖: Pi.sub_apply, add_sub_add_comm, map_add, map_smul, smul_sub, sub_apply
-/
instance : Sub (M ->ₛₗ[σ₁₂] N₂) :=
  ⟨fun f g =>
    { toFun := f - g
      map_add' := fun x y => by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x => by simp [Pi.sub_apply, smul_sub] }⟩

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : M ->ₛₗ[σ₁₂] N₂) (x : M)
  statement: (f - g) x = f x - g x
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : M ->ₛₗ[σ₁₂] N₂) (x : M)
  结论: (f - g) x = f x - g x
  证明: rfl
-/
theorem sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
  rfl

/--
theorem `sub_comp` / 定理 `sub_comp`

English:
theorem sub_comp
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] N₃)
  proof: rfl

中文:
定理 sub_comp
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] N₃)
  证明: rfl
-/
theorem sub_comp (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] N₃) :
    (g - h).comp f = g.comp f - h.comp f :=
  rfl

/--
theorem `comp_sub` / 定理 `comp_sub`

English:
theorem comp_sub
  given: (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃)
  proof: ext fun _ => h.map_sub _ _

中文:
定理 comp_sub
  条件: (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃)
  证明: ext fun _ => h.map_sub _ _

Depends on / 依赖: h.map_sub, map_sub
-/
theorem comp_sub (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃) :
    h.comp (g - f) = h.comp g - h.comp f :=
  ext fun _ => h.map_sub _ _

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (M ->ₛₗ[σ₁₂] N₂)
  body: fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 addCommGroup
  签名: : 加法交换群 (M ->ₛₗ[σ₁₂] N₂)
  定义体: fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance addCommGroup : AddCommGroup (M ->ₛₗ[σ₁₂] N₂) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `evalAddMonoidHom` / `evalAddMonoidHom` 的定义

English:
definition evalAddMonoidHom
  signature: (a : M)
  body: f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl

中文:
定义 evalAddMonoidHom
  签名: (a : M)
  定义体: f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl
-/
def evalAddMonoidHom (a : M) : (M ->ₛₗ[σ₁₂] M₂) ->+ M₂ where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl

/-- `LinearMap.toAddMonoidHom` promoted to an `AddMonoidHom`. -/
@[simps]
/--
Definition of `toAddMonoidHom'` / `toAddMonoidHom'` 的定义

English:
definition toAddMonoidHom'
  signature: : (M ->ₛₗ[σ₁₂] M₂) ->+ M ->+ M₂ where
  body: toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

中文:
定义 toAddMonoidHom'
  签名: : (M ->ₛₗ[σ₁₂] M₂) ->+ M ->+ M₂ where
  定义体: toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

Depends on / 依赖: toAddMonoidHom
-/
def toAddMonoidHom' : (M ->ₛₗ[σ₁₂] M₂) ->+ M ->+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

/-- If `M` is the zero module, then the identity map of `M` is the zero map. -/
@[simp]
/--
theorem `identityMapOfZeroModuleIsZero` / 定理 `identityMapOfZeroModuleIsZero`

English:
theorem identityMapOfZeroModuleIsZero
  given: [Subsingleton M]
  statement: id (R := R₁) (M := M) = 0
  proof: Subsingleton.eq_zero id

中文:
定理 identityMapOfZeroModuleIsZero
  条件: [子单例 M]
  结论: id (R := R₁) (M := M) = 0
  证明: Subsingleton.eq_zero id
-/
theorem identityMapOfZeroModuleIsZero [Subsingleton M] : id (R := R₁) (M := M) = 0 :=
  Subsingleton.eq_zero id

end Arithmetic

section Actions

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section SMul

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction S (M ->ₛₗ[σ₁₂] M₂)
  body: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

中文:
实例 :
  签名: 分配乘法作用 S (M ->ₛₗ[σ₁₂] M₂)
  定义体: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

Depends on / 依赖: one_smul
-/
instance : DistribMulAction S (M ->ₛₗ[σ₁₂] M₂) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: (a : S₃) (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂)
  proof: rfl

中文:
定理 smul_comp
  条件: (a : S₃) (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂)
  证明: rfl
-/
theorem smul_comp (a : S₃) (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f :=
  rfl

-- TODO: generalize this to semilinear maps
/--
theorem `comp_smul` / 定理 `comp_smul`

English:
theorem comp_smul
  statement: [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
  proof: ext fun _ => g.map_smul_of_tower _ _

中文:
定理 comp_smul
  结论: [模 R M₂] [模 R M₃] [标量交换类 R S M₂] [分配乘法作用 S M₃]
  证明: ext fun _ => g.map_smul_of_tower _ _

Depends on / 依赖: g.map_smul_of_tower, map_smul_of_tower
-/
theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ ->ₗ[R] M₂) (a : S) (f : M ->ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f :=
  ext fun _ => g.map_smul_of_tower _ _

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M₂] [SMulCommClass R₂ S M₂]

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module S (M ->ₛₗ[σ₁₂] M₂) where
  body: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

中文:
实例 module
  签名: : 模 S (M ->ₛₗ[σ₁₂] M₂) where
  定义体: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

Depends on / 依赖: add_smul
-/
instance module : Module S (M ->ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

end Module

end Actions

section RestrictScalarsAsLinearMap

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable (R S M N) in
@[simp]
/--
lemma `restrictScalars_zero` / 引理 `restrictScalars_zero`

English:
lemma restrictScalars_zero
  statement: (0 : M ->ₗ[S] N).restrictScalars R = 0
  proof: rfl

@[simp]

中文:
引理 restrictScalars_zero
  结论: (0 : M ->ₗ[S] N).restrictScalars R = 0
  证明: rfl

@[simp]
-/
lemma restrictScalars_zero : (0 : M ->ₗ[S] N).restrictScalars R = 0 :=
  rfl

@[simp]
/--
theorem `restrictScalars_add` / 定理 `restrictScalars_add`

English:
theorem restrictScalars_add
  given: (f g : M ->ₗ[S] N)
  proof: rfl

@[simp]

中文:
定理 restrictScalars_add
  条件: (f g : M ->ₗ[S] N)
  证明: rfl

@[simp]
-/
theorem restrictScalars_add (f g : M ->ₗ[S] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl

@[simp]
/--
theorem `restrictScalars_neg` / 定理 `restrictScalars_neg`

English:
theorem restrictScalars_neg
  statement: {M N : Type*} [AddCommMonoid M] [AddCommGroup N]
  proof: rfl

中文:
定理 restrictScalars_neg
  结论: {M N : 类型} [加法交换幺半群 M] [加法交换群 N]
  证明: rfl
-/
theorem restrictScalars_neg {M N : Type*} [AddCommMonoid M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]
    (f : M ->ₗ[S] N) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

@[simp]
/--
theorem `restrictScalars_smul` / 定理 `restrictScalars_smul`

English:
theorem restrictScalars_smul
  given: (c : R₁) (f : M ->ₗ[S] N)
  proof: rfl

@[simp]

中文:
定理 restrictScalars_smul
  条件: (c : R₁) (f : M ->ₗ[S] N)
  证明: rfl

@[simp]
-/
theorem restrictScalars_smul (c : R₁) (f : M ->ₗ[S] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

@[simp]
/--
lemma `restrictScalars_comp` / 引理 `restrictScalars_comp`

English:
lemma restrictScalars_comp
  statement: [AddCommMonoid P] [Module S P] [Module R P]
  proof: rfl

@[simp]

中文:
引理 restrictScalars_comp
  结论: [加法交换幺半群 P] [模 S P] [模 R P]
  证明: rfl

@[simp]
-/
lemma restrictScalars_comp [AddCommMonoid P] [Module S P] [Module R P]
    [CompatibleSMul N P R S] [CompatibleSMul M P R S] (f : N ->ₗ[S] P) (g : M ->ₗ[S] N) :
    (f ∘ₗ g).restrictScalars R = f.restrictScalars R ∘ₗ g.restrictScalars R :=
  rfl

@[simp]
/--
lemma `restrictScalars_trans` / 引理 `restrictScalars_trans`

English:
lemma restrictScalars_trans
  statement: {T : Type*} [Semiring T] [Module T M] [Module T N]
  proof: rfl

中文:
引理 restrictScalars_trans
  结论: {T : 类型} [半环 T] [模 T M] [模 T N]
  证明: rfl
-/
lemma restrictScalars_trans {T : Type*} [Semiring T] [Module T M] [Module T N]
    [CompatibleSMul M N S T] [CompatibleSMul M N R T] (f : M ->ₗ[T] N) :
    (f.restrictScalars S).restrictScalars R = f.restrictScalars R :=
  rfl

variable (S M N R R₁)

/-- `LinearMap.restrictScalars` as a `LinearMap`. -/
@[simps apply]
/--
Definition of `restrictScalarsₗ` / `restrictScalarsₗ` 的定义

English:
definition restrictScalarsₗ
  signature: : (M ->ₗ[S] N) ->ₗ[R₁] M ->ₗ[R] N where
  body: restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

中文:
定义 restrictScalarsₗ
  签名: : (M ->ₗ[S] N) ->ₗ[R₁] M ->ₗ[R] N where
  定义体: restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

Depends on / 依赖: restrictScalars
-/
def restrictScalarsₗ : (M ->ₗ[S] N) ->ₗ[R₁] M ->ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

end RestrictScalarsAsLinearMap

section mulLeftRight
variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (R) [SMulCommClass R A A]

/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (a : A)
  body: AddMonoidHom.mulLeft a
  map_smul' _ := mul_smul_comm _ _

@[simp]

中文:
定义 mulLeft
  签名: (a : A)
  定义体: AddMonoidHom.mulLeft a
  map_smul' _ := mul_smul_comm _ _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, mulLeft
-/
def mulLeft (a : A) : A ->ₗ[R] A where
  __ := AddMonoidHom.mulLeft a
  map_smul' _ := mul_smul_comm _ _

@[simp]
/--
theorem `mulLeft_apply` / 定理 `mulLeft_apply`

English:
theorem mulLeft_apply
  given: (a b : A)
  statement: mulLeft R a b = a * b
  proof: rfl

@[simp]

中文:
定理 mulLeft_apply
  条件: (a b : A)
  结论: mulLeft R a b = a * b
  证明: rfl

@[simp]
-/
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := rfl

@[simp]
/--
theorem `toAddMonoidHom_mulLeft` / 定理 `toAddMonoidHom_mulLeft`

English:
theorem toAddMonoidHom_mulLeft
  given: (a : A)
  statement: (mulLeft R a : A ->+ A) = AddMonoidHom.mulLeft a
  proof: rfl

中文:
定理 toAddMonoidHom_mulLeft
  条件: (a : A)
  结论: (mulLeft R a : A ->+ A) = 加法幺半群态射.mulLeft a
  证明: rfl
-/
theorem toAddMonoidHom_mulLeft (a : A) : (mulLeft R a : A ->+ A) = AddMonoidHom.mulLeft a := rfl

variable (A) in
@[simp]
/--
theorem `mulLeft_zero_eq_zero` / 定理 `mulLeft_zero_eq_zero`

English:
theorem mulLeft_zero_eq_zero
  statement: mulLeft R (0 : A) = 0
  proof: ext zero_mul

中文:
定理 mulLeft_zero_eq_zero
  结论: mulLeft R (0 : A) = 0
  证明: ext zero_mul

Depends on / 依赖: zero_mul
-/
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := ext zero_mul

end left

section right
variable (R) [IsScalarTower R A A]

/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (b : A)
  body: AddMonoidHom.mulRight b
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]

中文:
定义 mulRight
  签名: (b : A)
  定义体: AddMonoidHom.mulRight b
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, mulRight
-/
def mulRight (b : A) : A ->ₗ[R] A where
  __ := AddMonoidHom.mulRight b
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]
/--
theorem `mulRight_apply` / 定理 `mulRight_apply`

English:
theorem mulRight_apply
  given: (a b : A)
  statement: mulRight R a b = b * a
  proof: rfl

@[simp]

中文:
定理 mulRight_apply
  条件: (a b : A)
  结论: mulRight R a b = b * a
  证明: rfl

@[simp]
-/
theorem mulRight_apply (a b : A) : mulRight R a b = b * a := rfl

@[simp]
/--
theorem `toAddMonoidHom_mulRight` / 定理 `toAddMonoidHom_mulRight`

English:
theorem toAddMonoidHom_mulRight
  given: (a : A)
  statement: (mulRight R a : A ->+ A) = AddMonoidHom.mulRight a
  proof: rfl

中文:
定理 toAddMonoidHom_mulRight
  条件: (a : A)
  结论: (mulRight R a : A ->+ A) = 加法幺半群态射.mulRight a
  证明: rfl
-/
theorem toAddMonoidHom_mulRight (a : A) : (mulRight R a : A ->+ A) = AddMonoidHom.mulRight a := rfl

variable (A) in
@[simp]
/--
theorem `mulRight_zero_eq_zero` / 定理 `mulRight_zero_eq_zero`

English:
theorem mulRight_zero_eq_zero
  statement: mulRight R (0 : A) = 0
  proof: ext mul_zero

中文:
定理 mulRight_zero_eq_zero
  结论: mulRight R (0 : A) = 0
  证明: ext mul_zero

Depends on / 依赖: mul_zero
-/
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := ext mul_zero

end right

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable (R) in
/--
Definition of `mulLeftRight` / `mulLeftRight` 的定义

English:
definition mulLeftRight
  signature: (ab : A × A)
  body: (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]

中文:
定义 mulLeftRight
  签名: (ab : A × A)
  定义体: (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]

Depends on / 依赖: ab.fst, ab.snd, mulLeft, mulRight
-/
def mulLeftRight (ab : A × A) : A ->ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]
/--
theorem `mulLeftRight_apply` / 定理 `mulLeftRight_apply`

English:
theorem mulLeftRight_apply
  given: (a b x : A)
  statement: mulLeftRight R (a, b) x = a * x * b
  proof: rfl

中文:
定理 mulLeftRight_apply
  条件: (a b x : A)
  结论: mulLeftRight R (a, b) x = a * x * b
  证明: rfl
-/
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

end mulLeftRight

end LinearMap
