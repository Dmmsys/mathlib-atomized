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

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `IsLinearMap R f` asserts this
property. A bundled version is available with `LinearMap`, and should be favored over
`IsLinearMap` most of the time. -/
/-
**IsLinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   {M : Type v} →     {M₂ : Type w} →       [inst : Semiring
 R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddCommMonoid M₂]
 → [_root_.Module R M] → [_root_.Module R M₂] → (M → M₂) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` between modules over a semiring is linear if it satisfies the two prop
erties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. The predicate `IsLinearMap R 
f` asserts this
property. A bundled version is available with `LinearMap`, and should be favored
 over
`IsLinearMap` most of the time.
-/
structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) : Prop where
  /-- A linear map preserves addition. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- A linear map preserves scalar multiplication. -/
  map_smul : ∀ (c : R) (x), f (c • x) = c • f x

section

/-- A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided most of the time. -/
/-
**LinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         (R →+* S) →           (M : Type u_16) →             
(M₂ : Type u_17) →               [inst_2 : AddCommMonoid M] →                 [i
nst_3 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S M₂] → Type (m
ax u_16 u_17)
参数：R →+* S；M : Type u_16；M₂ : Type u_17；max u_16 u_17。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : 
R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the n
otation
`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. fo
r which
`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled versio
n of plain linear
maps is available with the predicate `IsLinearMap`, but it should be avoided mos
t of the time.
-/
structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

/-- The `MulActionHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toMulActionHom

/-- The `AddHom` underlying a `LinearMap`. -/
add_decl_doc LinearMap.toAddHom

/-- `M →ₛₗ[σ] N` is the type of `σ`-semilinear maps from `M` to `N`. -/
notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

/-- `M →ₗ[R] N` is the type of `R`-linear maps from `M` to `N`. -/
notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

/-- `SemilinearMapClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear maps `M → M₂`.

See also `LinearMapClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
/-
**SemilinearMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_14) →   {R : outParam (Type u_15)} →     {S : outParam (Type u
_16)} →       [inst : Semiring R] →         [inst_1 : Semiring S] →           ou
tParam (R →+* S) →             (M : outParam (Type u_17)) →               (M₂ : 
outParam (Type u_18)) →                 [inst_2 : AddCommMonoid M] →            
       [inst_3 : AddCommMonoid M₂] → [_root_.Module R M] → [_root_.Module S M₂] 
→ [FunLike F M M₂] → Prop
参数：Type u_17；Type u_18。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemilinearMapClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear ma
ps `M → M₂`.

See also `LinearMapClass F R M M₂` for the case where `σ` is the identity map on
 `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : 
R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`.
-/
class SemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam (R →+* S)) (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module S M₂] [FunLike F M M₂] : Prop
    extends AddHomClass F M M₂, MulActionSemiHomClass F σ M M₂

end

-- `map_smulₛₗ` should be `@[simp]` but doesn't fire due to https://github.com/leanprover/lean4/pull/3701.
-- attribute [simp] map_smulₛₗ

/-- `LinearMapClass F R M M₂` asserts `F` is a type of bundled `R`-linear maps `M → M₂`.

This is an abbreviation for `SemilinearMapClass F (RingHom.id R) M M₂`.
-/
/-
**LinearMapClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearMapClass (F : Type*) (R : outParam Type*) (M M₂ : Type*) [Semiring R
] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M
₂]
参数：F : Type*；R : outParam Type*；M M₂ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMapClass F R M M₂` asserts `F` is a type of bundled `R`-linear maps `M → 
M₂`.

This is an abbreviation for `SemilinearMapClass F (RingHom.id R) M M₂`.
-/
abbrev LinearMapClass (F : Type*) (R : outParam Type*) (M M₂ : Type*)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [FunLike F M M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂
/-
**LinearMapClass.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMapClass`。
形式化陈述：∀ {R : outParam (Type u_14)} {M : outParam (Type u_15)} {M₂ : outParam (Ty
pe u_16)} [inst : Semiring R]   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMono
id M₂] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R M₂]   {F : Type u_
17} [inst_5 : FunLike F M M₂] [LinearMapClass F R M M₂] (f : F) (r : R) (x : M),
 f (r • x) = r • f x
参数：Type u_14；Type u_15；Type u_16；f : F；r : R；x : M；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
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
variable {σ : R →+* S}

/-
**SemilinearMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instAddMonoidHomClass [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    AddMonoidHomClass F M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_zero := fun f ↦
      show f 0 = 0 by
        rw [← zero_smul R (0 : M), map_smulₛₗ]
        simp }
/-
**SemilinearMapClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearMapClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) distribMulActionSemiHomClass
    [FunLike F M M₃] [SemilinearMapClass F σ M M₃] :
    DistribMulActionSemiHomClass F σ M M₃ :=
  { SemilinearMapClass.toAddHomClass with
    map_smulₛₗ := fun f c x ↦ by rw [map_smulₛₗ] }

variable {F} (f : F) [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
/-
**SemilinearMapClass.map_smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearMapClass`
。
形式化陈述：map_smul_inv {σ' : S ->+* R} [RingHomInvPair σ σ'] (c : S) (x : M) : c • f
 x = f (σ' c • x)
参数：c : S；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp [map_smulₛₗ _]

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
@[coe]
/-
**SemilinearMapClass.semilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `SemilinearMapClass
`。
形式化陈述：semilinearMap : M ->ₛₗ[σ] M₃ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of semilinear maps as a semilinear map.
-/
def semilinearMap : M →ₛₗ[σ] M₃ where
  toFun := f
  map_add' := map_add f
  map_smul' := map_smulₛₗ f

/-- Reinterpret an element of a type of semilinear maps as a semilinear map. -/
/-
**SemilinearMapClass.instCoeToSemilinearMap** 是 Mathlib 中的一个实例，位于命名空间 `Semilinea
rMapClass`。
形式化陈述：instCoeToSemilinearMap : CoeHead F (M ->ₛₗ[σ] M₃) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of semilinear maps as a semilinear map.
-/
instance instCoeToSemilinearMap : CoeHead F (M →ₛₗ[σ] M₃) where
  coe f := semilinearMap f

end SemilinearMapClass

namespace LinearMapClass
variable {F : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  (f : F) [FunLike F M₁ M₂] [LinearMapClass F R M₁ M₂]

/-- Reinterpret an element of a type of linear maps as a linear map. -/
/-
**LinearMapClass.linearMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMapClass`。
形式化陈述：linearMap : M₁ ->ₗ[R] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of linear maps as a linear map.
-/
abbrev linearMap : M₁ →ₗ[R] M₂ := SemilinearMapClass.semilinearMap f

/-- Reinterpret an element of a type of linear maps as a linear map. -/
/-
**LinearMapClass.instCoeToLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `LinearMapClass`。
形式化陈述：instCoeToLinearMap : CoeHead F (M₁ ->ₗ[R] M₂) where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of linear maps as a linear map.
-/
instance instCoeToLinearMap : CoeHead F (M₁ →ₗ[R] M₂) where
  coe f := SemilinearMapClass.semilinearMap f

end LinearMapClass

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable {σ : R →+* S}

/-
**LinearMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：instFunLike : FunLike (M ->ₛₗ[σ] M₃) M M₃ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (M →ₛₗ[σ] M₃) M M₃ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h
/-
**LinearMap.semilinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：semilinearMapClass : SemilinearMapClass (M ->ₛₗ[σ] M₃) σ M M₃ where map_ad
d f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
-/
instance semilinearMapClass : SemilinearMapClass (M →ₛₗ[σ] M₃) σ M M₃ where
  map_add f := f.map_add'
  map_smulₛₗ := LinearMap.map_smul'

@[simp, norm_cast]
/-
**LinearMap.coe_coe** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] {f : F}
 : ⇑(f : M ->ₛₗ[σ] M₃) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] {f : F} :
    ⇑(f : M →ₛₗ[σ] M₃) = f :=
  rfl

/-- The `DistribMulActionHom` underlying a `LinearMap`. -/
/-
**LinearMap.toDistribMulActionHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toDistribMulActionHom (f : M ->ₛₗ[σ] M₃) : DistribMulActionHom σ.toMonoidH
om M M₃
参数：f : M ->ₛₗ[σ] M₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…

--- 原说明 ---
The `DistribMulActionHom` underlying a `LinearMap`.
-/
def toDistribMulActionHom (f : M →ₛₗ[σ] M₃) : DistribMulActionHom σ.toMonoidHom M M₃ :=
  { f with map_zero' := show f 0 = 0 from map_zero f }

@[simp]
/-
**LinearMap.coe_toAddHom** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_toAddHom (f : M ->ₛₗ[σ] M₃) : ⇑f.toAddHom = f
参数：f : M ->ₛₗ[σ] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddHom (f : M →ₛₗ[σ] M₃) : ⇑f.toAddHom = f := rfl

@[simp]
/-
**LinearMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toFun_eq_coe {f : M ->ₛₗ[σ] M₃} : f.toFun = (f : M -> M₃)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : M →ₛₗ[σ] M₃} : f.toFun = (f : M → M₃) := rfl

@[ext]
/-
**LinearMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : M →ₛₗ[σ] M₃} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `LinearMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**LinearMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {S : Type u_5} →     {M : Type u_8} →       {M₃ : Type 
u_11} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₃] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule S M₃] →                     {σ : R →+* S} → (f : M →ₛₗ[σ] M₃) → (f' : M → 
M₃) → f' = ⇑f → M →ₛₗ[σ] M₃
参数：f : M →ₛₗ[σ] M₃；f' : M → M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `LinearMap` with a new `toFun` equal to the old one. Useful to fix def
initional
equalities.
-/
protected def copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : M →ₛₗ[σ] M₃ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'

@[simp]
/-
**LinearMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_copy (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f) : ⇑(f.copy f' h) 
= f'
参数：f : M ->ₛₗ[σ] M₃；f' : M -> M₃；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**LinearMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：copy_eq (f : M ->ₛₗ[σ] M₃) (f' : M -> M₃) (h : f' = ⇑f) : f.copy f' h = f
参数：f : M ->ₛₗ[σ] M₃；f' : M -> M₃；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : M →ₛₗ[σ] M₃) (f' : M → M₃) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

initialize_simps_projections LinearMap (toFun → apply)

@[simp]
/-
**LinearMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_mk {σ : R ->+* S} (f : AddHom M M₃) (h) : ((LinearMap.mk f h : M ->ₛₗ[
σ] M₃) : M -> M₃) = f
参数：f : AddHom M M₃；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl

@[simp]
/-
**LinearMap.coe_addHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_addHom_mk {σ : R ->+* S} (f : AddHom M M₃) (h) : ((LinearMap.mk f h : 
M ->ₛₗ[σ] M₃) : AddHom M M₃) = f
参数：f : AddHom M M₃；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem coe_addHom_mk {σ : R →+* S} (f : AddHom M M₃) (h) :
    ((LinearMap.mk f h : M →ₛₗ[σ] M₃) : AddHom M M₃) = f :=
  rfl
/-
**LinearMap.coe_semilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_semilinearMap {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M
₃] (f : F) : ((f : M ->ₛₗ[σ] M₃) : M -> M₃) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_semilinearMap {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃] (f : F) :
    ((f : M →ₛₗ[σ] M₃) : M → M₃) = f :=
  rfl
/-
**LinearMap.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toLinearMap_injective {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ
 M M₃] {f g : F} (h : (f : M ->ₛₗ[σ] M₃) = (g : M ->ₛₗ[σ] M₃)) : f = g
参数：h : (f : M ->ₛₗ[σ] M₃) = (g : M ->ₛₗ[σ] M₃)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toLinearMap_injective {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
    {f g : F} (h : (f : M →ₛₗ[σ] M₃) = (g : M →ₛₗ[σ] M₃)) :
    f = g := by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

/-- Identity map as a `LinearMap` -/
@[instance_reducible]
/-
**LinearMap.id** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：id : M ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as a `LinearMap`
-/
def id : M →ₗ[R] M :=
  { DistribMulActionHom.id R with toFun x := x }
/-
**LinearMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_apply (x : M) : @id R M _ _ _ x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : M) : @id R M _ _ _ x = x :=
  rfl

@[simp, norm_cast]
/-
**LinearMap.id_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_coe : ((LinearMap.id : M →ₗ[R] M) : M → M) = _root_.id :=
  rfl

/-- A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the identity. -/
@[simps]
/-
**LinearMap.id'** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：id' {σ : R ->+* R} [RingHomId σ] : M ->ₛₗ[σ] M where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalisation of `LinearMap.id` that constructs the identity function
as a `σ`-semilinear map for any ring homomorphism `σ` which we know is the ident
ity.
-/
def id' {σ : R →+* R} [RingHomId σ] : M →ₛₗ[σ] M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    have := (RingHomId.eq_id : σ = _)
    subst this
    rfl

@[simp, norm_cast]
/-
**LinearMap.id'_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {σ : R →+* R} [inst_3 : RingHomId σ], ⇑Linea
rMap.id' = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id'_coe {σ : R →+* R} [RingHomId σ] : ((id' : M →ₛₗ[σ] M) : M → M) = _root_.id :=
  rfl

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module S M₃]
variable (σ : R →+* S)
variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

/-
**LinearMap.isLinear** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isLinear : IsLinearMap R fₗ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
-/
theorem isLinear : IsLinearMap R fₗ :=
  ⟨fₗ.map_add', fₗ.map_smul'⟩

variable {fₗ f g σ}
/-
**LinearMap.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_injective : Injective (DFunLike.coe : (M ->ₛₗ[σ] M₃) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : Injective (DFunLike.coe : (M →ₛₗ[σ] M₃) → _) :=
  DFunLike.coe_injective
/-
**LinearMap.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} {f : M →ₛₗ[σ] M₃} {x x' : M}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

/-- If two linear maps are equal, they are equal at each point. -/
/-
**LinearMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} {f g : M →ₛₗ[σ] M₃}, f = g → ∀ (x : M), f x = g x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If two linear maps are equal, they are equal at each point.
-/
protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x
/-
**LinearMap.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃) (h : ∀ (m : R) (x : M), (↑f).toFun (m • x) = σ m • (↑f).to
Fun x),   { toAddHom := ↑f, map_smul' := h } = f
参数：f : M →ₛₗ[σ] M₃；h : ∀ (m : R) (x : M), (↑f).toFun (m • x) = σ m • (↑f).toFun 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
@[simp] lemma mk_coe (f : M →ₛₗ[σ] M₃) (h) : (mk f h : M →ₛₗ[σ] M₃) = f := rfl
/-
**LinearMap.mk_coe'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃) (h : ∀ (m : R) (x : M), f.toFun (m • x) = σ m • f.toFun x)
,   { toAddHom := f.toAddHom, map_smul' := h } = f
参数：f : M →ₛₗ[σ] M₃；h : ∀ (m : R) (x : M), f.toFun (m • x) = σ m • f.toFun x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_coe' (f : M →ₛₗ[σ] M₃) (h) : (mk f.toAddHom h : M →ₛₗ[σ] M₃) = f := rfl

variable (fₗ f g)
/-
**LinearMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃) (x y : M), f (x + y) = f x + f y
参数：f : M →ₛₗ[σ] M₃；x y : M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
protected theorem map_add (x y : M) : f (x + y) = f x + f y :=
  map_add f x y
/-
**LinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃), f 0 = 0
参数：f : M →ₛₗ[σ] M₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

-- Porting note: `simp` wasn't picking up `map_smulₛₗ` for `LinearMap`s without specifying
-- `map_smulₛₗ f`, so we marked this as `@[simp]` in Mathlib3.
-- For Mathlib4, let's try without the `@[simp]` attribute and hope it won't need to be re-enabled.
-- This has to be re-tagged as `@[simp]` in https://github.com/leanprover-community/mathlib4/pull/8386 (see also https://github.com/leanprover/lean4/issues/3107).
@[simp]
/-
**LinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst
_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R M₂] (fₗ : M →ₗ[R] M₂) (c : R)   (x : M), fₗ (c • x) =
 c • fₗ x
参数：fₗ : M →ₗ[R] M₂；c : R；x : M；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
protected theorem map_smulₛₗ (c : R) (x : M) : f (c • x) = σ c • f x :=
  map_smulₛₗ f c x
/-
**LinearMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst
_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R M₂] (fₗ : M →ₗ[R] M₂) (c : R)   (x : M), fₗ (c • x) =
 c • fₗ x
参数：fₗ : M →ₗ[R] M₂；c : R；x : M；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
protected theorem map_smul (c : R) (x : M) : fₗ (c • x) = c • fₗ x :=
  map_smul fₗ c x
/-
**LinearMap.map_smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃) {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M), c • 
f x = f (σ' c • x)
参数：f : M →ₛₗ[σ] M₃；c : S；x : M；σ' c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp

@[simp]
/-
**LinearMap.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : Type u_11} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid M₃] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S M₃]   {σ : R →+*
 S} (f : M →ₛₗ[σ] M₃), Function.Injective ⇑f → ∀ {x : M}, f x = 0 ↔ x = 0
参数：f : M →ₛₗ[σ] M₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_eq_zero_iff (h : Function.Injective f) {x : M} : f x = 0 ↔ x = 0 :=
  _root_.map_eq_zero_iff f h

variable (M M₂)

/-- A typeclass for `SMul` structures which can be moved through a `LinearMap`.
This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be moved even if
`S` does not support negation.
-/
/-
**LinearMap.CompatibleSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：(M : Type u_8) →   (M₂ : Type u_10) →     [inst : AddCommMonoid M] →      
 [inst_1 : AddCommMonoid M₂] →         (R : Type u_14) →           (S : Type u_1
5) →             [inst_2 : Semiring S] → [SMul R M] → [_root_.Module S M] → [SMu
l R M₂] → [_root_.Module S M₂] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for `SMul` structures which can be moved through a `LinearMap`.
This typeclass is generated automatically from an `IsScalarTower` instance, but 
exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be
 moved even if
`S` does not support negation.
-/
class CompatibleSMul (R S : Type*) [Semiring S] [SMul R M] [Module S M] [SMul R M₂]
  [Module S M₂] : Prop where
  /-- Scalar multiplication by `R` of `M` can be moved through linear maps. -/
  map_smul : ∀ (fₗ : M →ₗ[S] M₂) (c : R) (x : M), fₗ (c • x) = c • fₗ x

variable {M M₂}

section

variable {R S : Type*} [Semiring S] [SMul R M] [Module S M] [SMul R M₂] [Module S M₂]

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsScalarTower.compatibleSMul [SMul R S]
    [IsScalarTower R S M] [IsScalarTower R S M₂] :
    CompatibleSMul M M₂ R S :=
  ⟨fun fₗ c x ↦ by rw [← smul_one_smul S c x, ← smul_one_smul S c (fₗ x), map_smul]⟩
/-
**LinearMap.IsScalarTower.compatibleSMul'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sScalarTower`。
形式化陈述：∀ {M : Type u_8} [inst : AddCommMonoid M] {R : Type u_14} {S : Type u_15} 
[inst_1 : Semiring S] [inst_2 : SMul R M]   [inst_3 : _root_.Module S M] [inst_4
 : SMul R S] [IsScalarTower R S M], LinearMap.CompatibleSMul S M R S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `IsScalarTower.smulHomClass`：∀ (M' : Type u_1) (X : Type u_5) [inst : SMu
l M' X] (Y : Type u_6) [inst_1 : SMul M' Y] (F : Type u_8)   [inst_2 : FunLike F
 X Y] [inst_3 : …
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
instance IsScalarTower.compatibleSMul' [SMul R S] [IsScalarTower R S M] :
    CompatibleSMul S M R S where
  map_smul := (IsScalarTower.smulHomClass R S M (S →ₗ[S] M)).map_smulₛₗ

@[simp]
/-
**LinearMap.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_smul_of_tower [CompatibleSMul M M₂ R S] (fₗ : M ->ₗ[S] M₂) (c : R) (x 
: M) : fₗ (c • x) = c • fₗ x
参数：fₗ : M ->ₗ[S] M₂；c : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.map_smul`：∀ {M : Type u_8} {M₂ : Type u_10} {in
st : AddCommMonoid M} {inst_1 : AddCommMonoid M₂} {R : Type u_14} {S : Type u_15
}   {inst_2 : Semiring …
-/
theorem map_smul_of_tower [CompatibleSMul M M₂ R S] (fₗ : M →ₗ[S] M₂) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  CompatibleSMul.map_smul fₗ c x
/-
**LinearMap._root_.LinearMapClass.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMapClass.map_smul_of_tower {F : Type*} [CompatibleSMul M M₂ R S]
    [FunLike F M M₂] [LinearMapClass F S M M₂] (fₗ : F) (c : R) (x : M) :
    fₗ (c • x) = c • fₗ x :=
  LinearMap.CompatibleSMul.map_smul (fₗ : M →ₗ[S] M₂) c x

variable (R R) in
/-
**LinearMap.isScalarTower_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isScalarTower_of_injective [SMul R S] [CompatibleSMul M M₂ R S] [IsScalarT
ower R S M₂] (f : M ->ₗ[S] M₂) (hf : Function.Injective f) : IsScalarTower R S M
 where smul_assoc r s _
参数：f : M ->ₗ[S] M₂；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
theorem isScalarTower_of_injective [SMul R S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂]
    (f : M →ₗ[S] M₂) (hf : Function.Injective f) : IsScalarTower R S M where
  smul_assoc r s _ := hf <| by rw [f.map_smul_of_tower r, map_smul, map_smul, smul_assoc]
/-
**LinearMap._root_.map_zsmul_unit** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.map_zsmul_unit {F M N : Type*}
    [AddGroup M] [AddGroup N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (c : ℤˣ) (m : M) :
    f (c • m) = c • f m := by
  simp [Units.smul_def]

end

variable (R) in
/-
**LinearMap.isLinearMap_of_compatibleSMul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isLinearMap_of_compatibleSMul [Module S M] [Module S M₂] [CompatibleSMul M
 M₂ R S] (f : M ->ₗ[S] M₂) : IsLinearMap R f where map_add
参数：f : M ->ₗ[S] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem isLinearMap_of_compatibleSMul [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]
    (f : M →ₗ[S] M₂) : IsLinearMap R f where
  map_add := map_add f
  map_smul := map_smul_of_tower f

/-- Convert a linear map to an additive monoid hom. -/
-- See note [implicit instance arguments]
/-
**LinearMap.toAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+* S} 
(f : M₁ ->ₛₗ[σ] M₂) : M₁ ->+ M₂ where toFun
参数：f : M₁ ->ₛₗ[σ] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
def toAddMonoidHom {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S} (f : M₁ →ₛₗ[σ] M₂) :
    M₁ →+ M₂ where
  toFun := f
  map_zero' := f.map_zero
  map_add' := f.map_add

omit [Module R M₂] in
@[simp]
/-
**LinearMap.toAddMonoidHom_coe** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom_coe {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R ->+*
 S} (f : M₁ ->ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f
参数：f : M₁ ->ₛₗ[σ] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddMonoidHom_coe {modM₁ : Module R M₁} {modM₂ : Module S M₂} {σ : R →+* S}
    (f : M₁ →ₛₗ[σ] M₂) : ⇑f.toAddMonoidHom = f := rfl

section RestrictScalars

variable (R)
variable [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `LinearMap.map_smul_of_tower`. -/
/-
**LinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   {S : Type u_5} →     {M : Type u_8} →       {M₂ : Type 
u_10} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₂] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule R M₂] →                     [inst_6 : _root_.Module S M] →                
       [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M 
→ₗ[S] M₂) → M →ₗ[R] M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), th
en any `S`-linear
map from `M` to `M₂` is `R`-linear.

See also `LinearMap.map_smul_of_tower`.
-/
@[coe] def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where
  toFun := fₗ
  map_add' := fₗ.map_add
  map_smul' := fₗ.map_smul_of_tower
/-
**LinearMap.coeIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：coeIsScalarTower : CoeHTCT (M ->ₗ[S] M₂) (M ->ₗ[R] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeIsScalarTower : CoeHTCT (M →ₗ[S] M₂) (M →ₗ[R] M₂) :=
  ⟨restrictScalars R⟩

@[simp, norm_cast]
/-
**LinearMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_restrictScalars (f : M ->ₗ[S] M₂) : ((f : M ->ₗ[R] M₂) : M -> M₂) = f
参数：f : M ->ₗ[S] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : M →ₗ[S] M₂) : ((f : M →ₗ[R] M₂) : M → M₂) = f :=
  rfl

@[simp]
/-
**LinearMap.restrictScalars_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_self (f : M ->ₗ[R] M₂) : f.restrictScalars R = f
参数：f : M ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
lemma restrictScalars_self (f : M →ₗ[R] M₂) : f.restrictScalars R = f := rfl
/-
**LinearMap.restrictScalars_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_apply (fₗ : M ->ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ
 x
参数：fₗ : M ->ₗ[S] M₂；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_apply (fₗ : M →ₗ[S] M₂) (x) : restrictScalars R fₗ x = fₗ x :=
  rfl
/-
**LinearMap.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (M ->ₗ
[S] M₂) -> M ->ₗ[R] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M →ₗ[S] M₂) → M →ₗ[R] M₂) := fun _ _ h ↦
  ext (LinearMap.congr_fun h :)

@[simp]
/-
**LinearMap.restrictScalars_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_inj (fₗ gₗ : M ->ₗ[S] M₂) : fₗ.restrictScalars R = gₗ.rest
rictScalars R ↔ fₗ = gₗ
参数：fₗ gₗ : M ->ₗ[S] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
-/
theorem restrictScalars_inj (fₗ gₗ : M →ₗ[S] M₂) :
    fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ :=
  (restrictScalars_injective R).eq_iff

@[simp]
/-
**LinearMap.restrictScalars_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_id [CompatibleSMul M M R S] : (id (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_id [CompatibleSMul M M R S] :
    (id (R := S) (M := M)).restrictScalars R = id := rfl

end RestrictScalars

/-
**LinearMap.toAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom_injective : Function.Injective (toAddMonoidHom : (M ->ₛₗ[σ]
 M₃) -> M ->+ M₃)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toAddMonoidHom_injective :
    Function.Injective (toAddMonoidHom : (M →ₛₗ[σ] M₃) → M →+ M₃) := fun fₗ gₗ h ↦
  ext <| (DFunLike.congr_fun h : ∀ x, fₗ.toAddMonoidHom x = gₗ.toAddMonoidHom x)

/-- If two `σ`-linear maps from `R` are equal on `1`, then they are equal. -/
@[ext high]
/-
**LinearMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g
参数：h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…

--- 原说明 ---
If two `σ`-linear maps from `R` are equal on `1`, then they are equal.
-/
theorem ext_ring {f g : R →ₛₗ[σ] M₃} (h : f 1 = g 1) : f = g :=
  ext fun x ↦ by rw [← mul_one x, ← smul_eq_mul, f.map_smulₛₗ, g.map_smulₛₗ, h]

end

/-- Interpret a `RingHom` `f` as an `f`-semilinear map. -/
@[simps]
/-
**LinearMap._root_.RingHom.toSemilinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `RingHom` `f` as an `f`-semilinear map.
-/
def _root_.RingHom.toSemilinearMap (f : R →+* S) : R →ₛₗ[f] S :=
  { f with
    map_smul' := f.map_mul }
/-
**LinearMap._root_.RingHom.coe_toSemilinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.RingHom.coe_toSemilinearMap (f : R →+* S) : ⇑f.toSemilinearMap = f := rfl

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

/-- Composition of two linear maps is a linear map -/
@[instance_reducible]
/-
**LinearMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁
₂] M₂) : M₁ ->ₛₗ[σ₁₃] M₃ where toFun x
参数：f : M₂ ->ₛₗ[σ₂₃] M₃；g : M₁ ->ₛₗ[σ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two linear maps is a linear map
-/
def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
    M₁ →ₛₗ[σ₁₃] M₃ where
  toFun x := f (g x)
  map_add' := by simp only [map_add, forall_const]
  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`
  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

/-- `∘ₗ` is notation for composition of two linear (not semilinear!) maps into a linear map.
This is useful when Lean is struggling to infer the `RingHomCompTriple` instance. -/
notation3:80 (name := compNotation) f:81 " ∘ₗ " g:80 =>
  LinearMap.comp (σ₁₂ := RingHom.id _) (σ₂₃ := RingHom.id _) (σ₁₃ := RingHom.id _) f g

@[inherit_doc] infixr:90 " ∘ₛₗ " => comp

/-
**LinearMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_apply (x : M₁) : f.comp g x = f (g x)
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (x : M₁) : f.comp g x = f (g x) :=
  rfl

@[simp, norm_cast]
/-
**LinearMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp : (f.comp g : M₁ → M₃) = f ∘ g :=
  rfl

@[simp]
/-
**LinearMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_id : f.comp id = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id : f.comp id = f :=
  rfl

@[simp]
/-
**LinearMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_comp : id.comp f = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp : id.comp f = f :=
  rfl
/-
**LinearMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
 {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄} [RingHomCompTriple σ₂₃
 σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (f : M
₁ ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (h : M₃ ->ₛₗ[σ₃₄] M₄) : ((h.comp g : M₂ ->
ₛₗ[σ₂₄] M₄).comp f : M₁ ->ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ ->ₛₗ[σ₁₃] M₃)
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；g : M₂ ->ₛₗ[σ₂₃] M₃；h : M₃ ->ₛₗ[σ₃₄] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc
    {R₄ M₄ : Type*} [Semiring R₄] [AddCommMonoid M₄] [Module R₄ M₄]
    {σ₃₄ : R₃ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
    [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
    (f : M₁ →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M₁ →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M₁ →ₛₗ[σ₁₃] M₃) :=
  rfl

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

/-- The linear map version of `Function.Surjective.injective_comp_right` -/
/-
**LinearMap._root_.Function.Surjective.injective_linearMapComp_right** 是 Mathlib
 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map version of `Function.Surjective.injective_comp_right`
-/
lemma _root_.Function.Surjective.injective_linearMapComp_right (hg : Surjective g) :
    Injective fun f : M₂ →ₛₗ[σ₂₃] M₃ ↦ f.comp g :=
  fun _ _ h ↦ ext <| hg.forall.2 (LinearMap.ext_iff.1 h)

@[simp]
/-
**LinearMap.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f'
参数：hg : Surjective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Surjective.injective_linearMapComp_right`：∀ {R₁ : Type u_2} {R₂
 : Type u_3} {R₃ : Type u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [
inst : Semiring R₁]   [inst_1 : Semirin…
-/
theorem cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  hg.injective_linearMapComp_right.eq_iff

/-- The linear map version of `Function.Injective.comp_left` -/
/-
**LinearMap._root_.Function.Injective.injective_linearMapComp_left** 是 Mathlib 中
的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map version of `Function.Injective.comp_left`
-/
lemma _root_.Function.Injective.injective_linearMapComp_left (hf : Injective f) :
    Injective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g :=
  fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) ↦ ext fun x ↦ hf <| by rw [← comp_apply, h, comp_apply]
/-
**LinearMap.surjective_comp_left_of_exists_rightInverse** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
形式化陈述：surjective_comp_left_of_exists_rightInverse {σ₃₂ : R₃ ->+* R₂} [RingHomInv
Pair σ₂₃ σ₃₂] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂] (hf : exists f' : M₃ ->ₛₗ[σ₃₂] M₂,
 f.comp f' = .id) : Surjective fun g : M₁ ->ₛₗ[σ₁₂] M₂ => f.comp g
参数：hf : exists f' : M₃ ->ₛₗ[σ₃₂] M₂, f.comp f' = .id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_comp_left_of_exists_rightInverse {σ₃₂ : R₃ →+* R₂}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    (hf : ∃ f' : M₃ →ₛₗ[σ₃₂] M₂, f.comp f' = .id) :
    Surjective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g := by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← comp_assoc, hf', id_comp]

@[simp]
/-
**LinearMap.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g'
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.injective_linearMapComp_left`：∀ {R₁ : Type u_2} {R₂ :
 Type u_3} {R₃ : Type u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [in
st : Semiring R₁]   [inst_1 : Semirin…
-/
theorem cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  hf.injective_linearMapComp_left.eq_iff

end

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ']

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
@[implicit_reducible]
/-
**LinearMap.inverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：inverse (f : M ->ₛₗ[σ] M₂) (g : M₂ -> M) (h₁ : LeftInverse g f) (h₂ : Righ
tInverse g f) : M₂ ->ₛₗ[σ'] M
参数：f : M ->ₛₗ[σ] M₂；g : M₂ -> M；h₁ : LeftInverse g f；h₂ : RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `g` is a left and right inverse of a linear map `f`, then `g` is l
inear itself.
-/
def inverse (f : M →ₛₗ[σ] M₂) (g : M₂ → M) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    M₂ →ₛₗ[σ'] M := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact
    { toFun := g
      map_add' := fun x y ↦ by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂]
      map_smul' := fun a b ↦ by
        rw [← h₁ (g (a • b)), ← h₁ (σ' a • g b)]
        simp [h₂] }

variable (f : M →ₛₗ[σ] M₂) (g : M₂ →ₛₗ[σ'] M) (h : g.comp f = .id)

include h
/-
**LinearMap.injective_of_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：injective_of_comp_eq_id : Injective f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
theorem injective_of_comp_eq_id : Injective f :=
  .of_comp (f := g) <| by simp_rw [← coe_comp, h, id_coe, bijective_id.1]
/-
**LinearMap.surjective_of_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：surjective_of_comp_eq_id : Surjective g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
theorem surjective_of_comp_eq_id : Surjective g :=
  .of_comp (g := f) <| by simp_rw [← coe_comp, h, id_coe, bijective_id.2]

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommGroup M₂]
variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R →+* S}
variable (f : M →ₛₗ[σ] M₂)

/-
**LinearMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : Type u_10} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGro
up M₂] {module_M : _root_.Module R M} {module_M₂ : _root_.Module S M₂}   {σ : R 
→+* S} (f : M →ₛₗ[σ] M₂) (x : M), f (-x) = -f x
参数：f : M →ₛₗ[σ] M₂；x : M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_neg (x : M) : f (-x) = -f x :=
  map_neg f x
/-
**LinearMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : Type u_10} [inst : Se
miring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGro
up M₂] {module_M : _root_.Module R M} {module_M₂ : _root_.Module S M₂}   {σ : R 
→+* S} (f : M →ₛₗ[σ] M₂) (x y : M), f (x - y) = f x - f y
参数：f : M →ₛₗ[σ] M₂；x y : M；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_sub (x y : M) : f (x - y) = f x - f y :=
  map_sub f x y
/-
**LinearMap.CompatibleSMul.intModule** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Compat
ibleSMul`。
形式化陈述：∀ {M : Type u_8} {M₂ : Type u_10} [inst : AddCommGroup M] [inst_1 : AddCom
mGroup M₂] {S : Type u_14}   [inst_2 : Semiring S] [inst_3 : _root_.Module S M] 
[inst_4 : _root_.Module S M₂], LinearMap.CompatibleSMul M M₂ ℤ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
-/
instance CompatibleSMul.intModule {S : Type*} [Semiring S] [Module S M] [Module S M₂] :
    CompatibleSMul M M₂ ℤ S :=
  ⟨fun fₗ c x ↦ by
    induction c with
    | zero => simp
    | succ n ih => simp [add_smul]
    | pred n ih => simp [sub_smul]⟩
/-
**LinearMap.CompatibleSMul.units** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Compatible
SMul`。
形式化陈述：∀ {M : Type u_8} {M₂ : Type u_10} [inst : AddCommGroup M] [inst_1 : AddCom
mGroup M₂] {R : Type u_14} {S : Type u_15}   [inst_2 : Monoid R] [inst_3 : MulAc
tion R M] [inst_4 : MulAction R M₂] [inst_5 : Semiring S]   [inst_6 : _root_.Mod
ule S M] [inst_7 : _root_.Module S M₂] [LinearMap.CompatibleSMul M M₂ R S],   Li
nearMap.CompatibleSMul M M₂ Rˣ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.map_smul`：∀ {M : Type u_8} {M₂ : Type u_10} {in
st : AddCommMonoid M} {inst_1 : AddCommMonoid M₂} {R : Type u_14} {S : Type u_15
}   {inst_2 : Semiring …
-/
instance CompatibleSMul.units {R S : Type*} [Monoid R] [MulAction R M] [MulAction R M₂]
    [Semiring S] [Module S M] [Module S M₂] [CompatibleSMul M M₂ R S] : CompatibleSMul M M₂ Rˣ S :=
  ⟨fun fₗ c x ↦ (CompatibleSMul.map_smul fₗ (c : R) x :)⟩

end AddCommGroup

end LinearMap

namespace Module

/-- `g : R →+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
/-
**Module.compHom.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Module.compHom`。
形式化陈述：{R : Type u_14} → {S : Type u_15} → [inst : Semiring R] → [inst_1 : Semiri
ng S] → (g : R →+* S) → R →ₗ[R] S
参数：g : R →+* S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g : R →+* S` is `R`-linear when the module structure on `S` is `Module.compHom 
S g` .
-/
def compHom.toLinearMap {R S : Type*} [Semiring R] [Semiring S] (g : R →+* S) :
    letI := compHom S g; R →ₗ[R] S :=
  letI := compHom S g
  { toFun := (g : R → S)
    map_add' := g.map_add
    map_smul' := g.map_mul }

end Module

namespace DistribMulActionHom

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Semiring R] [Module R M] [Semiring S] [Module S M₂] [Module R M₃]
variable {σ : R →+* S}

/-
**DistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `DistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilinearMapClass (M →ₑ+[σ.toMonoidHom] M₂) σ M M₂ where

/-- A `DistribMulActionHom` between two modules is a linear map. -/
/-
**DistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `DistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `DistribMulActionHom` between two modules is a linear map.
-/
instance : LinearMapClass (M →+[R] M₃) R M M₃ where

@[simp]
/-
**DistribMulActionHom.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `DistribMulActio
nHom`。
形式化陈述：coe_toLinearMap (f : M ->ₑ+[σ.toMonoidHom] M₂) : ((f : M ->ₛₗ[σ] M₂) : M -
> M₂) = f
参数：f : M ->ₑ+[σ.toMonoidHom] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type u
_5} {M : Type u_8} {M₂ : Type u_10} [inst : AddCommMonoid M] [inst_1 : AddCommMo
noid M₂]   [inst_2 : Semiring R]…
-/
theorem coe_toLinearMap (f : M →ₑ+[σ.toMonoidHom] M₂) : ((f : M →ₛₗ[σ] M₂) : M → M₂) = f :=
  rfl
/-
**DistribMulActionHom.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `DistribMu
lActionHom`。
形式化陈述：toLinearMap_injective {f g : M ->ₑ+[σ.toMonoidHom] M₂} (h : (f : M ->ₛₗ[σ]
 M₂) = (g : M ->ₛₗ[σ] M₂)) : f = g
参数：h : (f : M ->ₛₗ[σ] M₂) = (g : M ->ₛₗ[σ] M₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type u
_5} {M : Type u_8} {M₂ : Type u_10} [inst : AddCommMonoid M] [inst_1 : AddCommMo
noid M₂]   [inst_2 : Semiring R]…
· 使用定理 `DistribMulActionHom.ext`：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_
2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A]   [ins
t_3 : Distrib…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem toLinearMap_injective {f g : M →ₑ+[σ.toMonoidHom] M₂}
    (h : (f : M →ₛₗ[σ] M₂) = (g : M →ₛₗ[σ] M₂)) :
    f = g := by
  ext m
  exact LinearMap.congr_fun h m

end DistribMulActionHom

namespace IsLinearMap

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- Convert an `IsLinearMap` predicate to a `LinearMap` -/
/-
**IsLinearMap.mk'** 是 Mathlib 中的一个定义，位于命名空间 `IsLinearMap`。
形式化陈述：mk' (f : M -> M₂) (lin : IsLinearMap R f) : M ->ₗ[R] M₂ where toFun
参数：f : M -> M₂；lin : IsLinearMap R f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.map_add`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _r
oot_.Modu…
· 使用定理 `IsLinearMap.map_smul`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _
root_.Modu…

--- 原说明 ---
Convert an `IsLinearMap` predicate to a `LinearMap`
-/
def mk' (f : M → M₂) (lin : IsLinearMap R f) : M →ₗ[R] M₂ where
  toFun := f
  map_add' := lin.1
  map_smul' := lin.2

@[simp]
/-
**IsLinearMap.mk'_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst
_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R M₂] {f : M → M₂}   (lin : IsLinearMap R f) (x : M), (
IsLinearMap.mk' f lin) x = f x
参数：lin : IsLinearMap R f；x : M；IsLinearMap.mk' f lin。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk'_apply {f : M → M₂} (lin : IsLinearMap R f) (x : M) : mk' f lin x = f x :=
  rfl
/-
**IsLinearMap.isLinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module 
R M] (c : R) : IsLinearMap R fun z : M => c • z
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isLinearMap_smul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (c : R) :
    IsLinearMap R fun z : M ↦ c • z := by
  refine IsLinearMap.mk (smul_add c) ?_
  intro _ _
  simp only [smul_smul, mul_comm]
/-
**IsLinearMap.isLinearMap_smul'** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M
] (a : M) : IsLinearMap R fun c : R => c • a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem isLinearMap_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (a : M) :
    IsLinearMap R fun c : R ↦ c • a :=
  IsLinearMap.mk (fun x y ↦ add_smul x y a) fun x y ↦ mul_smul x y a
/-
**IsLinearMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：map_zero {f : M -> M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂)
参数：lin : IsLinearMap R f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem map_zero {f : M → M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂) :=
  (lin.mk' f).map_zero

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R M₂]

/-
**IsLinearMap.isLinearMap_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：isLinearMap_neg : IsLinearMap R fun z : M => -z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem isLinearMap_neg : IsLinearMap R fun z : M ↦ -z :=
  IsLinearMap.mk neg_add fun x y ↦ (smul_neg x y).symm
/-
**IsLinearMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：map_neg {f : M -> M₂} (lin : IsLinearMap R f) (x : M) : f (-x) = -f x
参数：lin : IsLinearMap R f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem map_neg {f : M → M₂} (lin : IsLinearMap R f) (x : M) : f (-x) = -f x :=
  (lin.mk' f).map_neg x
/-
**IsLinearMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearMap`。
形式化陈述：map_sub {f : M -> M₂} (lin : IsLinearMap R f) (x y : M) : f (x - y) = f x 
- f y
参数：lin : IsLinearMap R f；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem map_sub {f : M → M₂} (lin : IsLinearMap R f) (x y : M) : f (x - y) = f x - f y :=
  (lin.mk' f).map_sub x y

end AddCommGroup

end IsLinearMap

/-- Reinterpret an additive homomorphism as an `ℕ`-linear map. -/
/-
**AddMonoidHom.toNatLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M ->
+ M₂) : M ->ₗ[Nat] M₂ where toFun
参数：f : M ->+ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an additive homomorphism as an `ℕ`-linear map.
-/
def AddMonoidHom.toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) :
    M →ₗ[ℕ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_nsmul f
/-
**AddMonoidHom.toNatLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂]
 : Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem AddMonoidHom.toNatLinearMap_injective [AddCommMonoid M] [AddCommMonoid M₂] :
    Function.Injective (@AddMonoidHom.toNatLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/-
**AddMonoidHom.coe_toNatLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : 
M ->+ M₂) : ⇑f.toNatLinearMap = f
参数：f : M ->+ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoidHom.coe_toNatLinearMap [AddCommMonoid M] [AddCommMonoid M₂] (f : M →+ M₂) :
    ⇑f.toNatLinearMap = f :=
  rfl

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
/-
**AddMonoidHom.toIntLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M ->+ 
M₂) : M ->ₗ[Int] M₂ where toFun
参数：f : M ->+ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an additive homomorphism as a `ℤ`-linear map.
-/
def AddMonoidHom.toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) : M →ₗ[ℤ] M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_zsmul f
/-
**AddMonoidHom.toIntLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
 Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem AddMonoidHom.toIntLinearMap_injective [AddCommGroup M] [AddCommGroup M₂] :
    Function.Injective (@AddMonoidHom.toIntLinearMap M M₂ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x

@[simp]
/-
**AddMonoidHom.coe_toIntLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.coe_toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M 
->+ M₂) : ⇑f.toIntLinearMap = f
参数：f : M ->+ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoidHom.coe_toIntLinearMap [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂) :
    ⇑f.toIntLinearMap = f :=
  rfl

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂}
variable [DistribSMul S M₂] [SMulCommClass R₂ S M₂]
variable [DistribSMul T M₂] [SMulCommClass R₂ T M₂]

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun a f ↦
    { toFun := a • (f : M → M₂)
      map_add' := fun x y ↦ by simp only [Pi.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp [Pi.smul_apply, smul_comm] }⟩

@[simp]
/-
**LinearMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x
参数：a : S；f : M ->ₛₗ[σ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
  rfl

@[simp]
/-
**LinearMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_smul (a : S) (f : M ->ₛₗ[σ₁₂] M₂) : (a • f : M ->ₛₗ[σ₁₂] M₂) = a • (f 
: M -> M₂)
参数：a : S；f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (a : S) (f : M →ₛₗ[σ₁₂] M₂) : (a • f : M →ₛₗ[σ₁₂] M₂) = a • (f : M → M₂) :=
  rfl
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T M₂] : SMulCommClass S T (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun _ _ _ ↦ ext fun _ ↦ smul_comm _ _ _⟩

-- example application of this instance: if S -> T -> R are homomorphisms of commutative rings and
-- M and M₂ are R-modules then the S-module and T-module structures on Hom_R(M,M₂) are compatible.
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T M₂] : IsScalarTower S T (M →ₛₗ[σ₁₂] M₂) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc _ _ _
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul Sᵐᵒᵖ M₂] [SMulCommClass R₂ Sᵐᵒᵖ M₂] [IsCentralScalar S M₂] :
    IsCentralScalar S (M →ₛₗ[σ₁₂] M₂) where
  op_smul_eq_smul _ _ := ext fun _ ↦ op_smul_eq_smul _ _

end SMul

/-! ### Arithmetic on the codomain -/

section Arithmetic

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommGroup N₂] [AddCommGroup N₃]
variable [Module R₁ M] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₂ N₂] [Module R₃ N₃]
variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The constant 0 map is linear. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant 0 map is linear.
-/
instance : Zero (M →ₛₗ[σ₁₂] M₂) :=
  ⟨{  toFun := 0
      map_add' := by simp
      map_smul' := by simp }⟩
/-
**LinearMap.coe_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_8} {M₂ : Type u_10} [inst : 
Semiring R₁] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCo
mmMonoid M₂] [inst_4 : _root_.Module R₁ M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂
 : R₁ →+* R₂} (f : M →ₛₗ[σ₁₂] M₂), ⇑f = 0 ↔ f = 0
参数：f : M →ₛₗ[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma coe_zero_iff (f : M →ₛₗ[σ₁₂] M₂) : ⇑f = 0 ↔ f = 0 := by
  aesop

@[simp]
/-
**LinearMap.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : M) : (0 : M →ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

@[simp]
/-
**LinearMap.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁
₃] M₃) = 0
参数：g : M₂ ->ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem comp_zero (g : M₂ →ₛₗ[σ₂₃] M₃) : (g.comp (0 : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = 0 :=
  ext fun c ↦ by rw [comp_apply, zero_apply, zero_apply, g.map_zero]

@[simp]
/-
**LinearMap.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：zero_comp (f : M ->ₛₗ[σ₁₂] M₂) : ((0 : M₂ ->ₛₗ[σ₂₃] M₃).comp f : M ->ₛₗ[σ₁
₃] M₃) = 0
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_comp (f : M →ₛₗ[σ₁₂] M₂) : ((0 : M₂ →ₛₗ[σ₂₃] M₃).comp f : M →ₛₗ[σ₁₃] M₃) = 0 :=
  rfl
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M →ₛₗ[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
/-
**LinearMap.default_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：default_def : (default : M ->ₛₗ[σ₁₂] M₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_def : (default : M →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
/-
**LinearMap.uniqueOfLeft** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：uniqueOfLeft [Subsingleton M] : Unique (M ->ₛₗ[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueOfLeft [Subsingleton M] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  { (inferInstance : Inhabited (M →ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }
/-
**LinearMap.uniqueOfRight** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：uniqueOfRight [Subsingleton M₂] : Unique (M ->ₛₗ[σ₁₂] M₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.coe_injective`：coe_injective : Injective (DFunLike.coe : (M ->
ₛₗ[σ] M₃) -> _)
-/
instance uniqueOfRight [Subsingleton M₂] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique
/-
**LinearMap.ne_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ne_zero_of_injective [Nontrivial M] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f
) : f != 0
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ne_zero_of_injective [Nontrivial M] {f : M →ₛₗ[σ₁₂] M₂} (hf : Injective f) : f ≠ 0 :=
  have ⟨x, ne⟩ := exists_ne (0 : M)
  fun h ↦ hf.ne ne <| by simp [h]
/-
**LinearMap.ne_zero_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ne_zero_of_surjective [Nontrivial M₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Surjectiv
e f) : f != 0
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ne_zero_of_surjective [Nontrivial M₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : Surjective f) : f ≠ 0 := by
  have ⟨y, ne⟩ := exists_ne (0 : M₂)
  obtain ⟨x, rfl⟩ := hf y
  exact fun h ↦ ne congr($h x)

/-- The sum of two linear maps is linear. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two linear maps is linear.
-/
instance : Add (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun f g ↦
    { toFun := f + g
      map_add' := by simp [add_comm, add_left_comm]
      map_smul' := by simp [smul_add] }⟩

@[simp]
/-
**LinearMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x
参数：f g : M ->ₛₗ[σ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
  rfl
/-
**LinearMap.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：add_comp (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] M₃) : ((h + g).comp f : 
M ->ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f
参数：f : M ->ₛₗ[σ₁₂] M₂；g h : M₂ ->ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] M₃) :
    ((h + g).comp f : M →ₛₗ[σ₁₃] M₃) = h.comp f + g.comp f :=
  rfl
/-
**LinearMap.comp_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_add (f g : M ->ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃) : (h.comp (f + g) : 
M ->ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g
参数：f g : M ->ₛₗ[σ₁₂] M₂；h : M₂ ->ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem comp_add (f g : M →ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃) :
    (h.comp (f + g) : M →ₛₗ[σ₁₃] M₃) = h.comp f + h.comp g :=
  ext fun _ ↦ h.map_add _ _

-- The `AddMonoid` instance exists to help speedup unification
/-
**LinearMap.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：addMonoid : AddMonoid (M ->ₛₗ[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid (M →ₛₗ[σ₁₂] M₂) := fast_instance%
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The type of linear maps is an additive monoid. -/
/-
**LinearMap.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：addCommMonoid : AddCommMonoid (M ->ₛₗ[σ₁₂] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of linear maps is an additive monoid.
-/
instance addCommMonoid : AddCommMonoid (M →ₛₗ[σ₁₂] M₂) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The negation of a linear map is linear. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation of a linear map is linear.
-/
instance : Neg (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f ↦
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp }⟩
/-
**LinearMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_8} {N₂ : Type u_12} [inst : 
Semiring R₁] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCo
mmGroup N₂] [inst_4 : _root_.Module R₁ M] [inst_5 : _root_.Module R₂ N₂]   {σ₁₂ 
: R₁ →+* R₂} (f : M →ₛₗ[σ₁₂] N₂), ⇑(-f) = -⇑f
参数：f : M →ₛₗ[σ₁₂] N₂；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem coe_neg (f : M →ₛₗ[σ₁₂] N₂) : ⇑(-f) = -⇑f := rfl

@[simp]
/-
**LinearMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x
参数：f : M ->ₛₗ[σ₁₂] N₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : M →ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -f x :=
  rfl

@[simp]
/-
**LinearMap.neg_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：neg_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.com
p f
参数：f : M ->ₛₗ[σ₁₂] M₂；g : M₂ ->ₛₗ[σ₂₃] N₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] N₃) : (-g).comp f = -g.comp f :=
  rfl

@[simp]
/-
**LinearMap.comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_neg (f : M ->ₛₗ[σ₁₂] N₂) (g : N₂ ->ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.com
p f
参数：f : M ->ₛₗ[σ₁₂] N₂；g : N₂ ->ₛₗ[σ₂₃] N₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem comp_neg (f : M →ₛₗ[σ₁₂] N₂) (g : N₂ →ₛₗ[σ₂₃] N₃) : g.comp (-f) = -g.comp f :=
  ext fun _ ↦ g.map_neg _

/-- The subtraction of two linear maps is linear. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtraction of two linear maps is linear.
-/
instance : Sub (M →ₛₗ[σ₁₂] N₂) :=
  ⟨fun f g ↦
    { toFun := f - g
      map_add' := fun x y ↦ by simp only [Pi.sub_apply, map_add, add_sub_add_comm]
      map_smul' := fun r x ↦ by simp [Pi.sub_apply, smul_sub] }⟩

@[simp]
/-
**LinearMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x
参数：f g : M ->ₛₗ[σ₁₂] N₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
  rfl
/-
**LinearMap.sub_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sub_comp (f : M ->ₛₗ[σ₁₂] M₂) (g h : M₂ ->ₛₗ[σ₂₃] N₃) : (g - h).comp f = g
.comp f - h.comp f
参数：f : M ->ₛₗ[σ₁₂] M₂；g h : M₂ ->ₛₗ[σ₂₃] N₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_comp (f : M →ₛₗ[σ₁₂] M₂) (g h : M₂ →ₛₗ[σ₂₃] N₃) :
    (g - h).comp f = g.comp f - h.comp f :=
  rfl
/-
**LinearMap.comp_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_sub (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃) : h.comp (g - f) = h
.comp g - h.comp f
参数：f g : M ->ₛₗ[σ₁₂] N₂；h : N₂ ->ₛₗ[σ₂₃] N₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem comp_sub (f g : M →ₛₗ[σ₁₂] N₂) (h : N₂ →ₛₗ[σ₂₃] N₃) :
    h.comp (g - f) = h.comp g - h.comp f :=
  ext fun _ ↦ h.map_sub _ _

/-- The type of linear maps is an additive group. -/
/-
**LinearMap.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：addCommGroup : AddCommGroup (M ->ₛₗ[σ₁₂] N₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of linear maps is an additive group.
-/
instance addCommGroup : AddCommGroup (M →ₛₗ[σ₁₂] N₂) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `AddMonoidHom`. -/
@[simps]
/-
**LinearMap.evalAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：evalAddMonoidHom (a : M) : (M ->ₛₗ[σ₁₂] M₂) ->+ M₂ where toFun f
参数：a : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.add_apply`：add_apply (f g : M ->ₛₗ[σ₁₂] M₂) (x : M) : (f + g) 
x = f x + g x

--- 原说明 ---
Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `AddMonoidHom`.
-/
def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl

/-- `LinearMap.toAddMonoidHom` promoted to an `AddMonoidHom`. -/
@[simps]
/-
**LinearMap.toAddMonoidHom'** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom' : (M ->ₛₗ[σ₁₂] M₂) ->+ M ->+ M₂ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.toAddMonoidHom` promoted to an `AddMonoidHom`.
-/
def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

/-- If `M` is the zero module, then the identity map of `M` is the zero map. -/
@[simp]
/-
**LinearMap.identityMapOfZeroModuleIsZero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：identityMapOfZeroModuleIsZero [Subsingleton M] : id (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
If `M` is the zero module, then the identity map of `M` is the zero map.
-/
theorem identityMapOfZeroModuleIsZero [Subsingleton M] : id (R := R₁) (M := M) = 0 :=
  Subsingleton.eq_zero id

end Arithmetic

section Actions

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section SMul

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]

/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction S (M →ₛₗ[σ₁₂] M₂) where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _
/-
**LinearMap.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smul_comp (a : S₃) (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) : (a • g).co
mp f = a • g.comp f
参数：a : S₃；g : M₂ ->ₛₗ[σ₂₃] M₃；f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp (a : S₃) (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • g).comp f = a • g.comp f :=
  rfl

-- TODO: generalize this to semilinear maps
/-
**LinearMap.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAc
tion S M₃] [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ ->ₗ[R] M₂) 
(a : S) (f : M ->ₗ[R] M₃) : g.comp (a • f) = a • g.comp f
参数：g : M₃ ->ₗ[R] M₂；a : S；f : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem comp_smul [Module R M₂] [Module R M₃] [SMulCommClass R S M₂] [DistribMulAction S M₃]
    [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S R] (g : M₃ →ₗ[R] M₂) (a : S) (f : M →ₗ[R] M₃) :
    g.comp (a • f) = a • g.comp f :=
  ext fun _ ↦ g.map_smul_of_tower _ _

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M₂] [SMulCommClass R₂ S M₂]

/-
**LinearMap.module** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：module : Module S (M ->ₛₗ[σ₁₂] M₂) where add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module S (M →ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul _ _

end Module

end Actions

section RestrictScalarsAsLinearMap

variable {R S M N P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]

variable (R S M N) in
@[simp]
/-
**LinearMap.restrictScalars_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_zero : (0 : M ->ₗ[S] N).restrictScalars R = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_zero : (0 : M →ₗ[S] N).restrictScalars R = 0 :=
  rfl

@[simp]
/-
**LinearMap.restrictScalars_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_add (f g : M ->ₗ[S] N) : (f + g).restrictScalars R = f.res
trictScalars R + g.restrictScalars R
参数：f g : M ->ₗ[S] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_add (f g : M →ₗ[S] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl

@[simp]
/-
**LinearMap.restrictScalars_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_neg {M N : Type*} [AddCommMonoid M] [AddCommGroup N] [Modu
le R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S] (f : M -
>ₗ[S] N) : (-f).restrictScalars R = -f.restrictScalars R
参数：f : M ->ₗ[S] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_neg {M N : Type*} [AddCommMonoid M] [AddCommGroup N]
    [Module R M] [Module R N] [Module S M] [Module S N] [CompatibleSMul M N R S]
    (f : M →ₗ[S] N) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl

variable {R₁ : Type*} [Semiring R₁] [Module R₁ N] [SMulCommClass S R₁ N] [SMulCommClass R R₁ N]

@[simp]
/-
**LinearMap.restrictScalars_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_smul (c : R₁) (f : M ->ₗ[S] N) : (c • f).restrictScalars R
 = c • f.restrictScalars R
参数：c : R₁；f : M ->ₗ[S] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_smul (c : R₁) (f : M →ₗ[S] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

@[simp]
/-
**LinearMap.restrictScalars_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_comp [AddCommMonoid P] [Module S P] [Module R P] [Compatib
leSMul N P R S] [CompatibleSMul M P R S] (f : N ->ₗ[S] P) (g : M ->ₗ[S] N) : (f 
∘ₗ g).restrictScalars R = f.restrictScalars R ∘ₗ g.restrictScalars R
参数：f : N ->ₗ[S] P；g : M ->ₗ[S] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_comp [AddCommMonoid P] [Module S P] [Module R P]
    [CompatibleSMul N P R S] [CompatibleSMul M P R S] (f : N →ₗ[S] P) (g : M →ₗ[S] N) :
    (f ∘ₗ g).restrictScalars R = f.restrictScalars R ∘ₗ g.restrictScalars R :=
  rfl

@[simp]
/-
**LinearMap.restrictScalars_trans** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrictScalars_trans {T : Type*} [Semiring T] [Module T M] [Module T N] [
CompatibleSMul M N S T] [CompatibleSMul M N R T] (f : M ->ₗ[T] N) : (f.restrictS
calars S).restrictScalars R = f.restrictScalars R
参数：f : M ->ₗ[T] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_trans {T : Type*} [Semiring T] [Module T M] [Module T N]
    [CompatibleSMul M N S T] [CompatibleSMul M N R T] (f : M →ₗ[T] N) :
    (f.restrictScalars S).restrictScalars R = f.restrictScalars R :=
  rfl

variable (S M N R R₁)

/-- `LinearMap.restrictScalars` as a `LinearMap`. -/
@[simps apply]
/-
**LinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：(R : Type u_1) →   {S : Type u_5} →     {M : Type u_8} →       {M₂ : Type 
u_10} →         [inst : Semiring R] →           [inst_1 : Semiring S] →         
    [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M₂] →    
             [inst_4 : _root_.Module R M] →                   [inst_5 : _root_.M
odule R M₂] →                     [inst_6 : _root_.Module S M] →                
       [inst_7 : _root_.Module S M₂] → [LinearMap.CompatibleSMul M M₂ R S] → (M 
→ₗ[S] M₂) → M →ₗ[R] M₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.restrictScalars` as a `LinearMap`.
-/
def restrictScalarsₗ : (M →ₗ[S] N) →ₗ[R₁] M →ₗ[R] N where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

end RestrictScalarsAsLinearMap

section mulLeftRight
variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section left
variable (R) [SMulCommClass R A A]

/-- The multiplication on the left in an algebra is a linear map.

Note that this only assumes `SMulCommClass R A A`, so that it also works for `R := Aᵐᵒᵖ`.

When `A` is unital and associative, this is the same as `DistribSMul.toLinearMap R A a` -/
/-
**LinearMap.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mulLeft (a : A) : A ->ₗ[R] A where __
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on the left in an algebra is a linear map.

Note that this only assumes `SMulCommClass R A A`, so that it also works for `R 
:= Aᵐᵒᵖ`.

When `A` is unital and associative, this is the same as `DistribSMul.toLinearMap
 R A a`
-/
def mulLeft (a : A) : A →ₗ[R] A where
  __ := AddMonoidHom.mulLeft a
  map_smul' _ := mul_smul_comm _ _

@[simp]
/-
**LinearMap.mulLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeft_apply (a b : A) : mulLeft R a b = a * b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeft_apply (a b : A) : mulLeft R a b = a * b := rfl

@[simp]
/-
**LinearMap.toAddMonoidHom_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom_mulLeft (a : A) : (mulLeft R a : A ->+ A) = AddMonoidHom.mu
lLeft a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem toAddMonoidHom_mulLeft (a : A) : (mulLeft R a : A →+ A) = AddMonoidHom.mulLeft a := rfl

variable (A) in
@[simp]
/-
**LinearMap.mulLeft_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem mulLeft_zero_eq_zero : mulLeft R (0 : A) = 0 := ext zero_mul

end left

section right
variable (R) [IsScalarTower R A A]

/-- The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R := A`.

When `A` is unital and associative, this is the same as
`DistribSMul.toLinearMap R A (MulOpposite.op b)`. -/
/-
**LinearMap.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mulRight (b : A) : A ->ₗ[R] A where __
参数：b : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on the right in an algebra is a linear map.

Note that this only assumes `IsScalarTower R A A`, so that it also works for `R 
:= A`.

When `A` is unital and associative, this is the same as
`DistribSMul.toLinearMap R A (MulOpposite.op b)`.
-/
def mulRight (b : A) : A →ₗ[R] A where
  __ := AddMonoidHom.mulRight b
  map_smul' _ _ := smul_mul_assoc _ _ _

@[simp]
/-
**LinearMap.mulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulRight_apply (a b : A) : mulRight R a b = b * a
参数：a b : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRight_apply (a b : A) : mulRight R a b = b * a := rfl

@[simp]
/-
**LinearMap.toAddMonoidHom_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom_mulRight (a : A) : (mulRight R a : A ->+ A) = AddMonoidHom.
mulRight a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem toAddMonoidHom_mulRight (a : A) : (mulRight R a : A →+ A) = AddMonoidHom.mulRight a := rfl

variable (A) in
@[simp]
/-
**LinearMap.mulRight_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulRight_zero_eq_zero : mulRight R (0 : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mulRight_zero_eq_zero : mulRight R (0 : A) = 0 := ext mul_zero

end right

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable (R) in
/-- Simultaneous multiplication on the left and right is a linear map. -/
/-
**LinearMap.mulLeftRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mulLeftRight (ab : A × A) : A ->ₗ[R] A
参数：ab : A × A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simultaneous multiplication on the left and right is a linear map.
-/
def mulLeftRight (ab : A × A) : A →ₗ[R] A :=
  (mulRight R ab.snd).comp (mulLeft R ab.fst)

@[simp]
/-
**LinearMap.mulLeftRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b
参数：a b x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeftRight_apply (a b x : A) : mulLeftRight R (a, b) x = a * x * b :=
  rfl

end mulLeftRight

end LinearMap

