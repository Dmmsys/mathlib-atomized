/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Positive linear maps

This file defines positive linear maps as a linear map that is also an order homomorphism.

## Implementation notes

We do not define `PositiveLinearMapClass` to avoid adding a class that mixes order and algebra.
One can achieve the same effect by using a combination of `LinearMapClass` and `OrderHomClass`.
We nevertheless use the namespace for lemmas using that combination of typeclasses.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

@[expose] public section

/--
Definition of `PositiveLinearMap` / `PositiveLinearMap` 的定义

English:
structure PositiveLinearMap
  parameters: (R E₁ E₂ : Type*) [Semiring R]
  extends: E₁ ->ₗ[R] E₂, E₁ ->o E₂
  (no additional axioms)

中文:
结构 PositiveLinear映射
  参数: (R E₁ E₂ : 类型) [半环 R]
  继承: E₁ ->ₗ[R] E₂, E₁ ->o E₂
  (无附加公理)
-/
structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] extends E₁ ->ₗ[R] E₂, E₁ ->o E₂

/-- The `OrderHom` underlying a `PositiveLinearMap`. -/
add_decl_doc PositiveLinearMap.toOrderHom

/-- Notation for a `PositiveLinearMap`. -/
notation:25 E " ->ₚ[" R:25 "] " F:0 => PositiveLinearMap R E F

section PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/--
Definition of `PositiveLinearMap.ofClass` / `PositiveLinearMap.ofClass` 的定义

English:
definition PositiveLinearMap.ofClass
  signature: (f : F)
  body: { (f : E₁ ->ₗ[R] E₂), (f : E₁ ->o E₂) with }

@[deprecated (since := "2026-06-10")]
alias PositiveLinearMapClass.toPositiveLinearMap := PositiveLinearMap.ofClass

中文:
定义 PositiveLinear映射.ofClass
  签名: (f : F)
  定义体: { (f : E₁ ->ₗ[R] E₂), (f : E₁ ->o E₂) with }

@[deprecated (since := "2026-06-10")]
alias PositiveLinearMapClass.toPositiveLinearMap := PositiveLinearMap.ofClass
-/
def PositiveLinearMap.ofClass (f : F) : E₁ ->ₚ[R] E₂ :=
  { (f : E₁ ->ₗ[R] E₂), (f : E₁ ->o E₂) with }

@[deprecated (since := "2026-06-10")]
alias PositiveLinearMapClass.toPositiveLinearMap := PositiveLinearMap.ofClass

/--
lemma `OrderHomClass.of_addMonoidHom` / 引理 `OrderHomClass.of_addMonoidHom`

English:
lemma OrderHomClass.of_addMonoidHom
  statement: {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
  proof: by simpa using h f (b - a) (sub_nonneg.mpr hab)

中文:
引理 序态射类.of_addMonoidHom
  结论: {F' E₁' E₂' : 类型} [函数状 F' E₁' E₂'] [加法群 E₁']
  证明: by simpa using h f (b - a) (sub_nonneg.mpr hab)

Depends on / 依赖: sub_nonneg, sub_nonneg.mpr
-/
lemma OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : forall f : F', forall x, 0 <= x -> 0 <= f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (E₁ ->ₚ[R] E₂) E₁ E₂
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

initialize_simps_projections PositiveLinearMap (toFun -> apply, as_prefix toLinearMap)

@[ext]

中文:
实例 :
  签名: 函数状 (E₁ ->ₚ[R] E₂) E₁ E₂
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

initialize_simps_projections PositiveLinearMap (toFun -> apply, as_prefix toLinearMap)

@[ext]

Depends on / 依赖: f.toFun
-/
instance : FunLike (E₁ ->ₚ[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

initialize_simps_projections PositiveLinearMap (toFun -> apply, as_prefix toLinearMap)

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
引理 ext
  条件: {f g : E₁ ->ₚ[R] E₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (R E₁) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : E₁ ->ₚ[R] E₁ where
  body: LinearMap.id
  __ := OrderHom.id

中文:
定义 id
  签名: : E₁ ->ₚ[R] E₁ where
  定义体: LinearMap.id
  __ := OrderHom.id
-/
@[simps! apply toLinearMap] protected def id : E₁ ->ₚ[R] E₁ where
  __ := LinearMap.id
  __ := OrderHom.id

/--
lemma `toOrderHom_id` / 引理 `toOrderHom_id`

English:
lemma toOrderHom_id
  statement: (PositiveLinearMap.id R E₁).toOrderHom = .id
  proof: rfl

中文:
引理 toOrderHom_id
  结论: (PositiveLinear映射.id R E₁).toOrderHom = .id
  证明: rfl
-/
@[simp] lemma toOrderHom_id : (PositiveLinearMap.id R E₁).toOrderHom = .id := rfl

/-- The composition of positive linear maps is again a positive linear map. -/
@[simps! apply toLinearMap]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂)
  body: g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'

中文:
定义 comp
  签名: (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂)
  定义体: g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'

Depends on / 依赖: f.toLinearMap, g.toLinearMap.comp, toLinearMap
-/
def comp (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂) : E₁ ->ₚ[R] E₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'

/--
lemma `toOrderHom_comp` / 引理 `toOrderHom_comp`

English:
lemma toOrderHom_comp
  given: (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂)
  proof: rfl

中文:
引理 toOrderHom_comp
  条件: (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂)
  证明: rfl
-/
@[simp] lemma toOrderHom_comp (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl

/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (f : E₁ ->ₚ[R] E₂)
  statement: f.comp (.id R E₁) = f
  proof: rfl

中文:
引理 comp_id
  条件: (f : E₁ ->ₚ[R] E₂)
  结论: f.comp (.id R E₁) = f
  证明: rfl
-/
@[simp] lemma comp_id (f : E₁ ->ₚ[R] E₂) : f.comp (.id R E₁) = f := rfl
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (f : E₁ ->ₚ[R] E₂)
  statement: (PositiveLinearMap.id R E₂).comp f = f
  proof: rfl

中文:
引理 id_comp
  条件: (f : E₁ ->ₚ[R] E₂)
  结论: (PositiveLinear映射.id R E₂).comp f = f
  证明: rfl
-/
@[simp] lemma id_comp (f : E₁ ->ₚ[R] E₂) : (PositiveLinearMap.id R E₂).comp f = f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (E₁ ->ₚ[R] E₂) R E₁ E₂
  body: map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

中文:
实例 :
  签名: 线性映射类 (E₁ ->ₚ[R] E₂) R E₁ E₂
  定义体: map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

Depends on / 依赖: f.toLinearMap, map_add, toLinearMap
-/
instance : LinearMapClass (E₁ ->ₚ[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (E₁ ->ₚ[R] E₂) E₁ E₂
  body: fun {_ _} hab => f.monotone' hab

@[simp]

中文:
实例 :
  签名: 序态射类 (E₁ ->ₚ[R] E₂) E₁ E₂
  定义体: fun {_ _} hab => f.monotone' hab

@[simp]

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass (E₁ ->ₚ[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

@[simp]
/--
lemma `map_smul_of_tower` / 引理 `map_smul_of_tower`

English:
lemma map_smul_of_tower
  statement: {S : Type*} [SMul S E₁] [SMul S E₂]
  proof: LinearMapClass.map_smul_of_tower f _ _

中文:
引理 map_smul_of_tower
  结论: {S : 类型} [标量乘法 S E₁] [标量乘法 S E₂]
  证明: LinearMapClass.map_smul_of_tower f _ _

Depends on / 依赖: LinearMapClass, LinearMapClass.map_smul_of_tower, map_smul_of_tower
-/
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ ->ₚ[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
/--
lemma `map_nonneg` / 引理 `map_nonneg`

English:
lemma map_nonneg
  given: (f : E₁ ->ₚ[R] E₂) {x : E₁} (hx : 0 <= x)
  statement: 0 <= f x
  proof: _root_.map_nonneg f hx

@[simp]

中文:
引理 map_nonneg
  条件: (f : E₁ ->ₚ[R] E₂) {x : E₁} (hx : 0 <= x)
  结论: 0 <= f x
  证明: _root_.map_nonneg f hx

@[simp]
-/
protected lemma map_nonneg (f : E₁ ->ₚ[R] E₂) {x : E₁} (hx : 0 <= x) : 0 <= f x :=
  _root_.map_nonneg f hx

@[simp]
/--
lemma `coe_toLinearMap` / 引理 `coe_toLinearMap`

English:
lemma coe_toLinearMap
  given: (f : E₁ ->ₚ[R] E₂)
  statement: (f.toLinearMap : E₁ -> E₂) = f
  proof: rfl

中文:
引理 coe_toLinearMap
  条件: (f : E₁ ->ₚ[R] E₂)
  结论: (f.toLinearMap : E₁ -> E₂) = f
  证明: rfl
-/
lemma coe_toLinearMap (f : E₁ ->ₚ[R] E₂) : (f.toLinearMap : E₁ -> E₂) = f :=
  rfl

/--
lemma `toLinearMap_injective` / 引理 `toLinearMap_injective`

English:
lemma toLinearMap_injective
  statement: Function.Injective (toLinearMap : (E₁ ->ₚ[R] E₂) -> (E₁ ->ₗ[R] E₂))
  proof: fun _ _ h => by ext x; congrm($h x)

@[simp]

中文:
引理 toLinearMap_injective
  结论: 函数.单射 (toLinearMap : (E₁ ->ₚ[R] E₂) -> (E₁ ->ₗ[R] E₂))
  证明: fun _ _ h => by ext x; congrm($h x)

@[simp]

Depends on / 依赖: congrm
-/
lemma toLinearMap_injective : Function.Injective (toLinearMap : (E₁ ->ₚ[R] E₂) -> (E₁ ->ₗ[R] E₂)) :=
  fun _ _ h => by ext x; congrm($h x)

@[simp]
/--
lemma `toLinearMap_inj` / 引理 `toLinearMap_inj`

English:
lemma toLinearMap_inj
  given: {f g : E₁ ->ₚ[R] E₂}
  statement: f.toLinearMap = g.toLinearMap ↔ f = g
  proof: toLinearMap_injective.eq_iff

中文:
引理 toLinearMap_inj
  条件: {f g : E₁ ->ₚ[R] E₂}
  结论: f.toLinearMap = g.toLinearMap ↔ f = g
  证明: toLinearMap_injective.eq_iff

Depends on / 依赖: eq_iff, toLinearMap_injective, toLinearMap_injective.eq_iff
-/
lemma toLinearMap_inj {f g : E₁ ->ₚ[R] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (E₁ ->ₚ[R] E₂)
  body: .mk (0 : E₁ ->ₗ[R] E₂) fun _ => by simp

@[simp]

中文:
实例 :
  签名: 零 (E₁ ->ₚ[R] E₂)
  定义体: .mk (0 : E₁ ->ₗ[R] E₂) fun _ => by simp

@[simp]
-/
instance : Zero (E₁ ->ₚ[R] E₂) where
  zero := .mk (0 : E₁ ->ₗ[R] E₂) fun _ => by simp

@[simp]
/--
lemma `toLinearMap_zero` / 引理 `toLinearMap_zero`

English:
lemma toLinearMap_zero
  statement: (0 : E₁ ->ₚ[R] E₂).toLinearMap = 0
  proof: rfl

@[simp]

中文:
引理 toLinearMap_zero
  结论: (0 : E₁ ->ₚ[R] E₂).toLinearMap = 0
  证明: rfl

@[simp]
-/
lemma toLinearMap_zero : (0 : E₁ ->ₚ[R] E₂).toLinearMap = 0 :=
  rfl

@[simp]
/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (x : E₁)
  statement: (0 : E₁ ->ₚ[R] E₂) x = 0
  proof: rfl

中文:
引理 zero_apply
  条件: (x : E₁)
  结论: (0 : E₁ ->ₚ[R] E₂) x = 0
  证明: rfl
-/
lemma zero_apply (x : E₁) : (0 : E₁ ->ₚ[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (E₁ ->ₚ[R] E₂)
  body: .mk (f.toLinearMap + g.toLinearMap) fun _ _ h =>
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]

中文:
实例 :
  签名: 加法 (E₁ ->ₚ[R] E₂)
  定义体: .mk (f.toLinearMap + g.toLinearMap) fun _ _ h =>
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]

Depends on / 依赖: f.toLinearMap, g.toLinearMap, toLinearMap
-/
instance : Add (E₁ ->ₚ[R] E₂) where
  add f g := .mk (f.toLinearMap + g.toLinearMap) fun _ _ h =>
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]
/--
lemma `toLinearMap_add` / 引理 `toLinearMap_add`

English:
lemma toLinearMap_add
  given: (f g : E₁ ->ₚ[R] E₂)
  proof: by
  rfl

@[simp]

中文:
引理 toLinearMap_add
  条件: (f g : E₁ ->ₚ[R] E₂)
  证明: by
  rfl

@[simp]
-/
lemma toLinearMap_add (f g : E₁ ->ₚ[R] E₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := by
  rfl

@[simp]
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (f g : E₁ ->ₚ[R] E₂) (x : E₁)
  proof: by
  rfl

中文:
引理 add_apply
  条件: (f g : E₁ ->ₚ[R] E₂) (x : E₁)
  证明: by
  rfl
-/
lemma add_apply (f g : E₁ ->ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (E₁ ->ₚ[R] E₂)
  body: .mk (n • f.toLinearMap) fun x y h => by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]

中文:
实例 :
  签名: 标量乘法 自然数 (E₁ ->ₚ[R] E₂)
  定义体: .mk (n • f.toLinearMap) fun x y h => by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]

Depends on / 依赖: OrderHomClass, OrderHomClass.mono, add_le_add, add_nsmul, f.toLinearMap, toLinearMap
-/
instance : SMul Nat (E₁ ->ₚ[R] E₂) where
  smul n f := .mk (n • f.toLinearMap) fun x y h => by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]
/--
lemma `toLinearMap_nsmul` / 引理 `toLinearMap_nsmul`

English:
lemma toLinearMap_nsmul
  given: (f : E₁ ->ₚ[R] E₂) (n : Nat)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_nsmul
  条件: (f : E₁ ->ₚ[R] E₂) (n : 自然数)
  证明: rfl

@[simp]
-/
lemma toLinearMap_nsmul (f : E₁ ->ₚ[R] E₂) (n : Nat) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

@[simp]
/--
lemma `nsmul_apply` / 引理 `nsmul_apply`

English:
lemma nsmul_apply
  given: (f : E₁ ->ₚ[R] E₂) (n : Nat) (x : E₁)
  proof: rfl

中文:
引理 nsmul_apply
  条件: (f : E₁ ->ₚ[R] E₂) (n : 自然数) (x : E₁)
  证明: rfl
-/
lemma nsmul_apply (f : E₁ ->ₚ[R] E₂) (n : Nat) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (E₁ ->ₚ[R] E₂)
  body: toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

中文:
实例 :
  签名: 加法交换幺半群 (E₁ ->ₚ[R] E₂)
  定义体: toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

Depends on / 依赖: addCommMonoid, toLinearMap_add, toLinearMap_injective, toLinearMap_injective.addCommMonoid, toLinearMap_nsmul, toLinearMap_zero
-/
instance : AddCommMonoid (E₁ ->ₚ[R] E₂) :=
  toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

end general

section addgroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂]

/--
Definition of `mk₀` / `mk₀` 的定义

English:
definition mk₀
  signature: (f : E₁ ->ₗ[R] E₂) (hf : forall x, 0 <= x -> 0 <= f x)
  body: { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 <= f (b - a) := hf _ hab
      simpa using this }

中文:
定义 mk₀
  签名: (f : E₁ ->ₗ[R] E₂) (hf : 对任意 x, 0 <= x -> 0 <= f x)
  定义体: { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 <= f (b - a) := hf _ hab
      simpa using this }

Depends on / 依赖: monotone, sub_nonneg
-/
def mk₀ (f : E₁ ->ₗ[R] E₂) (hf : forall x, 0 <= x -> 0 <= f x) : E₁ ->ₚ[R] E₂ :=
  { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 <= f (b - a) := hf _ hab
      simpa using this }

end addgroup

end PositiveLinearMap
