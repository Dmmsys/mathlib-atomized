/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.UnivLE
public import Mathlib.Logic.Small.Basic

/-!
# Essentially small categories.

A category given by `(C : Type u) [Category.{v} C]` is `w`-essentially small
if there exists a `SmallModel C : Type w` equipped with `[SmallCategory (SmallModel C)]` and an
equivalence `C ≌ SmallModel C`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `Skeleton C` is `w`-small, and `C` is `w`-locally small.
-/

@[expose] public section


universe w w' v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `EssentiallySmall.{w}` if there exists
an equivalence to some `S : Type w` with `[SmallCategory S]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the smallness universe `w` in
-- `EssentiallySmall` and `LocallySmall` would default to a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.EssentiallySmall** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- An essentially small category is equivalent to some small category. -/
  equiv_smallCategory : ∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)

/-- Constructor for `EssentiallySmall C` from an explicit small category witness. -/
/-
**CategoryTheory.EssentiallySmall.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
EssentiallySmall`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {S : Type w} [ins
t_1 : CategoryTheory.SmallCategory S]   (e : C ≌ S), CategoryTheory.EssentiallyS
mall.{w, v, u} C
参数：e : C ≌ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `EssentiallySmall C` from an explicit small category witness.
-/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩

/-- An arbitrarily chosen small model for an essentially small category.
-/
@[pp_with_univ]
/-
**CategoryTheory.SmallModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w
参数：C : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EssentiallySmall.equiv_smallCategory`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.EssentiallySmall.{w
, v, u} C],   ∃ S x, Nonempty (C ≌ S)

--- 原说明 ---
An arbitrarily chosen small model for an essentially small category.
-/
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)
/-
**CategoryTheory.smallCategorySmallModel** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：smallCategorySmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w
} C] : SmallCategory (SmallModel C)
参数：C : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EssentiallySmall.equiv_smallCategory`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.EssentiallySmall.{w
, v, u} C],   ∃ S x, Nonempty (C ≌ S)
-/
noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : SmallCategory (SmallModel C) :=
  Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))

/-- The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
/-
**CategoryTheory.equivSmallModel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : C
 ≌ SmallModel C
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    C ≌ SmallModel C :=
  Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : EssentiallySmall.{w} Cᵒᵖ :=
  EssentiallySmall.mk' (equivSmallModel C).op
/-
**CategoryTheory.essentiallySmall_congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Catego
ry.{v'} D] (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D
参数：e : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EssentiallySmall.mk'`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (
e : C ≌ S), CategoryTheor…
-/
theorem essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)
/-
**CategoryTheory.Discrete.essentiallySmallOfSmall** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Discrete`。
形式化陈述：∀ {α : Type u} [Small.{w, u} α], CategoryTheory.EssentiallySmall.{w, u, u}
 (CategoryTheory.Discrete α)
参数：CategoryTheory.Discrete α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩
/-
**CategoryTheory.essentiallySmallSelf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：essentiallySmallSelf : EssentiallySmall.{max w v u} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EssentiallySmall.mk'`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {S : Type w} [inst_1 : CategoryTheory.SmallCategory S]   (
e : C ≌ S), CategoryTheor…
-/
theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)

/-- A category is `w`-locally small if every hom set is `w`-small.

See `ShrinkHoms C` for a category instance where every hom set has been replaced by a small model.
-/
-- See comment on `EssentiallySmall` above.
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.LocallySmall** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：LocallySmall (C : Type u) [Category.{v} C] : Prop where /-- A locally smal
l category has small hom-types. -/ hom_small : forall X Y : C, Small.{w} (X ⟶ Y)
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- A locally small category has small hom-types. -/
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) := by infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small.{w, v} (X ⟶ Y) :=
  LocallySmall.hom_small X Y
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] : LocallySmall.{w} Cᵒᵖ where
  hom_small X Y := small_of_injective (opEquiv X Y).injective
/-
**CategoryTheory.locallySmall_of_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Cate
gory.{v'} D] (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C 
where hom_small {_ _}
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
-/
theorem locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C where
  hom_small {_ _} := small_of_injective F.map_injective
/-
**CategoryTheory.locallySmall_congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{
v'} D] (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D
参数：e : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
-/
theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] [LocallySmall.{w'} C] :
    LocallySmall.{w'} (SmallModel.{w} C) :=
  (locallySmall_congr (equivSmallModel.{w} C)).1 inferInstance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] :
    LocallySmall.{v} C where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) locallySmall_of_univLE (C : Type u) [Category.{v} C] [UnivLE.{v, w}] :
    LocallySmall.{w} C where
/-
**CategoryTheory.locallySmall_max** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C 
where hom_small _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `small_max`：small_max (α : Type v) : Small.{max w v} α
-/
theorem locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C where
  hom_small _ _ := small_max.{w} _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)

/-- We define a type alias `ShrinkHoms C` for `C`. When we have `LocallySmall.{w} C`,
we'll put a `Category.{w}` instance on `ShrinkHoms C`.
-/
@[pp_with_univ]
/-
**CategoryTheory.ShrinkHoms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：ShrinkHoms (C : Type u)
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define a type alias `ShrinkHoms C` for `C`. When we have `LocallySmall.{w} C`
,
we'll put a `Category.{w}` instance on `ShrinkHoms C`.
-/
def ShrinkHoms (C : Type u) :=
  C

namespace ShrinkHoms

section

variable {C' : Type*}

-- a fresh variable with no category instance attached
/-- Help the typechecker by explicitly translating from `C` to `ShrinkHoms C`. -/
/-
**CategoryTheory.ShrinkHoms.toShrinkHoms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShrinkHoms`。
形式化陈述：toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C'
参数：X : C'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by explicitly translating from `C` to `ShrinkHoms C`.
-/
def toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C' :=
  X

/-- Help the typechecker by explicitly translating from `ShrinkHoms C` to `C`. -/
/-
**CategoryTheory.ShrinkHoms.fromShrinkHoms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShrinkHoms`。
形式化陈述：fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C'
参数：X : ShrinkHoms C'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by explicitly translating from `ShrinkHoms C` to `C`.
-/
def fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C' :=
  X

@[simp]
/-
**CategoryTheory.ShrinkHoms.to_from** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sh
rinkHoms`。
形式化陈述：to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X
参数：X : C'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl

@[simp]
/-
**CategoryTheory.ShrinkHoms.from_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sh
rinkHoms`。
形式化陈述：from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X
参数：X : ShrinkHoms C'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl

end

variable [LocallySmall.{w} C]

@[simps]
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Category.{w} (ShrinkHoms C) where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
/-
**CategoryTheory.ShrinkHoms.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
rinkHoms`。
形式化陈述：functor : C ⥤ ShrinkHoms C where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)

--- 原说明 ---
Implementation of `ShrinkHoms.equivalence`.
-/
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj X := toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f

/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
/-
**CategoryTheory.ShrinkHoms.inverse** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
rinkHoms`。
形式化陈述：inverse : ShrinkHoms C ⥤ C where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Implementation of `ShrinkHoms.equivalence`.
-/
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj X := fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The categorical equivalence between `C` and `ShrinkHoms C`, when `C` is locally small.
-/
@[simps]
/-
**CategoryTheory.ShrinkHoms.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShrinkHoms`。
形式化陈述：equivalence : C ≌ ShrinkHoms C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical equivalence between `C` and `ShrinkHoms C`, when `C` is locally 
small.
-/
noncomputable def equivalence : C ≌ ShrinkHoms C where
  functor := functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor C).IsEquivalence := (equivalence C).isEquivalence_functor
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (inverse C).IsEquivalence := (equivalence C).isEquivalence_inverse
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Type u} [Unique T] : Unique (ShrinkHoms.{u} T) where
  default := ShrinkHoms.toShrinkHoms (default : T)
  uniq _ := congr_arg ShrinkHoms.fromShrinkHoms (Unique.uniq _ _)
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Type u} [Category.{v} T] [IsDiscrete T] : IsDiscrete (ShrinkHoms.{u} T) where
  subsingleton _ _ := { allEq _ _ := Shrink.ext (Subsingleton.elim _ _) }
  eq_of_hom f := IsDiscrete.eq_of_hom (C := T) ((equivShrink _).symm f)

end ShrinkHoms

namespace Shrink

/-
**CategoryTheory.Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Small.{w} C] : Category.{v} (Shrink.{w} C) :=
  inferInstanceAs (Category (InducedCategory _ (equivShrink C).symm))

/-- The categorical equivalence between `C` and `Shrink C`, when `C` is small. -/
/-
**CategoryTheory.Shrink.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
rink`。
形式化陈述：equivalence [Small.{w} C] : C ≌ Shrink.{w} C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The categorical equivalence between `C` and `Shrink C`, when `C` is small.
-/
noncomputable def equivalence [Small.{w} C] : C ≌ Shrink.{w} C :=
  (Equivalence.induced _).symm
/-
**CategoryTheory.Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w'} C] [LocallySmall.{w} C] :
    LocallySmall.{w} (Shrink.{w'} C) :=
  locallySmall_of_faithful.{w} (equivalence.{w'} C).inverse

end Shrink

/-- A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
/-
**CategoryTheory.essentiallySmall_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：essentiallySmall_iff (C : Type u) [Category.{v} C] : EssentiallySmall.{w} 
C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C
参数：C : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_essentiallySmall`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.EssentiallySmall.{w, v, u} C],
   CategoryTheory.LocallySmall.{w, v,…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Equivalence.inducedFunctorOfEquiv`：∀ {D : Type u₂} [inst 
: CategoryTheory.Category.{v₂, u₂} D] {C' : Type u_1} (e : C' ≃ D),   (CategoryT
heory.inducedFunctor ⇑e).IsEquivalence

--- 原说明 ---
A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is s
mall,
and it is locally small.
-/
theorem essentiallySmall_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C := by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEquiv.symm
    exact ⟨⟨InducedCategory _ (e'.trans e).symm, inferInstance,
      ⟨(ShrinkHoms.equivalence C).trans
      ((skeletonEquivalence (ShrinkHoms C)).symm.trans
      (inducedFunctor _).asEquivalence.symm)⟩⟩⟩
/-
**CategoryTheory.essentiallySmall_of_small_of_locallySmall** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory`。
形式化陈述：essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} 
C] : EssentiallySmall.{w} C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.essentiallySmall_iff`：essentiallySmall_iff (C : Type u) [
Category.{v} C] : EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall
.{w} C
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
-/
instance essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (C : Type w) [SmallCategory C] : EssentiallySmall.{w} C := inferInstance
/-
**CategoryTheory.small_skeleton_of_essentiallySmall** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory`。
形式化陈述：small_skeleton_of_essentiallySmall [h : EssentiallySmall.{w} C] : Small.{w
} (Skeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.essentiallySmall_iff`：essentiallySmall_iff (C : Type u) [
Category.{v} C] : EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall
.{w} C
-/
instance small_skeleton_of_essentiallySmall [h : EssentiallySmall.{w} C] : Small.{w} (Skeleton C) :=
  essentiallySmall_iff C |>.1 h |>.1

variable {C} in
/-
**CategoryTheory.essentiallySmall_of_fully_faithful** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：essentiallySmall_of_fully_faithful {D : Type u'} [Category.{v'} D] (F : C 
⥤ D) [F.Full] [F.Faithful] [EssentiallySmall.{w} D] : EssentiallySmall.{w} C
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.essentiallySmall_iff`：essentiallySmall_iff (C : Type u) [
Category.{v} C] : EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall
.{w} C
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用引理 `CategoryTheory.Functor.mapSkeleton_injective`：mapSkeleton_injective [F.F
ull] [F.Faithful] : Function.Injective F.mapSkeleton.obj
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
· 使用定理 `CategoryTheory.locallySmall_of_essentiallySmall`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.EssentiallySmall.{w, v, u} C],
   CategoryTheory.LocallySmall.{w, v,…
-/
theorem essentiallySmall_of_fully_faithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] [EssentiallySmall.{w} D] : EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_injective F.mapSkeleton_injective,
    locallySmall_of_faithful F⟩

section FullSubcategory

/-
**CategoryTheory.locallySmall_fullSubcategory** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory`。
形式化陈述：locallySmall_fullSubcategory [LocallySmall.{w} C] (P : ObjectProperty C) :
 LocallySmall.{w} P.FullSubcategory
参数：P : ObjectProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
-/
instance locallySmall_fullSubcategory [LocallySmall.{w} C] (P : ObjectProperty C) :
    LocallySmall.{w} P.FullSubcategory :=
  locallySmall_of_faithful <| P.ι
/-
**CategoryTheory.essentiallySmall_fullSubcategory_mem** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory`。
形式化陈述：essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySma
ll.{w} C] : EssentiallySmall.{w} (ObjectProperty.FullSubcategory (· in s))
参数：s : Set C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.ext`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {x y
 : P.FullSubcategory}, x.obj = y.obj → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySmall.{w} C] :
    EssentiallySmall.{w} (ObjectProperty.FullSubcategory (· ∈ s)) :=
  suffices Small.{w} (ObjectProperty.FullSubcategory (· ∈ s)) from
    essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by cat_disch)

end FullSubcategory

/-- Any thin category is locally small.
-/
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any thin category is locally small.
-/
instance (priority := 100) locallySmall_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    LocallySmall.{w} C where

/--
A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
/-
**CategoryTheory.essentiallySmall_iff_of_thin** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin 
C] : EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A thin category is essentially small if and only if the underlying type of its s
keleton is small.
-/
theorem essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] : Small.{w} (Discrete C) := small_map discreteEquiv
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] [LocallySmall.{w} C] :
    Small.{w} (Arrow C) := by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by simpa using h
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} C] [LocallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [Small.{w} D] [LocallySmall.{w} D] :
    Small.{w} (C ⥤ D) := by
  refine small_of_injective (f := fun F (f : Arrow C) ↦ Arrow.mk (F.map f.hom))
    (fun F G h ↦ Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arrow.mk_eq_mk_iff] at this
    tauto
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type u'} [Category.{v'} A] [LocallySmall.{w} A] (C : Type w) [SmallCategory C] :
    LocallySmall.{w} (C ⥤ A) where
  hom_small P Q :=
    small_of_injective (f := NatTrans.app) (fun f g h ↦ by aesop)

end CategoryTheory

