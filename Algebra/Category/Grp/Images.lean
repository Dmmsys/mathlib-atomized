/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of commutative additive groups has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `AddCommGrpCat` is an abelian category.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AddCommGrpCat

-- Note that because `injective_of_mono` is currently only proved in `Type 0`,
-- we restrict to the lowest universe here for now.
variable {G H : AddCommGrpCat.{0}} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `IsImage` for `AddCommGrpCat`; use the API, not these
/-- the image of a morphism in `AddCommGrpCat` is just the bundling of `AddMonoidHom.range f` -/
/-
**AddCommGrpCat.image** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：image : AddCommGrpCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the image of a morphism in `AddCommGrpCat` is just the bundling of `AddMonoidHom
.range f`
-/
def image : AddCommGrpCat :=
  AddCommGrpCat.of (AddMonoidHom.range f.hom)

/-- the inclusion of `image f` into the target -/
/-
**AddCommGrpCat.image.** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the inclusion of `image f` into the target
-/
def image.ι : image f ⟶ H :=
  ofHom f.hom.range.subtype
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- the corestriction map to the image -/
/-
**AddCommGrpCat.factorThruImage** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：factorThruImage : G ⟶ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the corestriction map to the image
-/
def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict
/-
**AddCommGrpCat.image.fac** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat.image`。
形式化陈述：∀ {G H : AddCommGrpCat} (f : G ⟶ H),   CategoryTheory.CategoryStruct.comp 
(AddCommGrpCat.factorThruImage f) (AddCommGrpCat.image.ι f) = f
参数：f : G ⟶ H；AddCommGrpCat.factorThruImage f；AddCommGrpCat.image.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f := by
  ext
  rfl

attribute [local simp] image.fac

variable {f}

set_option backward.isDefEq.respectTransparency.types false in
/-- the universal property for the image factorisation -/
/-
**AddCommGrpCat.image.lift** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.image`。
形式化陈述：{G H : AddCommGrpCat} → {f : G ⟶ H} → (F' : CategoryTheory.Limits.MonoFact
orisation f) → AddCommGrpCat.image f ⟶ F'.I
参数：F' : CategoryTheory.Limits.MonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the universal property for the image factorisation
-/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
    map_zero' := by
      have := F'.m_mono
      apply injective_of_mono F'.m
      change (F'.e ≫ F'.m) _ = _
      rw [F'.fac, map_zero]
      exact (Classical.indefiniteDescription (fun y => f y = 0) _).2
    map_add' := by
      intro x y
      have := F'.m_mono
      apply injective_of_mono F'.m
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      rw [F'.fac]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
      rw [(Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddCommGrpCat.image.lift_fac** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat.image`。
形式化陈述：∀ {G H : AddCommGrpCat} {f : G ⟶ H} (F' : CategoryTheory.Limits.MonoFactor
isation f),   CategoryTheory.CategoryStruct.comp (AddCommGrpCat.image.lift F') F
'.m = AddCommGrpCat.image.ι f
参数：F' : CategoryTheory.Limits.MonoFactorisation f；AddCommGrpCat.image.lift F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in `AddCommGrpCat` through a mono. -/
/-
**AddCommGrpCat.monoFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：monoFactorisation : MonoFactorisation f where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.instMonoι`：∀ {G H : AddCommGrpCat} (f : G ⟶ H), CategoryTh
eory.Mono (AddCommGrpCat.image.ι f)

--- 原说明 ---
the factorisation of any morphism in `AddCommGrpCat` through a mono.
-/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

/-- the factorisation of any morphism in `AddCommGrpCat` through a mono has
the universal property of the image. -/
/-
**AddCommGrpCat.isImage** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：isImage : IsImage (monoFactorisation f) where lift
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.image.lift_fac`：∀ {G H : AddCommGrpCat} {f : G ⟶ H} (F' : 
CategoryTheory.Limits.MonoFactorisation f),   CategoryTheory.CategoryStruct.comp
 (AddCommGrpCat.im…

--- 原说明 ---
the factorisation of any morphism in `AddCommGrpCat` through a mono has
the universal property of the image.
-/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

/-- The categorical image of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical range.
-/
/-
**AddCommGrpCat.imageIsoRange** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：imageIsoRange {G H : AddCommGrpCat.{0}} (f : G ⟶ H) : Limits.image f ≅ Add
CommGrpCat.of f.hom.range
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical image of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical range.
-/
noncomputable def imageIsoRange {G H : AddCommGrpCat.{0}} (f : G ⟶ H) :
    Limits.image f ≅ AddCommGrpCat.of f.hom.range :=
  IsImage.isoExt (Image.isImage f) (isImage f)

end AddCommGrpCat

