/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# The category of R-modules has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `ModuleCat R` is an abelian category.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

attribute [local ext] Subtype.ext

section

-- implementation details of `HasImage` for ModuleCat; use the API, not these
/-- The image of a morphism in `ModuleCat R` is just the bundling of `LinearMap.range f` -/
/-
**ModuleCat.image** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：image : ModuleCat R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a morphism in `ModuleCat R` is just the bundling of `LinearMap.rang
e f`
-/
def image : ModuleCat R :=
  ModuleCat.of R (LinearMap.range f.hom)

/-- The inclusion of `image f` into the target -/
/-
**ModuleCat.image.** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `image f` into the target
-/
def image.ι : image f ⟶ H :=
  ofHom (LinearMap.range f.hom).subtype
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (image.ι f) :=
  ConcreteCategory.mono_of_injective (image.ι f) Subtype.val_injective

/-- The corestriction map to the image -/
/-
**ModuleCat.factorThruImage** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：factorThruImage : G ⟶ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The corestriction map to the image
-/
def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict
/-
**ModuleCat.image.fac** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.image`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {G H : ModuleCat R} (f : G ⟶ H),   Category
Theory.CategoryStruct.comp (ModuleCat.factorThruImage f) (ModuleCat.image.ι f) =
 f
参数：f : G ⟶ H；ModuleCat.factorThruImage f；ModuleCat.image.ι f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  rfl

attribute [local simp] image.fac

variable {f}

set_option backward.isDefEq.respectTransparency.types false in
/-- The universal property for the image factorisation -/
/-
**ModuleCat.image.lift** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.image`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {G H : ModuleCat R} → {f : G ⟶ H} →
 (F' : CategoryTheory.Limits.MonoFactorisation f) → ModuleCat.image f ⟶ F'.I
参数：F' : CategoryTheory.Limits.MonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property for the image factorisation
-/
noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

set_option backward.isDefEq.respectTransparency.types false in
/-
**ModuleCat.image.lift_fac** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.image`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {G H : ModuleCat R} {f : G ⟶ H} (F' : Categ
oryTheory.Limits.MonoFactorisation f),   CategoryTheory.CategoryStruct.comp (Mod
uleCat.image.lift F') F'.m = ModuleCat.image.ι f
参数：F' : CategoryTheory.Limits.MonoFactorisation f；ModuleCat.image.lift F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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

/-- The factorisation of any morphism in `ModuleCat R` through a mono. -/
/-
**ModuleCat.monoFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：monoFactorisation : MonoFactorisation f where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.instMonoι`：∀ {R : Type u} [inst : Ring R] {G H : ModuleCat R} 
(f : G ⟶ H), CategoryTheory.Mono (ModuleCat.image.ι f)

--- 原说明 ---
The factorisation of any morphism in `ModuleCat R` through a mono.
-/
def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

/-- The factorisation of any morphism in `ModuleCat R` through a mono has the universal property of
the image. -/
/-
**ModuleCat.isImage** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：isImage : IsImage (monoFactorisation f) where lift
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.image.lift_fac`：∀ {R : Type u} [inst : Ring R] {G H : ModuleCa
t R} {f : G ⟶ H} (F' : CategoryTheory.Limits.MonoFactorisation f),   CategoryThe
ory.CategorySt…

--- 原说明 ---
The factorisation of any morphism in `ModuleCat R` through a mono has the univer
sal property of
the image.
-/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

/-- The categorical image of a morphism in `ModuleCat R` agrees with the linear algebraic range. -/
/-
**ModuleCat.imageIsoRange** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) : Limits.image f ≅ Modul
eCat.of R (LinearMap.range f.hom)
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical image of a morphism in `ModuleCat R` agrees with the linear alge
braic range.
-/
noncomputable def imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f.hom) :=
  IsImage.isoExt (Image.isImage f) (isImage f)

@[simp, reassoc, elementwise]
/-
**ModuleCat.imageIsoRange_inv_image_** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageIsoRange_inv_image_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCat.ofHom (LinearMap.range f.hom).subtype :=
  IsImage.isoExt_inv_m _ _

@[simp, reassoc, elementwise]
/-
**ModuleCat.imageIsoRange_hom_subtype** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) : (imageIsoR
ange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f
参数：f : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.imageIsoRange_inv_image_ι`：imageIsoRange_inv_image_ι {G H : Mo
duleCat.{v} R} (f : G ⟶ H) : (imageIsoRange f).inv ≫ Limits.image.ι f = ModuleCa
t.ofHom (LinearMap.range …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem imageIsoRange_hom_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (imageIsoRange f).hom ≫ ModuleCat.ofHom (LinearMap.range f.hom).subtype = Limits.image.ι f := by
  rw [← imageIsoRange_inv_image_ι f, Iso.hom_inv_id_assoc]

end ModuleCat

