/-
Copyright (c) 2026 John Rozmarynowycz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rozmarynowycz
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Functors of submonoids

Given a functor `M : C ⥤ MonCat`, we define a functor of submonoids `S` to be a
family `Submonoid (M.obj U)` for all `U : C` that are compatible with the maps induced by `M`.

We provide the complete lattice structure and the basic functoriality properties.

## TODO

- Show the Galois connection between `SubmonoidFunctor.image` and `SubmonoidFunctor.comap`
  and provide the related API.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {M : C ⥤ MonCat.{w}}

variable (M) in
/-- A submonoid functor consists of a submonoid of `M.obj U` for every `U`,
compatible with the restriction maps `M.map i`. -/
@[ext]
/-
**CategoryTheory.SubmonoidFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：SubmonoidFunctor where /-- A submonoid of `M.obj U` for all `U : C`. -/ ob
j (U : C) : Submonoid (M.obj U) /-- For any `i : U ⟶ V`, `M.map i` maps the subm
onoid `obj U` into the submonoid `obj V`. -/ map {U V : C} (i : U ⟶ V) : obj U <
= (obj V).comap (M.map i).hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid functor consists of a submonoid of `M.obj U` for every `U`,
compatible with the restriction maps `M.map i`.
-/
structure SubmonoidFunctor where
  /-- A submonoid of `M.obj U` for all `U : C`. -/
  obj (U : C) : Submonoid (M.obj U)
  /-- For any `i : U ⟶ V`, `M.map i` maps the submonoid `obj U` into the submonoid `obj V`. -/
  map {U V : C} (i : U ⟶ V) : obj U ≤ (obj V).comap (M.map i).hom := by cat_disch

namespace SubmonoidFunctor

variable (S : SubmonoidFunctor M)

/-
**CategoryTheory.SubmonoidFunctor.map_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.SubmonoidFunctor`。
形式化陈述：map_le {U V : C} (f : U ⟶ V) : (S.obj U).map (M.map f).hom <= S.obj V
参数：f : U ⟶ V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {S : Submonoi
d M} {T : Submonoid N} : S.map f <= T ↔ S <= T.comap f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `CategoryTheory.SubmonoidFunctor.map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {M : CategoryTheory.Functor C MonCat}   (self : CategoryTh
eory.SubmonoidFunctor M) …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma map_le {U V : C} (f : U ⟶ V) : (S.obj U).map (M.map f).hom ≤ S.obj V := by
  grw [Submonoid.map_le_iff_le_comap, S.map f]

/-- The functor of monoids associated to a functor of submonoids. -/
@[simps obj map]
/-
**CategoryTheory.SubmonoidFunctor.toFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.SubmonoidFunctor`。
形式化陈述：toFunctor : C ⥤ MonCat.{w} where obj _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SubmonoidFunctor.map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {M : CategoryTheory.Functor C MonCat}   (self : CategoryTh
eory.SubmonoidFunctor M) …

--- 原说明 ---
The functor of monoids associated to a functor of submonoids.
-/
def toFunctor : C ⥤ MonCat.{w} where
  obj _ := MonCat.of (S.obj _)
  map i :=
    MonCat.ofHom <| ((M.map i).hom.submonoidComap (S.obj _)).comp <| Submonoid.inclusion (S.map i)

/-- The subfunctor associated to a functor of submonoids. -/
@[simps obj]
/-
**CategoryTheory.SubmonoidFunctor.toSubfunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.SubmonoidFunctor`。
形式化陈述：toSubfunctor : Subfunctor (M ⋙ forget MonCat) where obj _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SubmonoidFunctor.map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {M : CategoryTheory.Functor C MonCat}   (self : CategoryTh
eory.SubmonoidFunctor M) …

--- 原说明 ---
The subfunctor associated to a functor of submonoids.
-/
def toSubfunctor : Subfunctor (M ⋙ forget MonCat) where
  obj _ := (S.obj _).carrier
  map := S.map

variable {M M' M'' : C ⥤ MonCat.{w}} (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')
/-
**CategoryTheory.SubmonoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sub
monoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U : C} : CoeHead (S.toFunctor.obj U) (M.obj U) where
  coe := Subtype.val
/-
**CategoryTheory.SubmonoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sub
monoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (SubmonoidFunctor M) :=
  PartialOrder.lift SubmonoidFunctor.obj fun _ _ => SubmonoidFunctor.ext

@[simps! top_obj bot_obj sup_obj inf_obj sInf_obj sSup_obj]
/-
**CategoryTheory.SubmonoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sub
monoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (SubmonoidFunctor M) where
  sup F G :=
    { obj _ := F.obj _ ⊔ G.obj _
      map i := by grw [F.map i, G.map i, (Submonoid.monotone_comap).le_map_sup] }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by simp [h₁ U, h₂ U]
  inf S T :=
    { obj _ := S.obj _ ⊓ T.obj _
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩ }
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj _ := ⨆ F ∈ S, F.obj _
      map {U V} f := by
        grw [← Submonoid.monotone_comap.le_map_iSup₂]
        exact iSup₂_mono fun F _ ↦ F.map f }
  isLUB_sSup _ := ⟨fun a ha U ↦ le_iSup₂_of_le a ha le_rfl, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj _ := ⨅ F ∈ S, F.obj _
      map f := by
        rw [(Submonoid.gc_map_comap (M.map f).hom).u_iInf₂]
        exact iInf₂_mono fun F _ ↦ F.map f }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot := { obj _ := ⊥ }
  bot_le _ _ := bot_le
  top := { obj _ := ⊤ }
  le_top _ _ := le_top

/-- The inclusion of a submonoid functor `S` to the original functor of monoids `M`. -/
@[simps]
/-
**CategoryTheory.SubmonoidFunctor.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
monoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a submonoid functor `S` to the original functor of monoids `M`.
-/
def ι : S.toFunctor ⟶ M where
  app _ := MonCat.ofHom (Submonoid.subtype _)
/-
**CategoryTheory.SubmonoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sub
monoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono S.ι := by
  suffices ∀ (X : C), Mono (S.ι.app X) from NatTrans.mono_of_mono_app _
  intro X
  exact ConcreteCategory.mono_of_injective _ Subtype.val_injective

section image

variable (p : M ⟶ M')

/-- The submonoid functor defined by the image along a morphism of functors of monoids. -/
@[simps]
/-
**CategoryTheory.SubmonoidFunctor.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SubmonoidFunctor`。
形式化陈述：image (S : SubmonoidFunctor M) : SubmonoidFunctor M' where obj _
参数：S : SubmonoidFunctor M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid functor defined by the image along a morphism of functors of monoi
ds.
-/
def image (S : SubmonoidFunctor M) : SubmonoidFunctor M' where
  obj _ := Submonoid.map (MonCat.Hom.hom (p.app _)) (S.obj _)
  map i := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_map, ← MonCat.hom_comp, ← p.naturality,
      MonCat.hom_comp, ← Submonoid.map_map]
    grw [S.map_le]

variable (M) in
@[simp]
/-
**CategoryTheory.SubmonoidFunctor.image_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.SubmonoidFunctor`。
形式化陈述：image_id : image (𝟙 M) ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SubmonoidFunctor.ext`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} {M : CategoryTheory.Functor C MonCat}   {x y : CategoryThe
ory.SubmonoidFunctor M}, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SubmonoidFunctor.image_obj`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {M M' : CategoryTheory.Functor C MonCat} (p : M ⟶ M'
)   (S : CategoryTheory.Submono…
· 使用定理 `Submonoid.map_id`：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_id : image (𝟙 M) ⊤ = ⊤ := by aesop

@[simp]
/-
**CategoryTheory.SubmonoidFunctor.image_comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.SubmonoidFunctor`。
形式化陈述：image_comp (p' : M' ⟶ M'') : S.image (p ≫ p') = (S.image p).image p'
参数：p' : M' ⟶ M''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SubmonoidFunctor.ext`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} {M : CategoryTheory.Functor C MonCat}   {x y : CategoryThe
ory.SubmonoidFunctor M}, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SubmonoidFunctor.image_obj`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {M M' : CategoryTheory.Functor C MonCat} (p : M ⟶ M'
)   (S : CategoryTheory.Submono…
· 使用定理 `Submonoid.map.congr_simp`：∀ {M : Type u_1} {N : Type u_2} [inst : MulOne
Class M] [inst_1 : MulOneClass N] {F : Type u_4} [inst_2 : FunLike F M N]   [mc 
: MonoidHomCla…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_comp (p' : M' ⟶ M'') : S.image (p ≫ p') = (S.image p).image p' := by cat_disch

end image

section comap

variable (p : M ⟶ M') (S'' : SubmonoidFunctor M'')

/-- The submonoid functor defined by the preimage along a morphism of functors of monoids. -/
@[simps]
/-
**CategoryTheory.SubmonoidFunctor.comap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SubmonoidFunctor`。
形式化陈述：comap (S' : SubmonoidFunctor M') : SubmonoidFunctor M where obj _
参数：S' : SubmonoidFunctor M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid functor defined by the preimage along a morphism of functors of mo
noids.
-/
def comap (S' : SubmonoidFunctor M') : SubmonoidFunctor M where
  obj _ := Submonoid.comap (MonCat.Hom.hom (p.app _)) (S'.obj _)
  map _ _ h := by
    simp_rw [Submonoid.mem_comap, NatTrans.naturality_apply]
    exact Submonoid.mem_comap.mp (Set.mem_of_mem_of_subset h (S'.map _))

variable (M) in
@[simp]
/-
**CategoryTheory.SubmonoidFunctor.comap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.SubmonoidFunctor`。
形式化陈述：comap_id : comap (𝟙 M) ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_id : comap (𝟙 M) ⊤ = ⊤ := rfl

@[simp]
/-
**CategoryTheory.SubmonoidFunctor.comap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.SubmonoidFunctor`。
形式化陈述：comap_comp (p' : M' ⟶ M'') : S''.comap (p ≫ p') = (S''.comap p').comap p
参数：p' : M' ⟶ M''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comp (p' : M' ⟶ M'') : S''.comap (p ≫ p') = (S''.comap p').comap p := by rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.SubmonoidFunctor.image_comap_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.SubmonoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_comap_ι : image S.ι (comap S.ι S) = S := by aesop

end comap

section lift

variable (p : M ⟶ M') (S : SubmonoidFunctor M) (S' : SubmonoidFunctor M')
  (hp : image p ⊤ ≤ S')

set_option backward.defeqAttrib.useBackward true in
/-- If the image of morphism `M' ⟶ M` lands in a submonoid functor `S`,
then the morphism factors through it. -/
@[simps! app]
/-
**CategoryTheory.SubmonoidFunctor.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.SubmonoidFunctor`。
形式化陈述：lift : M ⟶ S'.toFunctor where app U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the image of morphism `M' ⟶ M` lands in a submonoid functor `S`,
then the morphism factors through it.
-/
def lift : M ⟶ S'.toFunctor where
  app U := MonCat.ofHom <| MonoidHom.codRestrict (p.app U).hom _ fun x ↦ hp _ (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.SubmonoidFunctor.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.SubmonoidFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι : lift p S' hp ≫ S'.ι = p := rfl

end lift

end SubmonoidFunctor

end CategoryTheory

