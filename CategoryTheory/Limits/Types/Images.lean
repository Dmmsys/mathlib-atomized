/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images in the category of types

In this file, it is shown that the category of types has categorical images,
and that these agree with the range of a function.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits.Types

variable {α β : Type u} (f : α ⟶ β)

section

-- implementation of `HasImage`
/-- the image of a morphism in Type is just `Set.range f` -/
/-
**CategoryTheory.Limits.Types.Image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Types`。
形式化陈述：Image : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the image of a morphism in Type is just `Set.range f`
-/
def Image : Type u :=
  Set.range f
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩

/-- the inclusion of `Image f` into the target -/
/-
**CategoryTheory.Limits.Types.Image.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the inclusion of `Image f` into the target
-/
def Image.ι : Image f ⟶ β :=
  ↾(Subtype.val)
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective

variable {f}

/-- the universal property for the image factorisation -/
/-
**CategoryTheory.Limits.Types.Image.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Types.Image`。
形式化陈述：{α β : Type u} →   {f : α ⟶ β} → (F' : CategoryTheory.Limits.MonoFactorisa
tion f) → CategoryTheory.Limits.Types.Image f ⟶ F'.I
参数：F' : CategoryTheory.Limits.MonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the universal property for the image factorisation
-/
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  ↾fun x => F'.e (Classical.indefiniteDescription _ x.2).1
/-
**CategoryTheory.Limits.Types.Image.lift_fac** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Types.Image`。
形式化陈述：∀ {α β : Type u} {f : α ⟶ β} (F' : CategoryTheory.Limits.MonoFactorisation
 f),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Types.Image.lif
t F') F'.m =     CategoryTheory.Limits.Types.Image.ι f
参数：F' : CategoryTheory.Limits.MonoFactorisation f；CategoryTheory.Limits.Types.Im
age.lift F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

/-- the factorisation of any morphism in Type through a mono. -/
/-
**CategoryTheory.Limits.Types.monoFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Types`。
形式化陈述：monoFactorisation : MonoFactorisation f where I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.instMonoImageι`：∀ {α β : Type u} (f : α ⟶ β)
, CategoryTheory.Mono (CategoryTheory.Limits.Types.Image.ι f)

--- 原说明 ---
the factorisation of any morphism in Type through a mono.
-/
def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := ↾(Set.rangeFactorization f)

/-- the factorisation through a mono has the universal property of the image. -/
/-
**CategoryTheory.Limits.Types.isImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Types`。
形式化陈述：isImage : IsImage (monoFactorisation f) where lift
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.Image.lift_fac`：∀ {α β : Type u} {f : α ⟶ β}
 (F' : CategoryTheory.Limits.MonoFactorisation f),   CategoryTheory.CategoryStru
ct.comp (CategoryTheory.Limits.T…

--- 原说明 ---
the factorisation through a mono has the universal property of the image.
-/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasImages (Type u) where
  has_image := by infer_instance
/-
**CategoryTheory.Limits.Types.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.
Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasImageMaps (Type u) where
  has_image_map {f g} st :=
    HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (↾fun x => ⟨st.right x.val, ⟨st.left (Classical.choose x.2), by
        rw [elementwise_of% st.w]
        rw [Classical.choose_spec x.property]⟩⟩) rfl

variable {F : ℕᵒᵖ ⥤ Type u} {c : Cone F}
  (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
/-
**CategoryTheory.Limits.Types.limitOfSurjectionsSurjective.preimage** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def limitOfSurjectionsSurjective.preimage
    (a : F.obj ⟨0⟩) : (n : ℕ) → F.obj ⟨n⟩
    | 0 => a
    | n + 1 => (hF n (preimage a n)).choose

include hF in
open limitOfSurjectionsSurjective in
/-- Auxiliary lemma. Use `limit_of_surjections_surjective` instead. -/
/-
**CategoryTheory.Limits.Types.surjective_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma. Use `limit_of_surjections_surjective` instead.
-/
lemma surjective_π_app_zero_of_surjective_map_aux :
    Function.Surjective ((limitCone F).π.app ⟨0⟩) := by
  intro a
  refine ⟨⟨fun ⟨n⟩ ↦ preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m ≤ n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m ≤ p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.le_succ p)).op) (g := (homOfLE h').op),
      comp_apply, (hF p _).choose_spec]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`, the projection map `lim Xₙ ⟶ X₀` is surjective.
-/
/-
**CategoryTheory.Limits.Types.surjective_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits.Types`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given surjections `⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`, the projection map `lim Xₙ ⟶ X₀` is 
surjective.
-/
lemma surjective_π_app_zero_of_surjective_map
    (hc : IsLimit c)
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]; rfl
  rw [this, types_comp]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_instance

end CategoryTheory.Limits.Types

