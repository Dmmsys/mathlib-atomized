/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Objects that are local with respect to a property of morphisms

Given `W : MorphismProperty C`, we define `W.isLocal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `Mathlib/CategoryTheory/Localization/Bousfield.lean`, it is shown that this is
part of a Galois connection, with "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.)

We also introduce the dual notion `W.isColocal : ObjectProperty C`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W W' : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is the property of `W`-local objects, i.e.
the objects `Z` such that for any `f : X ⟶ Y` such that `W f` holds, the precomposition
with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.) -/
/-
**CategoryTheory.MorphismProperty.isLocal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MorphismProperty`。
形式化陈述：isLocal : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C`, this is the property of `W`-local objects, i.e.
the objects `Z` such that for any `f : X ⟶ Y` such that `W f` holds, the precomp
osition
with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual
" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.)
-/
def isLocal : ObjectProperty C :=
  fun Z ↦ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)
/-
**CategoryTheory.MorphismProperty.isLocal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：isLocal_iff (Z : C) : W.isLocal Z ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> F
unction.Bijective (fun (g : _ ⟶ Z) => f ≫ g)
参数：Z : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocal_iff (Z : C) :
    W.isLocal Z ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g) := Iff.rfl

/-- Given `W : MorphismProperty C`, this is the property of `W`-colocal objects, i.e.
the objects `X` such that for any `g : Y ⟶ Z` such that `W g` holds, the postcomposition
with `g` gives a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual" construction
`ObjectProperty.isColocal : ObjectProperty C → MorphismProperty C`.) -/
/-
**CategoryTheory.MorphismProperty.isColocal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：isColocal : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C`, this is the property of `W`-colocal objects, i.e
.
the objects `X` such that for any `g : Y ⟶ Z` such that `W g` holds, the postcom
position
with `g` gives a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual
" construction
`ObjectProperty.isColocal : ObjectProperty C → MorphismProperty C`.)
-/
def isColocal : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g → Function.Bijective (fun (f : X ⟶ _) ↦ f ≫ g)
/-
**CategoryTheory.MorphismProperty.isColocal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.MorphismProperty`。
形式化陈述：isColocal_iff (X : C) : W.isColocal X ↔ forall ⦃Y Z : C⦄ (g : Y ⟶ Z), W g 
-> Function.Bijective (fun (f : X ⟶ Y) => f ≫ g)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isColocal_iff (X : C) :
    W.isColocal X ↔ ∀ ⦃Y Z : C⦄ (g : Y ⟶ Z),
      W g → Function.Bijective (fun (f : X ⟶ Y) ↦ f ≫ g) := Iff.rfl
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.isLocal.IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e hZ X Y f hf := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert! (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.isColocal.IsClosedUnderIsomorphisms where
  of_iso {X X'} e hX Y Z g hg := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homFromEquiv e).bijective]
    convert! (Iso.homFromEquiv e).bijective.comp (hX g hg) using 1
    aesop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type u') [Category.{v'} J] :
    W.isLocal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun Z ⟨p⟩ X Y f hf ↦ by
    refine ⟨fun g₁ g₂ h ↦ p.isLimit.hom_ext
      (fun j ↦ (p.prop_diag_obj j f hf).1 (by simp [reassoc_of% h])), fun g ↦ ?_⟩
    choose app h using fun j ↦ (p.prop_diag_obj j f hf).2 (g ≫ p.π.app j)
    exact ⟨p.isLimit.lift (Cone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ f hf).1
          (by simp [reassoc_of% h, h, p.w a]) }),
      p.isLimit.hom_ext (fun j ↦ by simp [p.isLimit.fac, h])⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type u') [Category.{v'} J] :
    W.isColocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun X ⟨p⟩ Y Z g hg ↦ by
    refine ⟨fun f₁ f₂ h ↦ p.isColimit.hom_ext
      (fun j ↦ (p.prop_diag_obj j g hg).1 (by simp [h])), fun f ↦ ?_⟩
    choose app h using fun j ↦ (p.prop_diag_obj j g hg).2 (p.ι.app j ≫ f)
    exact ⟨p.isColimit.desc (Cocone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ g hg).1
          (by simp [h]) }),
      p.isColimit.hom_ext (fun j ↦ by simp [p.isColimit.fac_assoc, h])⟩

variable {W W'} in
attribute [local simp] isLocal_iff in
/-
**CategoryTheory.MorphismProperty.isLocal_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MorphismProperty`。
形式化陈述：isLocal_antitone (h : W <= W') : W'.isLocal <= W.isLocal
参数：h : W <= W'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLocal_antitone (h : W ≤ W') :
    W'.isLocal ≤ W.isLocal := by
  intro f hf
  aesop

variable {W W'} in
attribute [local simp] isColocal_iff in
/-
**CategoryTheory.MorphismProperty.isColocal_antitone** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：isColocal_antitone (h : W <= W') : W'.isColocal <= W.isColocal
参数：h : W <= W'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isColocal_antitone (h : W ≤ W') :
    W'.isColocal ≤ W.isColocal := by
  intro f hf
  aesop

attribute [local simp] isLocal_iff in
@[simp]
/-
**CategoryTheory.MorphismProperty.isLocal_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：isLocal_iSup {ι : Sort*} (W : ι -> MorphismProperty C) : (⨆ (i : ι), W i).
isLocal = ⨅ (i : ι), (W i).isLocal
参数：W : ι -> MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
-/
lemma isLocal_iSup {ι : Sort*} (W : ι → MorphismProperty C) :
    (⨆ (i : ι), W i).isLocal = ⨅ (i : ι), (W i).isLocal := by
  aesop

attribute [local simp] isColocal_iff in
@[simp]
/-
**CategoryTheory.MorphismProperty.isColocal_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：isColocal_iSup {ι : Sort*} (W : ι -> MorphismProperty C) : (⨆ (i : ι), W i
).isColocal = ⨅ (i : ι), (W i).isColocal
参数：W : ι -> MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
-/
lemma isColocal_iSup {ι : Sort*} (W : ι → MorphismProperty C) :
    (⨆ (i : ι), W i).isColocal = ⨅ (i : ι), (W i).isColocal := by
  aesop
/-
**CategoryTheory.MorphismProperty.isLocal_single_iff_bijective** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isLocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) : (MorphismProp
erty.single f).isLocal Z ↔ (Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g))
参数：f : X ⟶ Y；Z : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma isLocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) :
    (MorphismProperty.single f).isLocal Z ↔
      (Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)) :=
  ⟨fun h ↦ h _ ⟨⟨⟩⟩, fun h ↦ by rintro _ _ _ ⟨_⟩; exact h⟩
/-
**CategoryTheory.MorphismProperty.isColocal_single_iff_bijective** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isColocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) : (MorphismPr
operty.single f).isColocal Z ↔ (Function.Bijective (fun (g : Z ⟶ _) => g ≫ f))
参数：f : X ⟶ Y；Z : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma isColocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) :
    (MorphismProperty.single f).isColocal Z ↔
      (Function.Bijective (fun (g : Z ⟶ _) ↦ g ≫ f)) :=
  ⟨fun h ↦ h _ ⟨⟨⟩⟩, fun h ↦ by rintro _ _ _ ⟨_⟩; exact h⟩

end MorphismProperty

end CategoryTheory

