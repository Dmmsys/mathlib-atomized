/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Localization

/-!
# Locally bijective morphisms of presheaves

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `A` be a concrete category.
In this file, we introduce a type class `J.WEqualsLocallyBijective A` which says
that the class `J.W` (of morphisms of presheaves which become isomorphisms
after sheafification) is the class of morphisms that are both locally injective
and locally surjective (i.e. locally bijective). We prove that this holds iff
for any presheaf `P : Cᵒᵖ ⥤ A`, the sheafification map `toSheafify J P` is locally bijective.
We show that this holds under certain universe assumptions.

-/

public section

universe w' w v' v u' u
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]


namespace Sheaf

section

variable {F G : Sheaf J (Type w)} (f : F ⟶ G)

/-- A morphism of sheaves of types is locally bijective iff it is an isomorphism.
(This is generalized below as `isLocallyBijective_iff_isIso`.) -/
/-
**CategoryTheory.Sheaf.isLocallyBijective_iff_isIso'** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of sheaves of types is locally bijective iff it is an isomorphism.
(This is generalized below as `isLocallyBijective_iff_isIso`.)
-/
private lemma isLocallyBijective_iff_isIso' :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨h₁, _⟩
    rw [isLocallyInjective_iff_injective] at h₁
    suffices ∀ (X : Cᵒᵖ), Function.Surjective (f.hom.app X) by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
      intro X
      rw [isIso_iff_bijective]
      exact ⟨h₁ X, this X⟩
    intro X s
    have H := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _
      (Presheaf.imageSieve_mem J f.hom s)
    let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
      fun Y g hg => Presheaf.localPreimage f.hom s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply h₁
      have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
      have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
      have eq₄ := congr_arg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨H.amalgamate t ht, ?_⟩
    · apply (((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property).isSeparated _
        (Presheaf.imageSieve_mem J f.hom s)).ext
      intro Y g hg
      rw [← NatTrans.naturality_apply, H.valid_glue ht]
      exact Presheaf.app_localPreimage f.hom s g hg
  · intro
    constructor <;> infer_instance

end

section

variable {F G : Sheaf J A} (f : F ⟶ G) [(forget A).ReflectsIsomorphisms]
  [J.HasSheafCompose (forget A)]

/-
**CategoryTheory.Sheaf.isLocallyBijective_iff_isIso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Sheaf`。
形式化陈述：isLocallyBijective_iff_isIso : IsLocallyInjective f ∧ IsLocallySurjective 
f ↔ IsIso f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.instReflectsIsomorphismsSheafSheafCompose`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.LocallyBijective.0.CategoryTheory.
Sheaf.isLocallyBijective_iff_isIso'`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F G : CategoryTheor
y.Sheaf J (Type w…
· 使用定理 `CategoryTheory.Sheaf.isLocallyInjective_forget`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category
.{v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `CategoryTheory.Sheaf.instIsLocallySurjectiveFunMapTypeSheafComposeForget
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.G
rothendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Sheaf.isLocallyInjective_of_iso`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category
.{v', u'} D]   {FD : D → D → Type u_…
-/
lemma isLocallyBijective_iff_isIso :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨_, _⟩
    rw [← isIso_iff_of_reflects_iso f (sheafCompose J (forget A)),
      ← isLocallyBijective_iff_isIso']
    constructor <;> infer_instance
  · intro
    constructor <;> infer_instance

end

end Sheaf

variable (J A)

namespace GrothendieckTopology

/-- Given a category `C` equipped with a Grothendieck topology `J` and a concrete category `A`,
this property holds if a morphism in `Cᵒᵖ ⥤ A` satisfies `J.W` (i.e. becomes an iso after
sheafification) iff it is both locally injective and locally surjective. -/
/-
**CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.GrothendieckTopology C →       (A : Type u') →         [inst : CategoryThe
ory.Category.{v', u'} A] →           {FA : A → A → Type u_1} →             {CA :
 A → Type w'} →               [inst_1 : (X Y : A) → FunLike (FA X Y) (CA X) (CA 
Y)] → [CategoryTheory.ConcreteCategory A FA] → Prop
参数：A : Type u'；X Y : A；FA X Y；CA X；CA Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category `C` equipped with a Grothendieck topology `J` and a concrete ca
tegory `A`,
this property holds if a morphism in `Cᵒᵖ ⥤ A` satisfies `J.W` (i.e. becomes an 
iso after
sheafification) iff it is both locally injective and locally surjective.
-/
class WEqualsLocallyBijective : Prop where
  iff {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y) :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f

section

variable {A}
variable [J.WEqualsLocallyBijective A] {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)

/-
**CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_iff_isLocallyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presh
eaf.IsLocallySurjective J f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.iff`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Grothendie
ckTopology C} {A : Type u'}   {inst_1 : CategoryTheor…
-/
lemma W_iff_isLocallyBijective :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f := by
  apply WEqualsLocallyBijective.iff
/-
**CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_of_isLocallyBijective [Presheaf.IsLocallyInjective J f] [Presheaf.IsLoca
llySurjective J f] : J.W f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`：W_iff_isLo
callyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySur
jective J f
-/
lemma W_of_isLocallyBijective [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f] : J.W f := by
  rw [W_iff_isLocallyBijective]
  constructor <;> infer_instance

variable {J f}
/-
**CategoryTheory.GrothendieckTopology.W.isLocallyInjective** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology.W`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} A] {FA : A → A → Type u_1} {CA : A → Type w'}   [inst_2 : (X Y : A) → FunL
ike (FA X Y) (CA X) (CA Y)] [inst_3 : CategoryTheory.ConcreteCategory A FA]   [J
.WEqualsLocallyBijective A] {X Y : CategoryTheory.Functor Cᵒᵖ A} {f : X ⟶ Y},   
J.W f → CategoryTheory.Presheaf.IsLocallyInjective J f
参数：X Y : A；FA X Y；CA X；CA Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`：W_iff_isLo
callyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySur
jective J f
-/
lemma W.isLocallyInjective (hf : J.W f) : Presheaf.IsLocallyInjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).1
/-
**CategoryTheory.GrothendieckTopology.W.isLocallySurjective** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.GrothendieckTopology.W`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheory.Category.{v'
, u'} A] {FA : A → A → Type u_1} {CA : A → Type w'}   [inst_2 : (X Y : A) → FunL
ike (FA X Y) (CA X) (CA Y)] [inst_3 : CategoryTheory.ConcreteCategory A FA]   [J
.WEqualsLocallyBijective A] {X Y : CategoryTheory.Functor Cᵒᵖ A} {f : X ⟶ Y},   
J.W f → CategoryTheory.Presheaf.IsLocallySurjective J f
参数：X Y : A；FA X Y；CA X；CA Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`：W_iff_isLo
callyBijective : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySur
jective J f
-/
lemma W.isLocallySurjective (hf : J.W f) : Presheaf.IsLocallySurjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).2

variable [HasWeakSheafify J A] (P : Cᵒᵖ ⥤ A)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallyInjective
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallySurjective

end

/-
**CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.mk'** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) (A : Type u')   [inst_1 : CategoryTheory.Category.{v'
, u'} A] {FA : A → A → Type u_1} {CA : A → Type w'}   [inst_2 : (X Y : A) → FunL
ike (FA X Y) (CA X) (CA Y)] [inst_3 : CategoryTheory.ConcreteCategory A FA]   [i
nst_4 : CategoryTheory.HasWeakSheafify J A] [(CategoryTheory.forget A).ReflectsI
somorphisms]   [J.HasSheafCompose (CategoryTheory.forget A)]   [∀ (P : CategoryT
heory.Functor Cᵒᵖ A), CategoryTheory.Presheaf.IsLocallyInjective J (CategoryTheo
ry.toSheafify J P)]   [∀ (P : CategoryTheory.Functor Cᵒᵖ A), CategoryTheory.Pres
heaf.IsLocallySurjective J (CategoryTheory.toSheafify J P)],   J.WEqualsLocallyB
ijective A
参数：J : CategoryTheory.GrothendieckTopology C；A : Type u'；X Y : A；FA X Y；CA X；CA 
Y；CategoryTheory.forget A；CategoryTheory.forget A；P : CategoryTheory.Functor Cᵒᵖ
 A；CategoryTheory.toSheafify J P；P : CategoryTheory.Functor Cᵒᵖ A；CategoryTheory
.toSheafify J P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff`：W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso ((presheafToSheaf J A).map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`：isLocallyBijective_if
f_isIso : IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_comp_iff`：isLocallyInjective_
comp_iff [IsLocallyInjective J ψ] : IsLocallyInjective J (φ ≫ ψ) ↔ IsLocallyInje
ctive J φ
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_comp_iff`：isLocallySurjectiv
e_comp_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjectiv
e J f₂] [IsLocallySurjective J f₂] : IsLoc…
· 使用定理 `CategoryTheory.toSheafify_naturality`：toSheafify_naturality {P Q : Cᵒᵖ ⥤
 D} (η : P ⟶ Q) : η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η
· 使用引理 `CategoryTheory.Presheaf.comp_isLocallyInjective_iff`：comp_isLocallyInjec
tive_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjective 
J f₁] [IsLocallySurjective J f₁] : IsLoca…
· 使用引理 `CategoryTheory.Presheaf.comp_isLocallySurjective_iff`：comp_isLocallySurj
ective_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjecti
ve J f₁] : IsLocallySurjective J (f₁ ≫ f₂)…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma WEqualsLocallyBijective.mk' [HasWeakSheafify J A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)]
    [∀ (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)]
    [∀ (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P)] :
    J.WEqualsLocallyBijective A where
  iff {P Q} f := by
    rw [W_iff, ← Sheaf.isLocallyBijective_iff_isIso (A := A),
      ← Presheaf.isLocallyInjective_comp_iff J f (CategoryTheory.toSheafify J Q),
      ← Presheaf.isLocallySurjective_comp_iff J f (CategoryTheory.toSheafify J Q),
      CategoryTheory.toSheafify_naturality, Presheaf.comp_isLocallyInjective_iff,
      Presheaf.comp_isLocallySurjective_iff]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type w} [Category.{w'} D] {FD : D → D → Type*} {CD : D → Type (max u v)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max u v} D FD]
    [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] [(forget D).ReflectsIsomorphisms] :
    J.WEqualsLocallyBijective D := by
  apply WEqualsLocallyBijective.mk'
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : J.WEqualsLocallyBijective (Type (max u v)) :=
  inferInstance

end GrothendieckTopology

namespace Presheaf

variable {A}
variable [HasWeakSheafify J A] [J.WEqualsLocallyBijective A] {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.isLocallyInjective_presheafToSheaf_map_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_presheafToSheaf_map_iff : Sheaf.IsLocallyInjective ((pr
esheafToSheaf J A).map φ) ↔ IsLocallyInjective J φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sheaf.isLocallyInjective_sheafToPresheaf_map_iff`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Catego
ryTheory.Category.{v', u'} D]   {FD : D → D → Type u_…
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_comp_iff`：isLocallyInjective_
comp_iff [IsLocallyInjective J ψ] : IsLocallyInjective J (φ ≫ ψ) ↔ IsLocallyInje
ctive J φ
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsLocallyInjectiveToSheafify`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Groth
endieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.Presheaf.comp_isLocallyInjective_iff`：comp_isLocallyInjec
tive_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjective 
J f₁] [IsLocallySurjective J f₁] : IsLoca…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsLocallySurjectiveToSheafify`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grot
hendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.toSheafify_naturality`：toSheafify_naturality {P Q : Cᵒᵖ ⥤
 D} (η : P ⟶ Q) : η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η
· 使用定理 `CategoryTheory.ObjectProperty.ι_map`：ι_map {X Y} {f : X ⟶ Y} : P.ι.map f
 = f.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocallyInjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallyInjective ((presheafToSheaf J A).map φ) ↔ IsLocallyInjective J φ := by
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← isLocallyInjective_comp_iff J _ (toSheafify J Q),
    ← comp_isLocallyInjective_iff J (toSheafify J P),
    toSheafify_naturality, ObjectProperty.ι_map]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_presheafToSheaf_map_iff : Sheaf.IsLocallySurjective ((
presheafToSheaf J A).map φ) ↔ IsLocallySurjective J φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_sheafToPresheaf_map_iff`：isLoca
llySurjective_sheafToPresheaf_map_iff : Presheaf.IsLocallySurjective J ((sheafTo
Presheaf J A).map φ) ↔ IsLocallySurjective φ
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_comp_iff`：isLocallySurjectiv
e_comp_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjectiv
e J f₂] [IsLocallySurjective J f₂] : IsLoc…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsLocallyInjectiveToSheafify`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Groth
endieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsLocallySurjectiveToSheafify`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grot
hendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
· 使用引理 `CategoryTheory.Presheaf.comp_isLocallySurjective_iff`：comp_isLocallySurj
ective_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjecti
ve J f₁] : IsLocallySurjective J (f₁ ≫ f₂)…
· 使用定理 `CategoryTheory.toSheafify_naturality`：toSheafify_naturality {P Q : Cᵒᵖ ⥤
 D} (η : P ⟶ Q) : η ≫ toSheafify J _ = toSheafify J _ ≫ sheafifyMap J η
· 使用定理 `CategoryTheory.ObjectProperty.ι_map`：ι_map {X Y} {f : X ⟶ Y} : P.ι.map f
 = f.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocallySurjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallySurjective ((presheafToSheaf J A).map φ) ↔ IsLocallySurjective J φ := by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
    ← isLocallySurjective_comp_iff J _ (toSheafify J Q),
    ← comp_isLocallySurjective_iff J (toSheafify J P),
    toSheafify_naturality, ObjectProperty.ι_map]

end Presheaf

end CategoryTheory

