/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `MonoCoprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `HasCoproduct A B`
holds. If so, it is shown that right inclusions are
also monomorphisms.

More generally, we deduce that when suitable coproducts exist, then
if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.
It also follows that for any `i : I`, `Sigma.ι X i : X i ⟶ ∐ X` is
a monomorphism.

TODO: define distributive categories, and show that they satisfy `MonoCoprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/

@[expose] public section


noncomputable section

universe u

namespace CategoryTheory

open CategoryTheory.Category CategoryTheory.Limits

namespace Limits

variable (C : Type*) [Category* C]

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
/-
**CategoryTheory.Limits.MonoCoprod** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This condition expresses that inclusion morphisms into coproducts are monomorphi
sms.
-/
class MonoCoprod : Prop where
  /-- the left inclusion of a colimit binary cofan is mono -/
  binaryCofan_inl : ∀ ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl

variable {C}
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) monoCoprodOfHasZeroMorphisms [HasZeroMorphisms C] : MonoCoprod C :=
  ⟨fun A B c hc => by
    have : IsSplitMono c.inl :=
      IsSplitMono.mk' (SplitMono.mk (BinaryCofan.IsColimit.desc hc (𝟙 A) 0) (IsColimit.fac _ _ _))
    infer_instance⟩

namespace MonoCoprod

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.binaryCofan_inr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.MonoCoprod`。
形式化陈述：binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsCol
imit c) : Mono c.inr
参数：c : BinaryCofan A B；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.inr_desc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Bi
naryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.inl_desc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : CategoryTheory.Limits.Bi
naryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inl`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.Limits.MonoCopro
d C] ⦃A B : C⦄   (c : CategoryTheory.L…
-/
theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr := by
  have hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _
      (fun f₁ f₂ => BinaryCofan.IsColimit.desc (s := c) hc f₂ f₁)
      (by simp) (by simp)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by cat_disch) (by cat_disch))
  exact binaryCofan_inl _ hc'
/-
**CategoryTheory.Limits.MonoCoprod.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.MonoCoprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inl : A ⟶ A ⨿ B) :=
  binaryCofan_inl _ (colimit.isColimit _)
/-
**CategoryTheory.Limits.MonoCoprod.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.MonoCoprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inr : B ⟶ A ⨿ B) :=
  binaryCofan_inr _ (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.mono_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.MonoCoprod`。
形式化陈述：mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂
 : IsColimit c₂) : Mono c₁.inl ↔ Mono c₂.inl
参数：hc₁ : IsColimit c₁；hc₂ : IsColimit c₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl := by
  suffices
    ∀ (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    by exact ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂ _
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using!
    mono_comp c₁.inl (hc₁.coconePointUniqueUpToIso hc₂).hom
/-
**CategoryTheory.Limits.MonoCoprod.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.MonoCoprod`。
形式化陈述：mk' (h : forall A B : C, exists (c : BinaryCofan A B) (_ : IsColimit c), M
ono c.inl) : MonoCoprod C
参数：h : forall A B : C, exists (c : BinaryCofan A B) (_ : IsColimit c), Mono c.in
l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoCoprod.mono_inl_iff`：mono_inl_iff {A B : C} {c
₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) : Mono c₁.inl 
↔ Mono c₂.inl
-/
theorem mk' (h : ∀ A B : C, ∃ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C :=
  ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.monoCoprodType** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits.MonoCoprod`。
形式化陈述：monoCoprodType : MonoCoprod (Type u)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoCoprod.mk'`：mk' (h : forall A B : C, exists (c
 : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
-/
instance monoCoprodType : MonoCoprod (Type u) :=
  MonoCoprod.mk' fun A B => by
    refine ⟨BinaryCofan.mk (↾(Sum.inl : A → A ⊕ B))
      (↾Sum.inr), ?_, ?_⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ => ↾fun x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ m h₁ h₂ => by
          ext x
          rcases x with x | x
          · exact ConcreteCategory.congr_hom h₁ x
          · exact ConcreteCategory.congr_hom h₂ x)
    · rw [mono_iff_injective]
      intro a₁ a₂ h
      simpa using h

section

variable {I₁ I₂ : Type*} {X : I₁ ⊕ I₂ → C} (c : Cofan X)
  (c₁ : Cofan (X ∘ Sum.inl)) (c₂ : Cofan (X ∘ Sum.inr))
  (hc : IsColimit c) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
include hc hc₁ hc₂

/-- Given a family of objects `X : I₁ ⊕ I₂ → C`, a cofan of `X`, and two colimit cofans
of `X ∘ Sum.inl` and `X ∘ Sum.inr`, this is a cofan for `c₁.pt` and `c₂.pt` whose
point is `c.pt`. -/
@[simp]
/-
**CategoryTheory.Limits.MonoCoprod.binaryCofanSum** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.MonoCoprod`。
形式化陈述：binaryCofanSum : BinaryCofan c₁.pt c₂.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of objects `X : I₁ ⊕ I₂ → C`, a cofan of `X`, and two colimit cof
ans
of `X ∘ Sum.inl` and `X ∘ Sum.inr`, this is a cofan for `c₁.pt` and `c₂.pt` whos
e
point is `c.pt`.
-/
def binaryCofanSum : BinaryCofan c₁.pt c₂.pt :=
  BinaryCofan.mk (Cofan.IsColimit.desc hc₁ (fun i₁ => c.inj (Sum.inl i₁)))
    (Cofan.IsColimit.desc hc₂ (fun i₂ => c.inj (Sum.inr i₂)))

set_option backward.isDefEq.respectTransparency false in
/-- The binary cofan `binaryCofanSum c c₁ c₂ hc₁ hc₂` is colimit. -/
/-
**CategoryTheory.Limits.MonoCoprod.isColimitBinaryCofanSum** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：isColimitBinaryCofanSum : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary cofan `binaryCofanSum c c₁ c₂ hc₁ hc₂` is colimit.
-/
def isColimitBinaryCofanSum : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂) :=
  BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => Cofan.IsColimit.desc hc (fun i => match i with
      | Sum.inl i₁ => c₁.inj i₁ ≫ f₁
      | Sum.inr i₂ => c₂.inj i₂ ≫ f₂))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₁ _ _ (by simp))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₂ _ _ (by simp))
    (fun f₁ f₂ m hm₁ hm₂ => by
      apply Cofan.IsColimit.hom_ext hc
      rintro (i₁ | i₂) <;> cat_disch)
/-
**CategoryTheory.Limits.MonoCoprod.mono_binaryCofanSum_inl** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_binaryCofanSum_inl [MonoCoprod C] : Mono (binaryCofanSum c c₁ c₂ hc₁ 
hc₂).inl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inl`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.Limits.MonoCopro
d C] ⦃A B : C⦄   (c : CategoryTheory.L…
-/
lemma mono_binaryCofanSum_inl [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl :=
  MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
/-
**CategoryTheory.Limits.MonoCoprod.mono_binaryCofanSum_inr** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_binaryCofanSum_inr [MonoCoprod C] : Mono (binaryCofanSum c c₁ c₂ hc₁ 
hc₂).inr
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inr`：binaryCofan_inr {A B :
 C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) : Mono c.inr
-/
lemma mono_binaryCofanSum_inr [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr :=
  MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.mono_binaryCofanSum_inl'** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_binaryCofanSum_inl' [MonoCoprod C] (inl : c₁.pt ⟶ c.pt) (hinl : foral
l (i₁ : I₁), c₁.inj i₁ ≫ inl = c.inj (Sum.inl i₁)) : Mono inl
参数：inl : c₁.pt ⟶ c.pt；hinl : forall (i₁ : I₁), c₁.inj i₁ ≫ inl = c.inj (Sum.inl 
i₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inl`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.Limits.MonoCopro
d C] ⦃A B : C⦄   (c : CategoryTheory.L…
-/
lemma mono_binaryCofanSum_inl' [MonoCoprod C] (inl : c₁.pt ⟶ c.pt)
    (hinl : ∀ (i₁ : I₁), c₁.inj i₁ ≫ inl = c.inj (Sum.inl i₁)) :
    Mono inl := by
  suffices inl = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl by
    rw [this]
    exact MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₁ _ _ (by simpa using hinl)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.mono_binaryCofanSum_inr'** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_binaryCofanSum_inr' [MonoCoprod C] (inr : c₂.pt ⟶ c.pt) (hinr : foral
l (i₂ : I₂), c₂.inj i₂ ≫ inr = c.inj (Sum.inr i₂)) : Mono inr
参数：inr : c₂.pt ⟶ c.pt；hinr : forall (i₂ : I₂), c₂.inj i₂ ≫ inr = c.inj (Sum.inr 
i₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inr`：binaryCofan_inr {A B :
 C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) : Mono c.inr
-/
lemma mono_binaryCofanSum_inr' [MonoCoprod C] (inr : c₂.pt ⟶ c.pt)
    (hinr : ∀ (i₂ : I₂), c₂.inj i₂ ≫ inr = c.inj (Sum.inr i₂)) :
    Mono inr := by
  suffices inr = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr by
    rw [this]
    exact MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₂ _ _ (by simpa using hinr)

end

section

variable [MonoCoprod C] {I J : Type*} (X : I → C) (ι : J → I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.mono_of_injective_aux** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_of_injective_aux (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofa
n (X ∘ ι)) (hc : IsColimit c) (hc₁ : IsColimit c₁) (c₂ : Cofan (fun (k : ((Set.r
ange ι)ᶜ : Set I)) => X k.1)) (hc₂ : IsColimit c₂) : Mono (Cofan.IsColimit.desc 
hc₁ (fun i => c.inj (ι i)))
参数：hι : Function.Injective ι；c : Cofan X；c₁ : Cofan (X ∘ ι)；hc : IsColimit c；hc₁
 : IsColimit c₁；c₂ : Cofan (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)；hc₂ : I
sColimit c₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_binaryCofanSum_inl'`：mono_binaryCo
fanSum_inl' [MonoCoprod C] (inl : c₁.pt ⟶ c.pt) (hinl : forall (i₁ : I₁), c₁.inj
 i₁ ≫ inl = c.inj (Sum.inl i₁)) : Mono inl
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mono_of_injective_aux (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
    (hc : IsColimit c) (hc₁ : IsColimit c₁)
    (c₂ : Cofan (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1))
    (hc₂ : IsColimit c₂) : Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) := by
  classical
  let e := ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  refine mono_binaryCofanSum_inl' (Cofan.mk c.pt (fun i' => c.inj (e i'))) _ _ ?_
    hc₁ hc₂ _ (by simp [e])
  exact IsColimit.ofIsoColimit ((IsColimit.ofCoconeEquiv (Cocone.equivalenceOfReindexing
    (Discrete.equivalence e) (Iso.refl _))).symm hc) (Cocone.ext (Iso.refl _))

variable (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
  (hc : IsColimit c) (hc₁ : IsColimit c₁)
include hι

include hc in
/-
**CategoryTheory.Limits.MonoCoprod.mono_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_of_injective [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k
.1)] : Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i)))
参数：fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_of_injective_aux`：mono_of_injectiv
e_aux (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι)) (hc : IsCol
imit c) (hc₁ : IsColimit c₁) (c₂ : Cofan (fu…
-/
lemma mono_of_injective [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) :=
  mono_of_injective_aux X ι hι c c₁ hc hc₁ _ (colimit.isColimit _)
/-
**CategoryTheory.Limits.MonoCoprod.mono_of_injective'** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.MonoCoprod`。
形式化陈述：mono_of_injective' [HasCoproduct (X ∘ ι)] [HasCoproduct X] [HasCoproduct (
fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] : Mono (Sigma.desc (f
参数：X ∘ ι；fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_of_injective`：mono_of_injective [H
asCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] : Mono (Cofan.IsColim
it.desc hc₁ (fun i => c.inj (ι i)))
-/
lemma mono_of_injective' [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.desc (f := X ∘ ι) (fun j => Sigma.ι X (ι j))) :=
  mono_of_injective X ι hι _ _ (colimit.isColimit _) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTh
eory.Limits.MonoCoprod C] {I : Type u_2}   {J : Type u_3} (X : I → C) (ι : J → I
),   Function.Injective ι →     ∀ [inst_2 : CategoryTheory.Limits.HasCoproduct (
X ∘ ι)] [inst_3 : CategoryTheory.Limits.HasCoproduct X]       [CategoryTheory.Li
mits.HasCoproduct fun k => X ↑k],       CategoryTheory.Mono (CategoryTheory.Limi
ts.Sigma.map' ι fun j => CategoryTheory.CategoryStruct.id ((X ∘ ι) j))
参数：X : I → C；ι : J → I；X ∘ ι；CategoryTheory.Limits.Sigma.map' ι fun j => Categor
yTheory.CategoryStruct.id ((X ∘ ι) j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_of_injective'`：mono_of_injective' 
[HasCoproduct (X ∘ ι)] [HasCoproduct X] [HasCoproduct (fun (k : ((Set.range ι)ᶜ 
: Set I)) => X k.1)] : Mono (Sigma.desc (…
-/
lemma mono_map'_of_injective [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.map' ι (fun j => 𝟙 ((X ∘ ι) j))) := by
  convert! mono_of_injective' X ι hι
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_comp_map', id_comp, colimit.ι_desc]
  simp

end

section

variable [MonoCoprod C] {I : Type*} (X : I → C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.MonoCoprod.mono_inj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits.MonoCoprod`。
形式化陈述：mono_inj (c : Cofan X) (h : IsColimit c) (i : I) [HasCoproduct (fun (k : (
(Set.range (fun _ : Unit => i))ᶜ : Set I)) => X k.1)] : Mono (Cofan.inj c i)
参数：c : Cofan X；h : IsColimit c；i : I；fun (k : ((Set.range (fun _ : Unit => i))ᶜ 
: Set I)) => X k.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_of_injective`：mono_of_injective [H
asCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] : Mono (Cofan.IsColim
it.desc hc₁ (fun i => c.inj (ι i)))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma mono_inj (c : Cofan X) (h : IsColimit c) (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit ↦ i))ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.inj c i) := by
  let ι : Unit → I := fun _ ↦ i
  have hι : Function.Injective ι := fun _ _ _ ↦ rfl
  exact mono_of_injective X ι hι c (Cofan.mk (X i) (fun _ ↦ 𝟙 _)) h
    (Cofan.IsColimit.mk _ (fun s => s.inj ()))
/-
**CategoryTheory.Limits.MonoCoprod.mono_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.MonoCoprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mono_ι [HasCoproduct X] (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit ↦ i))ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.ι X i) :=
  mono_inj X _ (colimit.isColimit _) i

end

open CategoryTheory.Functor

section Preservation

variable {D : Type*} [Category* D] (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.MonoCoprod`。
形式化陈述：monoCoprod_of_preservesCoprod_of_reflectsMono [MonoCoprod D] [PreservesCol
imitsOfShape (Discrete WalkingPair) F] [ReflectsMonomorphisms F] : MonoCoprod C 
where binaryCofan_inl {A B} c h
参数：Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.MonoCoprod.binaryCofan_inl`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.Limits.MonoCopro
d C] ⦃A B : C⦄   (c : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monoCoprod_of_preservesCoprod_of_reflectsMono [MonoCoprod D]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsMonomorphisms F] : MonoCoprod C where
  binaryCofan_inl {A B} c h := by
    let c' := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    apply mono_of_mono_map F
    change Mono c'.inl
    apply MonoCoprod.binaryCofan_inl
    apply mapIsColimitOfPreservesOfIsColimit F
    apply IsColimit.ofIsoColimit h
    refine Cocone.ext (φ := eqToIso rfl) ?_
    rintro ⟨(j₁ | j₂)⟩ <;> simp only [eqToIso_refl, Iso.refl_hom,
      Category.comp_id, BinaryCofan.mk_inl, BinaryCofan.mk_inr]

end Preservation

section Concrete

/-
**CategoryTheory.Limits.MonoCoprod.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.MonoCoprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type*}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesColimitsOfShape (Discrete WalkingPair) (forget C)]
    [ReflectsMonomorphisms (forget C)] : MonoCoprod C :=
  monoCoprod_of_preservesCoprod_of_reflectsMono (forget C)

end Concrete

end MonoCoprod

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) [HasCoproducts.{u} C] [MonoCoprod C] :
    (sigmaConst.{u}.obj A).PreservesMonomorphisms where
  preserves {J I} ι hι := by
    rw [mono_iff_injective] at hι
    exact MonoCoprod.mono_map'_of_injective (fun (i : I) ↦ A) ι hι

end Limits

end CategoryTheory

