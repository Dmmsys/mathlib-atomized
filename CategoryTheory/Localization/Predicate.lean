/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.IsLocalization W` is introduced for a functor `L : C ⥤ D`
and `W : MorphismProperty C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `StrictUniversalPropertyFixedTarget L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factor as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `IsLocalization.mk'` for `L.IsLocalization W`.

When `L : C ⥤ D` is a localization functor for `W : MorphismProperty` (i.e. when
`[L.IsLocalization W]` holds), for any category `E`, there is
an equivalence `FunctorEquivalence L W E : (D ⥤ E) ≌ (W.FunctorsInverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `Lifting L W F F'`. The functions
`liftNatTrans` and `liftNatIso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category* E]

namespace Functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : MorphismProperty C`. -/
/-
**CategoryTheory.Functor.IsLocalization** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : MorphismProperty C`.
-/
class IsLocalization : Prop where
  /-- the functor inverts the given `MorphismProperty` -/
  inverts : W.IsInvertedBy L
  /-- the induced functor from the constructed localized category is an equivalence -/
  isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)
/-
**CategoryTheory.Functor.q_isLocalization** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：q_isLocalization : W.Q.IsLocalization W where inverts
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Q_inverts`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] (W : CategoryTheory.MorphismProperty C), W.IsInv
ertedBy W.Q
· 使用定理 `CategoryTheory.Localization.Construction.uniq`：uniq (G₁ G₂ : W.Localizat
ion ⥤ D) (h : W.Q ⋙ G₁ = W.Q ⋙ G₂) : G₁ = G₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Construction.fac`：fac : W.Q ⋙ lift G hG = G
-/
instance q_isLocalization : W.Q.IsLocalization W where
  inverts := W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl

end Functor

namespace Localization

/-- This universal property states that a functor `L : C ⥤ D` inverts the morphisms
in `W` and every functor `F : C ⥤ E` (for a fixed category `E`) inverting `W` admits
a unique factorisation through `L`. -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget** 是 Mathlib 中的一
个归纳类型，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           CategoryTheory.MorphismProperty C →        
     (E : Type u_3) →               [CategoryTheory.Category.{v_3, u_3} E] → Typ
e (max (max (max (max (max u_1 u_2) u_3) v_1) v_2) v_3)
参数：E : Type u_3；max (max (max (max (max u_1 u_2) u_3) v_1) v_2) v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This universal property states that a functor `L : C ⥤ D` inverts the morphisms
in `W` and every functor `F : C ⥤ E` (for a fixed category `E`) inverting `W` ad
mits
a unique factorisation through `L`.
-/
structure StrictUniversalPropertyFixedTarget where
  /-- the functor `L` inverts `W` -/
  inverts : W.IsInvertedBy L
  /-- any functor `C ⥤ E` which inverts `W` can be lifted as a functor `D ⥤ E` -/
  lift : ∀ (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
  /-- there is a factorisation involving the lifted functor -/
  fac : ∀ (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  /-- uniqueness of the lifted functor -/
  uniq : ∀ (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂

/-- The localized category `W.Localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
/-
**CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W
.Q W E where inverts
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Q_inverts`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] (W : CategoryTheory.MorphismProperty C), W.IsInv
ertedBy W.Q
· 使用定理 `CategoryTheory.Localization.Construction.fac`：fac : W.Q ⋙ lift G hG = G
· 使用定理 `CategoryTheory.Localization.Construction.uniq`：uniq (G₁ G₂ : W.Localizat
ion ⥤ D) (h : W.Q ⋙ G₁ = W.Q ⋙ G₂) : G₁ = G₂

--- 原说明 ---
The localized category `W.Localization` that was constructed satisfies
the universal property of the localization.
-/
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.Q W E where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (StrictUniversalPropertyFixedTarget W.Q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
/-
**CategoryTheory.Localization.strictUniversalPropertyFixedTargetId** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：strictUniversalPropertyFixedTargetId (hW : W <= MorphismProperty.isomorphi
sms C) : StrictUniversalPropertyFixedTarget (𝟭 C) W E where inverts _ _ f hf
参数：hW : W <= MorphismProperty.isomorphisms C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization.
-/
def strictUniversalPropertyFixedTargetId (hW : W ≤ MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E where
  inverts _ _ f hf := hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq

end Localization

namespace Functor

/-
**CategoryTheory.Functor.IsLocalization.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor.IsLocalization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) (h₁ : CategoryTheory.Localizati
on.StrictUniversalPropertyFixedTarget L W D)   (h₂ : CategoryTheory.Localization
.StrictUniversalPropertyFixedTarget L W W.Localization), L.IsLocalization W
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；h₁ : Cat
egoryTheory.Localization.StrictUniversalPropertyFixedTarget L W D；h₂ : CategoryT
heory.Localization.StrictUniversalPropertyFixedTarget L W W.Localization。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.inverts`：
∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.mk'`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.Q_inverts`：∀ {C : Type uC} [inst : Categ
oryTheory.Category.{uC', uC} C] (W : CategoryTheory.MorphismProperty C), W.IsInv
ertedBy W.Q
· 使用定理 `CategoryTheory.Localization.Construction.uniq`：uniq (G₁ G₂ : W.Localizat
ion ⥤ D) (h : W.Q ⋙ G₁ = W.Q ⋙ G₂) : G₁ = G₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Localization.Construction.fac`：fac : W.Q ⋙ lift G hG = G
· 使用定理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.fac`：∀ {C
 : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [ins
t_1 : CategoryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.uniq`：∀ {
C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} D] {L : Categor…
-/
theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }
/-
**CategoryTheory.Functor.IsLocalization.for_id** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsLocalization`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C],   ∀ W ≤ Ca
tegoryTheory.MorphismProperty.isomorphisms C, (CategoryTheory.Functor.id C).IsLo
calization W
参数：CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
-/
theorem IsLocalization.for_id (hW : W ≤ MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟭 C).IsLocalization (MorphismProperty.isomorphisms C) :=
  IsLocalization.for_id _ (by rfl)

end Functor

namespace Localization

variable [L.IsLocalization W]

/-
**CategoryTheory.Localization.inverts** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Localization`。
形式化陈述：inverts : W.IsInvertedBy L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.inverts`：∀ {C : Type u_1} {D : Typ
e u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTheory.
Category.{v_2, u_2} D} {L : Categor…
-/
theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.IsLocalization W`. -/
@[simps! hom]
/-
**CategoryTheory.Localization.isoOfHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Localization`。
形式化陈述：isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y
参数：f : X ⟶ Y；hf : W f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L

--- 原说明 ---
The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` 
which
belongs to `W`, when `L.IsLocalization W`.
-/
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.isoOfHom_hom_inv_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：isoOfHom_hom_inv_id {X Y : C} (f : X ⟶ Y) (hf : W f) : L.map f ≫ (isoOfHom
 L W f hf).inv = 𝟙 _
参数：f : X ⟶ Y；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma isoOfHom_hom_inv_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    L.map f ≫ (isoOfHom L W f hf).inv = 𝟙 _ :=
  (isoOfHom L W f hf).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.isoOfHom_inv_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：isoOfHom_inv_hom_id {X Y : C} (f : X ⟶ Y) (hf : W f) : (isoOfHom L W f hf)
.inv ≫ L.map f = 𝟙 _
参数：f : X ⟶ Y；hf : W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma isoOfHom_inv_hom_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _ :=
  (isoOfHom L W f hf).inv_hom_id

@[simp]
/-
**CategoryTheory.Localization.isoOfHom_id_inv** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Localization`。
形式化陈述：isoOfHom_id_inv (X : C) (hX : W (𝟙 X)) : (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _
参数：X : C；hX : W (𝟙 X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Localization.isoOfHom_hom`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma isoOfHom_id_inv (X : C) (hX : W (𝟙 X)) :
    (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _ := by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom, Iso.inv_hom_id, id_comp,
    isoOfHom_hom, Functor.map_id]

variable {W}
/-
**CategoryTheory.Localization.Construction.wIso_eq_isoOfHom** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Localization.Construction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C} {X Y : C}   (f : X ⟶ Y) (hf : W f),   CategoryTheor
y.Localization.Construction.wIso f hf = CategoryTheory.Localization.isoOfHom W.Q
 W f hf
参数：f : X ⟶ Y；hf : W f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
lemma Construction.wIso_eq_isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wIso f hf = isoOfHom W.Q W f hf := by ext; rfl
/-
**CategoryTheory.Localization.Construction.wInv_eq_isoOfHom_inv** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Localization.Construction`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Catego
ryTheory.MorphismProperty C} {X Y : C}   (f : X ⟶ Y) (hf : W f),   CategoryTheor
y.Localization.Construction.wInv f hf = (CategoryTheory.Localization.isoOfHom W.
Q W f hf).inv
参数：f : X ⟶ Y；hf : W f；CategoryTheory.Localization.isoOfHom W.Q W f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Construction.wIso_eq_isoOfHom`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismPr
operty C} {X Y : C}   (f : X ⟶ Y) (hf : W f),  …
-/
lemma Construction.wInv_eq_isoOfHom_inv {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wInv f hf = (isoOfHom W.Q W f hf).inv :=
  congr_arg Iso.inv (wIso_eq_isoOfHom f hf)
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Localization.Construction.lift L (inverts L W)).IsEquivalence :=
  (inferInstance : L.IsLocalization W).isEquivalence

variable (W)

/-- A chosen equivalence of categories `W.Localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.IsLocalization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`. -/
/-
**CategoryTheory.Localization.equivalenceFromModel** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Localization`。
形式化陈述：equivalenceFromModel : W.Localization ≌ D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.instIsEquivalenceLocalizationLift`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
A chosen equivalence of categories `W.Localization ≅ D` for a functor
`L : C ⥤ D` which satisfies `L.IsLocalization W`. This shall be used in
order to deduce properties of `L` from properties of `W.Q`.
-/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence

/-- Via the equivalence of categories `equivalenceFromModel L W : W.Localization ≌ D`,
one may identify the functors `W.Q` and `L`. -/
/-
**CategoryTheory.Localization.qCompEquivalenceFromModelFunctorIso** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).fun
ctor ≅ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Via the equivalence of categories `equivalenceFromModel L W : W.Localization ≌ D
`,
one may identify the functors `W.Q` and `L`.
-/
def qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L :=
  eqToIso (Construction.fac _ _)

/-- Via the equivalence of categories `equivalenceFromModel L W : W.Localization ≌ D`,
one may identify the functors `L` and `W.Q`. -/
/-
**CategoryTheory.Localization.compEquivalenceFromModelInverseIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Localization`。
形式化陈述：compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).invers
e ≅ W.Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Via the equivalence of categories `equivalenceFromModel L W : W.Localization ≌ D
`,
one may identify the functors `L` and `W.Q`.
-/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := rightUnitor _
/-
**CategoryTheory.Localization.essSurj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Localization`。
形式化陈述：essSurj (W) [L.IsLocalization W] : L.EssSurj
参数：W。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem essSurj (W) [L.IsLocalization W] : L.EssSurj :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩

/-- The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`. -/
/-
**CategoryTheory.Localization.whiskeringLeftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Localization`。
形式化陈述：whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(D ⥤ E) ⥤ W.functors_inverting E` induced by the composition
with a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`
.
-/
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  ObjectProperty.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (whiskeringLeftFunctor L W E).IsEquivalence := by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        rw [ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom, eqToHom_app, eqToHom_app,
          eqToHom_refl, eqToHom_refl]
        dsimp
        rw [comp_id, id_comp]
        rfl)
  exact Functor.isEquivalence_of_iso iso

/-- The equivalence of categories `(D ⥤ E) ≌ (W.FunctorsInverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : MorphismProperty C`. -/
/-
**CategoryTheory.Localization.functorEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Localization`。
形式化陈述：functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.instIsEquivalenceFunctorFunctorsInvertingWhi
skeringLeftFunctor`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor
…

--- 原说明 ---
The equivalence of categories `(D ⥤ E) ≌ (W.FunctorsInverting E)` induced by
the composition with a localization functor `L : C ⥤ D` with respect to
`W : MorphismProperty C`.
-/
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence

set_option linter.overlappingInstances false in
/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : MorphismProperty C`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.Localization.whiskeringLeftFunctor'** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Localization`。
形式化陈述：whiskeringLeftFunctor' [L.IsLocalization W] (E : Type*) [Category* E] : (D
 ⥤ E) ⥤ C ⥤ E
参数：E : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : MorphismProperty C`.
-/
def whiskeringLeftFunctor' [L.IsLocalization W] (E : Type*) [Category* E] :
    (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L
/-
**CategoryTheory.Localization.whiskeringLeftFunctor'_eq** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) (E : Type u_3) [inst_2 : Catego
ryTheory.Category.{v_3, u_3} E]   [inst_3 : L.IsLocalization W],   CategoryTheor
y.Localization.whiskeringLeftFunctor' L W E =     (CategoryTheory.Localization.w
hiskeringLeftFunctor L W E).comp       (CategoryTheory.inducedFunctor CategoryTh
eory.ObjectProperty.FullSubcategory.obj)
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；E : Type
 u_3；CategoryTheory.Localization.whiskeringLeftFunctor L W E；CategoryTheory.indu
cedFunctor CategoryTheory.ObjectProperty.FullSubcategory.obj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl

variable {E} in
@[simp]
/-
**CategoryTheory.Localization.whiskeringLeftFunctor'_obj** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) {E : Type u_3} [inst_2 : Catego
ryTheory.Category.{v_3, u_3} E]   [inst_3 : L.IsLocalization W] (F : CategoryThe
ory.Functor D E),   (CategoryTheory.Localization.whiskeringLeftFunctor' L W E).o
bj F = L.comp F
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；F : Cate
goryTheory.Functor D E；CategoryTheory.Localization.whiskeringLeftFunctor' L W E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (whiskeringLeftFunctor' L W E).Full := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full -- why is it not found automatically ???
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (whiskeringLeftFunctor' L W E).Faithful := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful -- why is it not found automatically ???
/-
**CategoryTheory.Localization.full_whiskeringLeft** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：full_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Cate
gory* E] : ((whiskeringLeft C D E).obj L).Full
参数：L : C ⥤ D；W；E : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma full_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).Full :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Full
/-
**CategoryTheory.Localization.faithful_whiskeringLeft** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Localization`。
形式化陈述：faithful_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [
Category* E] : ((whiskeringLeft C D E).obj L).Faithful
参数：L : C ⥤ D；W；E : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faithful_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).Faithful :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful

/-- The precomposition with a localization functor gives fully faithful functors
between functor categories. -/
/-
**CategoryTheory.Localization.fullyFaithfulWhiskeringLeft** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Localization`。
形式化陈述：fullyFaithfulWhiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type
*) [Category* E] : ((whiskeringLeft C D E).obj L).FullyFaithful
参数：L : C ⥤ D；W；E : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.full_whiskeringLeft`：full_whiskeringLeft (L 
: C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeringLeft C
 D E).obj L).Full
· 使用引理 `CategoryTheory.Localization.faithful_whiskeringLeft`：faithful_whiskering
Left (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] : ((whiskeri
ngLeft C D E).obj L).Faithful

--- 原说明 ---
The precomposition with a localization functor gives fully faithful functors
between functor categories.
-/
def fullyFaithfulWhiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).FullyFaithful := by
  have := full_whiskeringLeft L W E
  have := faithful_whiskeringLeft L W E
  exact FullyFaithful.ofFullyFaithful _

variable {E}
/-
**CategoryTheory.Localization.natTrans_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Localization`。
形式化陈述：natTrans_ext (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : 
F₁ ⟶ F₂} (h : forall X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ'
参数：L : C ⥤ D；W；h : forall X : C, τ.app (L.obj X) = τ'.app (L.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.instIsSplitEpiMap`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {X Y : C} (f : X ⟶…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem natTrans_ext (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂}
    (h : ∀ X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' := by
  have := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom), τ.naturality, τ'.naturality, h]

/-- When `L : C ⥤ D` is a localization functor for `W : MorphismProperty C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
/-
**CategoryTheory.Localization.Lifting** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Localization`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {E
 : Type u_3} →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       CategoryTheory.Functor C D →               CategoryTheory.MorphismPropert
y C →                 CategoryTheory.Functor C E → CategoryTheory.Functor D E → 
Type (max u_1 v_3)
参数：max u_1 v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `L : C ⥤ D` is a localization functor for `W : MorphismProperty C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obviou
s diagram
is commutative up to an isomorphism.
-/
class Lifting (L : C ⥤ D) (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E) where
  /-- the isomorphism relating the localization functor and the two other given functors -/
  iso (L W F F') : L ⋙ F' ≅ F

variable {W}

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`. -/
/-
**CategoryTheory.Localization.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Loc
alization`。
形式化陈述：lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] 
: D ⥤ E
参数：F : C ⥤ E；hF : W.IsInvertedBy F；L : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C` and
a functor `F : C ⥤ E` which inverts `W`, this is a choice of functor
`D ⥤ E` which lifts `F`.
-/
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩
/-
**CategoryTheory.Localization.liftingLift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Localization`。
形式化陈述：liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalizat
ion W] : Lifting L W F (lift F hF L)
参数：F : C ⥤ E；hF : W.IsInvertedBy F；L : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩

/-- The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`. -/
/-
**CategoryTheory.Localization.fac** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Loca
lization`。
形式化陈述：fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
 L ⋙ lift F hF L ≅ F
参数：F : C ⥤ E；hF : W.IsInvertedBy F；L : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `L ⋙ lift F hF L ≅ F` for any functor `F : C ⥤ E`
which inverts `W`, when `L : C ⥤ D` is a localization functor for `W`.
-/
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso L W F _
/-
**CategoryTheory.Localization.liftingConstructionLift** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Localization`。
形式化陈述：liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) : Lifting W.Q 
W F (Construction.lift F hF)
参数：F : C ⥤ D；hF : W.IsInvertedBy F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Construction.fac`：fac : W.Q ⋙ lift G hG = G
-/
instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.Q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩

variable (W)

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lift functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformation `F₁' ⟶ F₂'`. -/
/-
**CategoryTheory.Localization.liftNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Localization`。
形式化陈述：liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifti
ng L W F₂ F₂'] (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂'
参数：F₁ F₂ : C ⥤ E；F₁' F₂' : D ⥤ E；τ : F₁ ⟶ F₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.instFullFunctorWhiskeringLeftFunctor'`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lift functors `(F₁ F₂ : C ⥤ E)`,
a natural transformation `τ : F₁ ⟶ F₂` uniquely lifts to a natural transformatio
n `F₁' ⟶ F₂'`.
-/
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)

@[simp]
/-
**CategoryTheory.Localization.liftNatTrans_app** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Localization`。
形式化陈述：liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [L
ifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) (X : C) : (liftNatTrans L W F₁ F₂ F₁' F₂' τ).ap
p (L.obj X) = (Lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂
 F₂').inv.app X
参数：F₁ F₂ : C ⥤ E；F₁' F₂' : D ⥤ E；τ : F₁ ⟶ F₂；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Localization.instFullFunctorWhiskeringLeftFunctor'`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
-/
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.comp_liftNatTrans** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Localization`。
形式化陈述：comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L
 W F₁ F₁'] [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ'
 : F₂ ⟶ F₃) : liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' 
τ' = liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ')
参数：F₁ F₂ F₃ : C ⥤ E；F₁' F₂' F₃' : D ⥤ E；τ : F₁ ⟶ F₂；τ' : F₂ ⟶ F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.natTrans_ext`：natTrans_ext (L : C ⥤ D) (W) [
L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂} (h : forall X : C, τ.app (L
.obj X) = τ'.app (L.obj X)) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  natTrans_ext L W fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]

@[simp]
/-
**CategoryTheory.Localization.liftNatTrans_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Localization`。
形式化陈述：liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] : liftNatT
rans L W F F F' F' (𝟙 F) = 𝟙 F'
参数：F : C ⥤ E；F' : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.natTrans_ext`：natTrans_ext (L : C ⥤ D) (W) [
L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂} (h : forall X : C, τ.app (L
.obj X) = τ'.app (L.obj X)) : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  natTrans_ext L W fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lift functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
/-
**CategoryTheory.Localization.liftNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Localization`。
形式化陈述：liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂
 : Lifting L W F₂ F₂'] (e : F₁ ≅ F₂) : F₁' ≅ F₂' where hom
参数：F₁ F₂ : C ⥤ E；F₁' F₂' : D ⥤ E；e : F₁ ≅ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lift functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`.
-/
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv

namespace Lifting

@[simps]
/-
**CategoryTheory.Localization.Lifting.compRight** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Localization.Lifting`。
形式化陈述：compRight {E' : Type*} [Category* E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L 
W F F'] (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G)
参数：F : C ⥤ E；F' : D ⥤ E；G : E ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compRight {E' : Type*} [Category* E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩

@[simps]
/-
**CategoryTheory.Localization.Lifting.id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Localization.Lifting`。
形式化陈述：id : Lifting L W L (𝟭 D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id : Lifting L W L (𝟭 D) :=
  ⟨rightUnitor L⟩

@[simps]
/-
**CategoryTheory.Localization.Lifting.compLeft** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Localization.Lifting`。
形式化陈述：compLeft (F : D ⥤ E) : Localization.Lifting L W (L ⋙ F) F
参数：F : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance compLeft (F : D ⥤ E) : Localization.Lifting L W (L ⋙ F) F := ⟨Iso.refl _⟩

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`. -/
@[simps, instance_reducible]
/-
**CategoryTheory.Localization.Lifting.ofIsos** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Localization.Lifting`。
形式化陈述：ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [L
ifting L W F₁ F₁'] : Lifting L W F₂ F₂'
参数：e : F₁ ≅ F₂；e' : F₁' ≅ F₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`.
-/
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

end Lifting

end Localization

namespace Functor

namespace IsLocalization

open Localization

/-
**CategoryTheory.Functor.IsLocalization.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsLocalization`。
形式化陈述：of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocaliza
tion W
参数：e : L₁ ≅ L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory
.Category.{v', u'} D]   (W : CategoryTheory.M…
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_iso`：isEquivalence_of_iso {F G :
 C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence
· 使用定理 `CategoryTheory.Localization.instIsEquivalenceLocalizationLift`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W := by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }

/-- If `L : C ⥤ D` is a localization for `W : MorphismProperty C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of categories. -/
/-
**CategoryTheory.Functor.IsLocalization.of_equivalence_target** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.IsLocalization`。
形式化陈述：of_equivalence_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) 
[L.IsLocalization W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization W
参数：L' : C ⥤ E；eq : D ≌ E；e : L ⋙ eq.functor ≅ L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.iff_of_iso`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory
.Category.{v', u'} D]   (W : CategoryTheory.M…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.of_comp`：of_comp {C₁ C₂ C₃ 
: Type*} [Category* C₁] [Category* C₂] [Category* C₃] (W : MorphismProperty C₁) 
(F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G :…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_iso`：isEquivalence_of_iso {F G :
 C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence
· 使用定理 `CategoryTheory.Functor.isEquivalence_trans`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Localization.instIsEquivalenceLocalizationLift`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `L : C ⥤ D` is a localization for `W : MorphismProperty C`, then it is also
the case of a functor obtained by post-composing `L` with an equivalence of cate
gories.
-/
theorem of_equivalence_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization W := by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }
/-
**CategoryTheory.Functor.IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ E) [F.IsEquivalence] [L.IsLocalization W] :
    (L ⋙ F).IsLocalization W :=
  of_equivalence_target L W _ F.asEquivalence (Iso.refl _)
/-
**CategoryTheory.Functor.IsLocalization.of_isEquivalence** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor.IsLocalization`。
形式化陈述：of_isEquivalence (L : C ⥤ D) (W : MorphismProperty C) (hW : W <= MorphismP
roperty.isomorphisms C) [IsEquivalence L] : L.IsLocalization W
参数：L : C ⥤ D；W : MorphismProperty C；hW : W <= MorphismProperty.isomorphisms C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.for_id`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C],   ∀ W ≤ CategoryTheory.MorphismProperty.is
omorphisms C, (CategoryTheory.Func…
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
lemma of_isEquivalence (L : C ⥤ D) (W : MorphismProperty C)
    (hW : W ≤ MorphismProperty.isomorphisms C) [IsEquivalence L] :
    L.IsLocalization W := by
  have : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor

end IsLocalization

end Functor

namespace Localization

variable {D₁ D₂ : Type _} [Category* D₁] [Category* D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']

/-- If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, this is an equivalence of categories `D₁ ≌ D₂`. -/
/-
**CategoryTheory.Localization.uniq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Loc
alization`。
形式化陈述：uniq : D₁ ≌ D₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, this is an equivalence of categories `D₁ ≌ D₂`.
-/
def uniq : D₁ ≌ D₂ :=
  (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Localization.uniq_symm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Localization`。
形式化陈述：uniq_symm : (uniq L₁ L₂ W').symm = uniq L₂ L₁ W'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.ext`：∀ {C : Type u₁} {D : Type u₂} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D} 
  {x y : C ≌ D},   x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isoWhiskerRight_trans`：isoWhiskerRight_trans {G H
 K : C ⥤ D} (α : G ≅ H) (β : H ≅ K) (F : D ⥤ E) : isoWhiskerRight (α ≪≫ β) F = i
soWhiskerRight α F ≪≫ isoWhiskerRi…
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Equivalence.mk'.congr_simp`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (functor : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
lemma uniq_symm : (uniq L₁ L₂ W').symm = uniq L₂ L₁ W' := by
  dsimp [uniq, Equivalence.trans]
  ext <;> aesop

/-- The functor of equivalence of localized categories given by `Localization.uniq` is
compatible with the localization functors. -/
/-
**CategoryTheory.Localization.compUniqFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Localization`。
形式化陈述：compUniqFunctor : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor of equivalence of localized categories given by `Localization.uniq` 
is
compatible with the localization functors.
-/
def compUniqFunctor : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂ :=
  calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'

/-- The inverse functor of equivalence of localized categories given by `Localization.uniq` is
compatible with the localization functors. -/
/-
**CategoryTheory.Localization.compUniqInverse** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Localization`。
形式化陈述：compUniqInverse : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of equivalence of localized categories given by `Localizatio
n.uniq` is
compatible with the localization functors.
-/
def compUniqInverse : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁ := compUniqFunctor L₂ L₁ W'
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lifting L₁ W' L₂ (uniq L₁ L₂ W').functor := ⟨compUniqFunctor L₁ L₂ W'⟩
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lifting L₂ W' L₁ (uniq L₁ L₂ W').inverse := ⟨compUniqInverse L₁ L₂ W'⟩

/-- If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, any functor `F : D₁ ⥤ D₂` equipped with an isomorphism
`L₁ ⋙ F ≅ L₂` is isomorphic to the functor of the equivalence given by `uniq`. -/
/-
**CategoryTheory.Localization.isoUniqFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Localization`。
形式化陈述：isoUniqFunctor (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂) : F ≅ (uniq L₁ L₂ W').funct
or
参数：F : D₁ ⥤ D₂；e : L₁ ⋙ F ≅ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` are two localization functors for the
same `MorphismProperty C`, any functor `F : D₁ ⥤ D₂` equipped with an isomorphis
m
`L₁ ⋙ F ≅ L₂` is isomorphic to the functor of the equivalence given by `uniq`.
-/
def isoUniqFunctor (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂) :
    F ≅ (uniq L₁ L₂ W').functor :=
  letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Localization.morphismProperty_eq_top** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Localization`。
形式化陈述：morphismProperty_eq_top [L.IsLocalization W] (P : MorphismProperty D) [P.R
espectsIso] [P.IsMultiplicative] (h₁ : forall ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f)
) (h₂ : forall ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv) : P 
= ⊤
参数：P : MorphismProperty D；h₁ : forall ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f)；h₂ : fo
rall ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Construction.morphismProperty_eq_top`：morphi
smProperty_eq_top (P : MorphismProperty W.Localization) [P.IsStableUnderComposit
ion] (hP₁ : forall ⦃X Y : C⦄ (f : X ⟶ Y), P (W.Q.map f…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inverseImage`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : 
CategoryTheory.Category.{v', u'} D]   {P : CategoryTheory.M…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Construction.wInv_eq_isoOfHom_inv`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Morphi
smProperty C} {X Y : C}   (f : X ⟶ Y) (hf : W f),  …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Localization.isoOfHom_hom`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用引理 `CategoryTheory.Localization.isoOfHom_inv_hom_id`：isoOfHom_inv_hom_id {X 
Y : C} (f : X ⟶ Y) (hf : W f) : (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.MorphismProperty.map_inverseImage_eq_of_isEquivalence`：ma
p_inverseImage_eq_of_isEquivalence (P : MorphismProperty D) [P.RespectsIso] (F :
 C ⥤ D) [F.IsEquivalence] : (P.inverseImage F).map F = P
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.MorphismProperty.map_top_eq_top_of_essSurj_of_full`：map_t
op_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] : (⊤ : MorphismPro
perty C).map F = ⊤
-/
lemma morphismProperty_eq_top [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso]
    [P.IsMultiplicative] (h₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f))
    (h₂ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv) :
    P = ⊤ := by
  let e := compUniqFunctor W.Q L W
  have hP : P.inverseImage (uniq W.Q L W).functor = ⊤ :=
    Construction.morphismProperty_eq_top _
      (fun _ _ f ↦ (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso e).app (Arrow.mk f))).2 (h₁ f))
      (fun X Y f hf ↦ by
        refine (P.arrow_mk_iso_iff (Arrow.isoMk (e.app _) (e.app _) ?_)).2 (h₂ f hf)
        dsimp
        rw [Construction.wInv_eq_isoOfHom_inv, ← cancel_mono (isoOfHom L W f hf).hom,
          assoc, assoc, Iso.inv_hom_id, comp_id, isoOfHom_hom, ← NatTrans.naturality,
          Functor.comp_map, ← Functor.map_comp_assoc,
          isoOfHom_inv_hom_id, map_id, id_comp])
  rw [← P.map_inverseImage_eq_of_isEquivalence (uniq W.Q L W).functor, hP,
    MorphismProperty.map_top_eq_top_of_essSurj_of_full]
/-
**CategoryTheory.Localization.isGroupoid** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Localization`。
形式化陈述：isGroupoid [L.IsLocalization ⊤] : IsGroupoid D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isGroupoid_iff_isomorphisms_eq_top`：isGroupoid_iff_isomor
phisms_eq_top (C : Type*) [Category* C] : IsGroupoid C ↔ isomorphisms C = ⊤
· 使用引理 `CategoryTheory.Localization.morphismProperty_eq_top`：morphismProperty_eq
_top [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso] [P.IsMultipli
cative] (h₁ : forall ⦃X Y : C⦄ (f : X ⟶ Y…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instIsomorphisms`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.MorphismP
roperty.isomorphisms C).IsMultiplicative
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma isGroupoid [L.IsLocalization ⊤] :
    IsGroupoid D := by
  rw [isGroupoid_iff_isomorphisms_eq_top]
  exact morphismProperty_eq_top L ⊤ _
    (fun _ _ f ↦ inverts L ⊤ _ (by simp))
    (fun _ _ f hf ↦ Iso.isIso_inv _)
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsGroupoid (⊤ : MorphismProperty C).Localization :=
  isGroupoid <| MorphismProperty.Q ⊤

/-- Localization of a category with respect to all morphisms results in a groupoid. -/
@[instance_reducible]
/-
**CategoryTheory.Localization.groupoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Localization`。
形式化陈述：groupoid : Groupoid (⊤ : MorphismProperty C).Localization
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.instIsGroupoidLocalizationTopMorphismPropert
y`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C], CategoryTheor
y.IsGroupoid ⊤.Localization

--- 原说明 ---
Localization of a category with respect to all morphisms results in a groupoid.
-/
def groupoid : Groupoid (⊤ : MorphismProperty C).Localization :=
  Groupoid.ofIsGroupoid

end Localization

section

variable {X Y : C} (f g : X ⟶ Y)

/-- The property that two morphisms become equal in the localized category. -/
/-
**CategoryTheory.AreEqualizedByLocalization** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：AreEqualizedByLocalization : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that two morphisms become equal in the localized category.
-/
def AreEqualizedByLocalization : Prop := W.Q.map f = W.Q.map g
/-
**CategoryTheory.areEqualizedByLocalization_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：areEqualizedByLocalization_iff [L.IsLocalization W] : AreEqualizedByLocali
zation W f g ↔ L.map f = L.map g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma areEqualizedByLocalization_iff [L.IsLocalization W] :
    AreEqualizedByLocalization W f g ↔ L.map f = L.map g := by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    dsimp
    rw [h]

namespace AreEqualizedByLocalization

/-
**CategoryTheory.AreEqualizedByLocalization.mk** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.AreEqualizedByLocalization`。
形式化陈述：mk (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g) : AreEqualized
ByLocalization W f g
参数：L : C ⥤ D；h : L.map f = L.map g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.areEqualizedByLocalization_iff`：areEqualizedByLocalizatio
n_iff [L.IsLocalization W] : AreEqualizedByLocalization W f g ↔ L.map f = L.map 
g
-/
lemma mk (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g) :
    AreEqualizedByLocalization W f g :=
  (areEqualizedByLocalization_iff L W f g).2 h

variable {W f g}
/-
**CategoryTheory.AreEqualizedByLocalization.map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.AreEqualizedByLocalization`。
形式化陈述：map_eq (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalizatio
n W] : L.map f = L.map g
参数：h : AreEqualizedByLocalization W f g；L : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.areEqualizedByLocalization_iff`：areEqualizedByLocalizatio
n_iff [L.IsLocalization W] : AreEqualizedByLocalization W f g ↔ L.map f = L.map 
g
-/
lemma map_eq (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] :
    L.map f = L.map g :=
  (areEqualizedByLocalization_iff L W f g).1 h
/-
**CategoryTheory.AreEqualizedByLocalization.map_eq_of_isInvertedBy** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.AreEqualizedByLocalization`。
形式化陈述：map_eq_of_isInvertedBy (h : AreEqualizedByLocalization W f g) (F : C ⥤ D) 
(hF : W.IsInvertedBy F) : F.map f = F.map g
参数：h : AreEqualizedByLocalization W f g；F : C ⥤ D；hF : W.IsInvertedBy F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.AreEqualizedByLocalization.map_eq`：map_eq (h : AreEqualiz
edByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] : L.map f = L.map g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_eq_of_isInvertedBy (h : AreEqualizedByLocalization W f g)
    (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    F.map f = F.map g := by
  simp [← NatIso.naturality_1 (Localization.fac F hF W.Q), h.map_eq W.Q]

end AreEqualizedByLocalization

end

end CategoryTheory

