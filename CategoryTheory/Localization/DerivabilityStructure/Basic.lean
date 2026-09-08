/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism, i.e. `W₁ : MorphismProperty C₁`,
`W₂ : MorphismProperty C₂`, and `Φ.functor : C₁ ⥤ C₂` is a functor which maps `W₁` to `W₂`.
Following the definition introduced by Bruno Kahn and Georges Maltsiniotis in
[Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008],
we say that `Φ` is a right derivability structure if `Φ` has right resolutions and
the following 2-square is Guitart exact, where `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, and `F : D₁ ⥤ D₂` is the induced functor
on the localized categories:

```
    Φ.functor
  C₁   ⥤   C₂
  |         |
L₁|         | L₂
  v         v
  D₁   ⥤   D₂
       F
```

## Implementation details

In the field `guitartExact'` of the structure `LocalizerMorphism.IsRightDerivabilityStructure`,
The condition that the square is Guitart exact is stated for the localization functors
of the constructed categories (`W₁.Q` and `W₂.Q`).
The lemma `LocalizerMorphism.isRightDerivabilityStructure_iff` shows that it does
not depend on the choice of the localization functors.

## TODO

* Construct the injective derivability structure in order to derive functor from
  the bounded below homotopy category in an abelian category with enough injectives
* Construct the projective derivability structure in order to derive functor from
  the bounded above homotopy category in an abelian category with enough projectives
* Construct the flat derivability structure on the bounded above homotopy category
  of categories of modules (and categories of sheaves of modules)
* Define the product derivability structure and formalize derived functors of
  functors in several variables

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

public section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/-- A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a right derivability
structure if it has right resolutions and the 2-square where the left and right functors
are localization functors for `W₁` and `W₂` are Guitart exact. -/
/-
**CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure** 是 Mathlib 中的一个
类，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：IsRightDerivabilityStructure : Prop where hasRightResolutions : Φ.HasRight
Resolutions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a right derivability
structure if it has right resolutions and the 2-square where the left and right 
functors
are localization functors for `W₁` and `W₂` are Guitart exact.
-/
class IsRightDerivabilityStructure : Prop where
  hasRightResolutions : Φ.HasRightResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isRightDerivabilityStructure` instead,
  see also the lemma `isRightDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

attribute [instance] IsRightDerivabilityStructure.hasRightResolutions
  IsRightDerivabilityStructure.guitartExact'

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] (F : D₁ ⥤ D₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ 
L₂ ≅ L₁ ⋙ F) : Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartExact e.hom
参数：e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.guitartExa
ct'`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁
}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `CategoryTheory.TwoSquare.vComp'_app`：∀ {C₁ : Type u_1} {C₂ : Type u_2} {
C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Type u_5} {D₃ : Type u_6}   [inst : Categor
yTheory.Category.{v_1, u_…
· 使用定理 `CategoryTheory.Localization.liftNatIso_hom`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Localization.liftNatTrans_app`：liftNatTrans_app (F₁ F₂ : 
C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂)
 (X : C) : (liftNatTrans L W F₁ F₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.TwoSquare.GuitartExact.vComp'_iff_of_equivalences`：∀ {C₁ 
: Type u_1} {C₂ : Type u_2} {C₃ : Type u_3} {D₁ : Type u_4} {D₂ : Type u_5} {D₃ 
: Type u_6}   [inst : CategoryTheory.Category.{v_1, u_…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartExact e.hom := by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L₂ W₂
  let e₁ : W₁.Q ⋙ E₁.functor ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let e₂ : W₂.Q ⋙ E₂.functor ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  let e'' : (Φ.functor ⋙ W₂.Q) ⋙ E₂.functor ≅ (W₁.Q ⋙ E₁.functor) ⋙ F :=
    associator _ _ _ ≪≫ isoWhiskerLeft _ e₂ ≪≫ e ≪≫ isoWhiskerRight e₁.symm F
  let e''' : Φ.localizedFunctor W₁.Q W₂.Q ⋙ E₂.functor ≅ E₁.functor ⋙ F :=
    liftNatIso W₁.Q W₁ _ _ _ _ e''
  have : TwoSquare.vComp' e'.hom e'''.hom e₁ e₂ = e.hom := by
    ext X₁
    rw [TwoSquare.vComp'_app, liftNatIso_hom, liftNatTrans_app]
    simp only [Functor.comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      whiskerRight_app, id_comp, assoc, e'']
    dsimp [Lifting.iso]
    rw [F.map_id, id_comp, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, comp_id,
      ← Functor.map_comp_assoc]
    erw [show (CatCommSq.iso Φ.functor W₁.Q W₂.Q (localizedFunctor Φ W₁.Q W₂.Q)).hom =
      (Lifting.iso W₁.Q W₁ _ _).inv by rfl, Iso.inv_hom_id_app]
    simp
  rw [← TwoSquare.GuitartExact.vComp'_iff_of_equivalences e'.hom E₁ E₂ e''' e₁ e₂, this]
/-
**CategoryTheory.LocalizerMorphism.guitartExact_of_isRightDerivabilityStructure'
** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：guitartExact_of_isRightDerivabilityStructure' [h : Φ.IsRightDerivabilitySt
ructure] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.hom
参数：e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff`：isRig
htDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F
) : Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartE…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.hasRightRe
solutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, 
u₁} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
-/
instance guitartExact_of_isRightDerivabilityStructure' [h : Φ.IsRightDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.hom := by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h
/-
**CategoryTheory.LocalizerMorphism.guitartExact_of_isRightDerivabilityStructure*
* 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：guitartExact_of_isRightDerivabilityStructure [Φ.IsRightDerivabilityStructu
re] : TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance guitartExact_of_isRightDerivabilityStructure [Φ.IsRightDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).hom :=
  guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasRightResolutions :=
  fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

/-- A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a left derivability
structure if it has left resolutions and the 2-square where the top and bottom functors
are localization functors for `W₁` and `W₂` is Guitart exact. -/
/-
**CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure** 是 Mathlib 中的一个类
，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：IsLeftDerivabilityStructure : Prop where hasLeftResolutions : Φ.HasLeftRes
olutions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A localizer morphism `Φ : LocalizerMorphism W₁ W₂` is a left derivability
structure if it has left resolutions and the 2-square where the top and bottom f
unctors
are localization functors for `W₁` and `W₂` is Guitart exact.
-/
class IsLeftDerivabilityStructure : Prop where
  hasLeftResolutions : Φ.HasLeftResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isLeftDerivabilityStructure` instead,
  see also the lemma `isLeftDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv

attribute [instance] IsLeftDerivabilityStructure.hasLeftResolutions
  IsLeftDerivabilityStructure.guitartExact'
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_op** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_iff_op : Φ.IsLeftDerivabilityStructure ↔ Φ.op.
IsRightDerivabilityStructure
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff`：isRig
htDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F
) : Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartE…
· 使用定理 `CategoryTheory.LocalizerMorphism.instHasRightResolutionsOppositeOpOpOfHa
sLeftResolutions`：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用引理 `CategoryTheory.LocalizerMorphism.hasLeftResolutions_iff_op`：hasLeftResol
utions_iff_op : Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions
· 使用定理 `CategoryTheory.LocalizerMorphism.IsRightDerivabilityStructure.hasRightRe
solutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, 
u₁} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isLeftDerivabilityStructure_iff_op :
    Φ.IsLeftDerivabilityStructure ↔
      Φ.op.IsRightDerivabilityStructure := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.hom ↔ TwoSquare.GuitartExact e.inv :=
    TwoSquare.guitartExact_op_iff _
  constructor
  · rintro ⟨_, _⟩
    rwa [Φ.op.isRightDerivabilityStructure_iff _ _ _ e', eq]
  · intro
    have : Φ.HasLeftResolutions := by
      rw [hasLeftResolutions_iff_op]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [← eq]
    exact Φ.op.guitartExact_of_isRightDerivabilityStructure' _ _ _ e'
/-
**CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLeftDerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂
 ≅ L₁ ⋙ F) : Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExact e.inv
参数：e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff_op`：isL
eftDerivabilityStructure_iff_op : Φ.IsLeftDerivabilityStructure ↔ Φ.op.IsRightDe
rivabilityStructure
· 使用引理 `CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff`：isRig
htDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F
) : Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartE…
· 使用定理 `CategoryTheory.Functor.IsLocalization.op`：∀ {C : Type u_1} {D : Type u_2
} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instHasRightResolutionsOppositeOpOpOfHa
sLeftResolutions`：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftDerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExact e.inv := by
  rw [isLeftDerivabilityStructure_iff_op,
    Φ.op.isRightDerivabilityStructure_iff L₁.op L₂.op F.op (NatIso.op e.symm),
    ← TwoSquare.guitartExact_op_iff e.inv]
  rfl
/-
**CategoryTheory.LocalizerMorphism.guitartExact_of_isLeftDerivabilityStructure'*
* 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：guitartExact_of_isLeftDerivabilityStructure' [h : Φ.IsLeftDerivabilityStru
cture] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.inv
参数：e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff`：isLeft
DerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
 Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExac…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftReso
lutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁
} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
-/
instance guitartExact_of_isLeftDerivabilityStructure' [h : Φ.IsLeftDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.inv := by
  simpa only [Φ.isLeftDerivabilityStructure_iff L₁ L₂ F e] using h
/-
**CategoryTheory.LocalizerMorphism.guitartExact_of_isLeftDerivabilityStructure**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：guitartExact_of_isLeftDerivabilityStructure [Φ.IsLeftDerivabilityStructure
] : TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance guitartExact_of_isLeftDerivabilityStructure [Φ.IsLeftDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).inv :=
  guitartExact_of_isLeftDerivabilityStructure' _ _ _ _ _
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasLeftResolutions :=
  fun X₂ => ⟨LeftResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsLeftDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isLeftDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id' W₁.Q
/-
**CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_iff_op** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isRightDerivabilityStructure_iff_op : Φ.IsRightDerivabilityStructure ↔ Φ.o
p.IsLeftDerivabilityStructure
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_iff`：isLeft
DerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
 Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExac…
· 使用定理 `CategoryTheory.LocalizerMorphism.instHasLeftResolutionsOppositeOpOpOfHas
RightResolutions`：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_iff_op`：hasRightRes
olutions_iff_op : Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftReso
lutions`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁
} C₁}   {inst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isRightDerivabilityStructure_iff_op :
    Φ.IsRightDerivabilityStructure ↔
      Φ.op.IsLeftDerivabilityStructure := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.inv ↔ TwoSquare.GuitartExact e.hom :=
    TwoSquare.guitartExact_op_iff _
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun _ ↦ ?_⟩
  · simpa only [Φ.op.isLeftDerivabilityStructure_iff _ _ _ e', eq]
  · have : Φ.HasRightResolutions := by
      rw [hasRightResolutions_iff_op]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [← eq]
    exact Φ.op.guitartExact_of_isLeftDerivabilityStructure' _ _ _ e'
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLeftDerivabilityStructure] : Φ.op.IsRightDerivabilityStructure := by
  rwa [← isLeftDerivabilityStructure_iff_op]
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsRightDerivabilityStructure] : Φ.op.IsLeftDerivabilityStructure := by
  rwa [← isRightDerivabilityStructure_iff_op]

end LocalizerMorphism

end CategoryTheory

