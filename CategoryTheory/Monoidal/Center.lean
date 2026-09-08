/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `Center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `Center C` is braided monoidal,
and provide the monoidal functor `Center.forget` from `Center C` back to `C`.

## Implementation notes

Verifying the various axioms directly requires tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial).
3. Automating these proofs using `rewrite_search` or some relative.

In this file, we take the second approach using the monoidal composition `⊗≫` and the
`coherence` tactic.
-/

@[expose] public section


universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
/-
**CategoryTheory.HalfBraiding** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：HalfBraiding (X : C) where /-- The family of isomorphisms `X ⊗ U ≅ U ⊗ X` 
-/ β : forall U, X otimes U ≅ U otimes X monoidal : forall U U', (β (U otimes U'
)).hom = (α_ _ _ _).inv ≫ ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫
 (α_ _ _ _).inv
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same a
s natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which s
end the unique
`0`-morphism to `X`.
-/
structure HalfBraiding (X : C) where
  /-- The family of isomorphisms `X ⊗ U ≅ U ⊗ X` -/
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal : ∀ U U', (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫
        ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv := by
    cat_disch
  naturality : ∀ {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X) := by
    cat_disch

attribute [reassoc, simp] HalfBraiding.monoidal -- the reassoc lemma is redundant as a simp lemma

attribute [simp, reassoc] HalfBraiding.naturality

variable (C)

/-- The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
/-
**CategoryTheory.Center** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Center
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, wh
ere `X : C`
and `b` is a half-braiding on `X`.
-/
def Center :=
  Σ X : C, HalfBraiding X

namespace Center

variable {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext]
/-
**CategoryTheory.Center.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Center`。
形式化陈述：Hom (X Y : Center C) where /-- The underlying morphism between the first c
omponents of the objects involved -/ f : X.1 ⟶ Y.1 comm : forall U, (f ▷ U) ≫ (Y
.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f)
参数：X Y : Center C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the Drinfeld center of `C`.
-/
structure Hom (X Y : Center C) where
  /-- The underlying morphism between the first components of the objects involved -/
  f : X.1 ⟶ Y.1
  comm : ∀ U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Center C) where
  Hom := Hom

@[ext]
/-
**CategoryTheory.Center.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Center`。
形式化陈述：ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g
参数：f g : X ⟶ Y；w : f.f = g.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by
  cases f; cases g; congr
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Center C) where
  id X := { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]
/-
**CategoryTheory.Center.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Center`。
形式化陈述：id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1
参数：X : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl

@[simp]
/-
**CategoryTheory.Center.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Center`
。
形式化陈述：comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
/-
**CategoryTheory.Center.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Center`。
形式化陈述：isoMk {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where hom
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
def isoMk {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv := ⟨inv f.f,
    fun U => by simp [← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp] ⟩
/-
**CategoryTheory.Center.isIso_of_f_isIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  change IsIso (isoMk f).hom
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/-
**CategoryTheory.Center.tensorObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cent
er`。
形式化陈述：tensorObj (X Y : Center C) : Center C
参数：X Y : Center C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def tensorObj (X Y : Center C) : Center C :=
  ⟨X.1 ⊗ Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        simp only [HalfBraiding.monoidal]
        -- We'd like to commute `X.1 ◁ U ◁ (HalfBraiding.β Y.2 U').hom`
        -- and `((HalfBraiding.β X.2 U).hom ▷ U' ▷ Y.1)` past each other.
        -- We do this with the help of the monoidal composition `⊗≫` and the `coherence` tactic.
        calc
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ▷ U' ⊗≫
              (_ ◁ (HalfBraiding.β Y.2 U').hom ≫
                (HalfBraiding.β X.2 U).hom ▷ _) ⊗≫
                  U ◁ (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = _ := by rw [whisker_exchange]; monoidal
      naturality := fun {U U'} f => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        calc
          _ = 𝟙 _ ⊗≫
            (X.1 ◁ (Y.1 ◁ f ≫ (HalfBraiding.β Y.2 U').hom)) ⊗≫
              (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ⊗≫
              (X.1 ◁ f ≫ (HalfBraiding.β X.2 U').hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
            rw [HalfBraiding.naturality]; monoidal
          _ = _ := by rw [HalfBraiding.naturality]; monoidal }⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Center.whiskerLeft_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：whiskerLeft_comm (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) :
 (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U).hom = ((tensorObj X Y₁).2.β U).hom ≫
 U ◁ X.1 ◁ f.f
参数：X : Center C；f : Y₁ ⟶ Y₂；U : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Center.Hom.comm`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {X Y : Catego
ryTheory.Center C} (…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem whiskerLeft_comm (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) :
    (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U).hom =
      ((tensorObj X Y₁).2.β U).hom ≫ U ◁ X.1 ◁ f.f := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) ⊗≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (HalfBraiding.β Y₁.snd U).hom ⊗≫
        ((X.fst ⊗ U) ◁ f.f ≫ (HalfBraiding.β X.snd U).hom ▷ Y₂.fst) ⊗≫ 𝟙 _ := by
      rw [f.comm]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
/-
**CategoryTheory.Center.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ce
nter`。
形式化陈述：whiskerLeft (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : tensorObj X 
Y₁ ⟶ tensorObj X Y₂ where f
参数：X : Center C；f : Y₁ ⟶ Y₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Center.whiskerLeft_comm`：whiskerLeft_comm (X : Center C) 
{Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) : (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2
.β U).hom = ((tensorObj X Y₁…

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def whiskerLeft (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below.
@[reassoc]
/-
**CategoryTheory.Center.whiskerRight_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Center`。
形式化陈述：whiskerRight_comm {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) 
: f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U).hom = ((tensorObj X₁ Y).2.β U).hom ≫ 
U ◁ f.f ▷ Y.1
参数：f : X₁ ⟶ X₂；Y : Center C；U : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.Center.Hom.comm`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {X Y : Catego
ryTheory.Center C} (…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
-/
theorem whiskerRight_comm {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) :
    f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U).hom =
      ((tensorObj X₁ Y).2.β U).hom ≫ U ◁ f.f ▷ Y.1 := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      (f.f ▷ (Y.fst ⊗ U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) ⊗≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X₁.fst ◁ (HalfBraiding.β Y.snd U).hom ⊗≫
        (f.f ▷ U ≫ (HalfBraiding.β X₂.snd U).hom) ▷ Y.fst ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
/-
**CategoryTheory.Center.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
enter`。
形式化陈述：whiskerRight {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : tensorObj X
₁ Y ⟶ tensorObj X₂ Y where f
参数：f : X₁ ⟶ X₂；Y : Center C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Center.whiskerRight_comm`：whiskerRight_comm {X₁ X₂ : Cent
er C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) : f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2
.β U).hom = ((tensorObj X₁ Y)…

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def whiskerRight {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/-
**CategoryTheory.Center.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cent
er`。
形式化陈述：tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj
 X₁ X₂ ⟶ tensorObj Y₁ Y₂ where f
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ₘ g.f
  comm U := by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
      MonoidalCategory.whiskerLeft_comp]

section

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
/-
**CategoryTheory.Center.tensorUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cen
ter`。
形式化陈述：tensorUnit : Center C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def tensorUnit : Center C :=
  ⟨𝟙_ C, { β := fun U => λ_ U ≪≫ (ρ_ U).symm }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
/-
**CategoryTheory.Center.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cen
ter`。
形式化陈述：associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X 
(tensorObj Y Z)
参数：X Y Z : Center C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk ⟨(α_ X.1 Y.1 Z.1).hom, fun U => by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
/-
**CategoryTheory.Center.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cen
ter`。
形式化陈述：leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X
参数：X : Center C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X :=
  isoMk ⟨(λ_ X.1).hom, fun U => by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
/-
**CategoryTheory.Center.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ce
nter`。
形式化陈述：rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X
参数：X : Center C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `MonoidalCategory` instance on `Center C`.
-/
def rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X :=
  isoMk ⟨(ρ_ X.1).hom, fun U => by simp⟩

end

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] Center.associator Center.leftUnitor Center.rightUnitor

attribute [local simp] Center.whiskerLeft Center.whiskerRight Center.tensorHom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory (Center C) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.tensor_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cen
ter`。
形式化陈述：tensor_fst (X Y : Center C) : (X otimes Y).1 = X.1 otimes Y.1
参数：X Y : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_fst (X Y : Center C) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.tensor_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Center
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_β (X Y : Center C) (U : C) :
    (X ⊗ Y).2.β U =
      α_ _ _ _ ≪≫
        (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
          (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.whiskerLeft_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Center`。
形式化陈述：whiskerLeft_f (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : (X ◁ f).f 
= X.1 ◁ f.f
参数：X : Center C；f : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_f (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : (X ◁ f).f = X.1 ◁ f.f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.whiskerRight_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Center`。
形式化陈述：whiskerRight_f {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : (f ▷ Y).f
 = f.f ▷ Y.1
参数：f : X₁ ⟶ X₂；Y : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_f {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.tensor_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cente
r`。
形式化陈述：tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f otimesₘ
 g).f = f.f otimesₘ g.f
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.tensorUnit_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ce
nter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorUnit_β (U : C) : (𝟙_ (Center C)).2.β U = λ_ U ≪≫ (ρ_ U).symm :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.associator_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z
.1).hom
参数：X Y Z : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.associator_inv_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z
.1).inv
参数：X Y Z : Center C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_ext'`：inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_i
d : f.hom ≫ g = 𝟙 X) : g = f.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Center.associator_hom_f`：associator_hom_f (X Y Z : Center
 C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom
· 使用定理 `CategoryTheory.Center.comp_f`：comp_f {X Y Z : Center C} (f : X ⟶ Y) (g :
 Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.leftUnitor_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：leftUnitor_hom_f (X : Center C) : Hom.f (fun_ X).hom = (fun_ X.1).hom
参数：X : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_hom_f (X : Center C) : Hom.f (λ_ X).hom = (λ_ X.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.leftUnitor_inv_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Center`。
形式化陈述：leftUnitor_inv_f (X : Center C) : Hom.f (fun_ X).inv = (fun_ X.1).inv
参数：X : Center C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_ext'`：inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_i
d : f.hom ≫ g = 𝟙 X) : g = f.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Center.leftUnitor_hom_f`：leftUnitor_hom_f (X : Center C) 
: Hom.f (fun_ X).hom = (fun_ X.1).hom
· 使用定理 `CategoryTheory.Center.comp_f`：comp_f {X Y Z : Center C} (f : X ⟶ Y) (g :
 Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem leftUnitor_inv_f (X : Center C) : Hom.f (λ_ X).inv = (λ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.rightUnitor_hom_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Center`。
形式化陈述：rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom
参数：X : Center C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Center.rightUnitor_inv_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Center`。
形式化陈述：rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv
参数：X : Center C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_ext'`：inv_ext' {f : X ≅ Y} {g : Y ⟶ X} (hom_inv_i
d : f.hom ≫ g = 𝟙 X) : g = f.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Center.rightUnitor_hom_f`：rightUnitor_hom_f (X : Center C
) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom
· 使用定理 `CategoryTheory.Center.comp_f`：comp_f {X Y Z : Center C} (f : X ⟶ Y) (g :
 Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

end

section

variable (C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
/-
**CategoryTheory.Center.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Center`
。
形式化陈述：forget : Center C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful monoidal functor from the Drinfeld center to the original category
.
-/
def forget : Center C ⥤ C where
  obj X := X.1
  map f := f.f

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Center
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_ε : ε (forget C) = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Center
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_η : η (forget C) = 𝟙 _ := rfl

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Center
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_μ (X Y : Center C) : μ (forget C) X Y = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Center
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_δ (X Y : Center C) : δ (forget C) X Y = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f i := by dsimp at i; change IsIso (isoMk f).hom; infer_instance

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `BraidedCategory` instance on `Center C`. -/
@[simps!]
/-
**CategoryTheory.Center.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cente
r`。
形式化陈述：braiding (X Y : Center C) : X otimes Y ≅ Y otimes X
参数：X Y : Center C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `BraidedCategory` instance on `Center C`.
-/
def braiding (X Y : Center C) : X ⊗ Y ≅ Y ⊗ X :=
  isoMk
    ⟨(X.2.β Y.1).hom, fun U => by
      dsimp
      simp only [Category.assoc]
      rw [← IsIso.inv_comp_eq, IsIso.Iso.inv_hom, ← HalfBraiding.monoidal_assoc,
        ← HalfBraiding.naturality_assoc, HalfBraiding.monoidal]
      simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.braidedCategoryCenter** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Center`。
形式化陈述：braidedCategoryCenter : BraidedCategory (Center C) where braiding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance braidedCategoryCenter : BraidedCategory (Center C) where
  braiding := braiding

-- `cat_disch` handles the hexagon axioms
section

variable [BraidedCategory C]

open BraidedCategory

/-- Auxiliary construction for `ofBraided`. -/
@[simps]
/-
**CategoryTheory.Center.ofBraidedObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
enter`。
形式化陈述：ofBraidedObj (X : C) : Center C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for `ofBraided`.
-/
def ofBraidedObj (X : C) : Center C :=
  ⟨X, { β := fun Y => β_ X Y}⟩

variable (C)

/-- The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
/-
**CategoryTheory.Center.ofBraided** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cent
er`。
形式化陈述：ofBraided : C ⥤ Center C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C}   [self : CategoryTheory.BraidedCatego…

--- 原说明 ---
The functor lifting a braided category to its center, using the braiding as the 
half-braiding.
-/
def ofBraided : C ⥤ Center C where
  obj := ofBraidedObj
  map f :=
    { f
      comm := fun U => braiding_naturality_left f U }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Center.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Center`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ofBraided C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } }
      μIso := fun _ _ ↦
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } } }

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.ofBraided_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cen
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofBraided_ε_f : (ε (ofBraided C)).f = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.ofBraided_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cen
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofBraided_η_f : (η (ofBraided C)).f = 𝟙 _ := rfl

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.ofBraided_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cen
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofBraided_μ_f (X Y : C) : (μ (ofBraided C) X Y).f = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Center.ofBraided_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cen
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofBraided_δ_f (X Y : C) : (δ (ofBraided C) X Y).f = 𝟙 _ := rfl

end

end Center

end CategoryTheory

