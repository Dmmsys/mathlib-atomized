/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Transformations between lax functors

Just as there are natural transformations between functors, there are transformations
between lax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
lax functors):
* lax natural transformations;
* oplax natural transformations;
* strong natural transformations.

These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Lax.LaxTrans F G`: lax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Lax.OplaxTrans F G`: oplax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Lax.StrongTrans F G`: strong transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-isomorphism `app a ≫ G.map f ≅ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define three (scoped) `CategoryStruct` instances on `B ⥤ᴸ C`, in the
`Lax.LaxTrans`, `Lax.OplaxTrans`, and `Lax.StrongTrans` namespaces. The arrows in these
`CategoryStruct` instances are given by lax transformations, oplax transformations, and strong
transformations respectively.

We also provide API for going between lax transformations and strong transformations:
* `LaxTrans.StrongCore η`: a structure on a lax transformation between lax functors that
  promotes it to a strong transformation.
* `StrongTrans.mkOfLax η η'`: given a lax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfLax` gives the corresponding strong transformation.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
  section 4.2.

-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- If `η` is a lax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Lax.LaxTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Lax`。
形式化陈述：LaxTrans (F G : B ⥤ᴸ C) where /-- The component 1-morphisms of a lax trans
formation. -/ app (a : B) : F.obj a ⟶ G.obj a /-- The 2-morphisms underlying the
 lax naturality constraint. -/ naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map 
f ⟶ F.map f ≫ app b /-- Naturality of the lax naturality constraint. -/ naturali
ty_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : naturality f ≫ F.map₂ η ▷ ap
p b = app a ◁ G.map₂ η ≫ naturality g
参数：F G : B ⥤ᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η` is a lax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism `f : a 
⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities 
and
the compositions modulo some adjustments of domains and codomains of 2-morphisms
.
-/
structure LaxTrans (F G : B ⥤ᴸ C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  /-- Naturality of the lax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    cat_disch
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ naturality (𝟙 a) =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv ≫ F.mapId a ▷ app a := by
    cat_disch
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ naturality (f ≫ g) =
      (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    cat_disch

attribute [reassoc (attr := simp)] LaxTrans.naturality_naturality LaxTrans.naturality_id
  LaxTrans.naturality_comp

namespace LaxTrans

variable {F G H : B ⥤ᴸ C} (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
/-- The identity lax transformation. -/
/-
**CategoryTheory.Lax.LaxTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lax.L
axTrans`。
形式化陈述：id : LaxTrans F F where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity lax transformation.
-/
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv
/-
**CategoryTheory.Lax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.Lax
Trans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LaxTrans F F) :=
  ⟨id F⟩

/-- Auxiliary definition for `vComp`. -/
/-
**CategoryTheory.Lax.LaxTrans.vCompApp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Lax.LaxTrans`。
形式化陈述：vCompApp (a : B) : F.obj a ⟶ H.obj a
参数：a : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `vComp`.
-/
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a :=
  η.app a ≫ θ.app a

/-- Auxiliary definition for `vComp`. -/
/-
**CategoryTheory.Lax.LaxTrans.vCompNaturality** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Lax.LaxTrans`。
形式化陈述：vCompNaturality {a b : B} (f : a ⟶ b) : (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.
map f ≫ η.app b ≫ θ.app b
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `vComp`.
-/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.map f ≫ η.app b ≫ θ.app b :=
  (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom
/-
**CategoryTheory.Lax.LaxTrans.vComp_naturality_naturality** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Lax.LaxTrans`。
形式化陈述：vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) : η.vCompN
aturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b = η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompN
aturality θ g
参数：β : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.LaxTrans.naturality_naturality`：∀ {B : Type u₁} [inst
 : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategor
y C]   {F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
-/
theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    η.vCompNaturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b =
      η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompNaturality θ g :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) ⊗≫
          η.naturality g ▷ θ.app b ⊗≫ 𝟙 _ := by
      rw [naturality_naturality]
      bicategory
    _ = _ := by
      rw [naturality_naturality]
      bicategory
/-
**CategoryTheory.Lax.LaxTrans.vComp_naturality_id** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Lax.LaxTrans`。
形式化陈述：vComp_naturality_id (a : B) : η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturali
ty θ (𝟙 a) = (ρ_ (η.vCompApp θ a)).hom ≫ (fun_ (η.vCompApp θ a)).inv ≫ F.mapId a
 ▷ η.vCompApp θ a
参数：a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.LaxTrans.naturality_id`：∀ {B : Type u₁} [inst : Categ
oryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   {
F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
-/
theorem vComp_naturality_id (a : B) :
    η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturality θ (𝟙 a) =
      (ρ_ (η.vCompApp θ a)).hom ≫ (λ_ (η.vCompApp θ a)).inv ≫ F.mapId a ▷ η.vCompApp θ a :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) ⊗≫
          η.naturality (𝟙 a) ▷ θ.app a ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a ⊗≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ = _ := by
      rw [naturality_id]
      bicategory
/-
**CategoryTheory.Lax.LaxTrans.vComp_naturality_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Lax.LaxTrans`。
形式化陈述：vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : η.vCompApp θ a
 ◁ H.mapComp f g ≫ η.vCompNaturality θ (f ≫ g) = (α_ (η.vCompApp θ a) (H.map f) 
(H.map g)).inv ≫ η.vCompNaturality θ f ▷ H.map g ≫ (α_ (F.map f) (η.vCompApp θ b
) (H.map g)).hom ≫ F.map f ◁ η.vCompNaturality θ g ≫ (α_ (F.map f) (F.map g) (η.
vCompApp θ c)).inv ≫ F.mapComp f g ▷ η.vCompApp θ c
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.LaxTrans.naturality_comp`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 {F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompApp θ a ◁ H.mapComp f g ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
        η.vCompNaturality θ f ▷ H.map g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
            F.map f ◁ η.vCompNaturality θ g ≫
              (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv ≫ F.mapComp f g ▷ η.vCompApp θ c :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) ⊗≫
          η.naturality (f ≫ g) ▷ θ.app c ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ▷ (H.map g) ⊗≫ G.map f ◁ θ.naturality g) ⊗≫
          (η.app a ◁ G.mapComp f g ≫ η.naturality (f ≫ g)) ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp θ]
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ▷ H.map g ⊗≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) ⊗≫
            F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
              F.mapComp f g ▷ η.app c ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [naturality_comp η]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

/-- Vertical composition of lax transformations. -/
/-
**CategoryTheory.Lax.LaxTrans.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.La
x.LaxTrans`。
形式化陈述：vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where app a
参数：η : LaxTrans F G；θ : LaxTrans G H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Lax.LaxTrans.vComp_naturality_naturality`：vComp_naturalit
y_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) : η.vCompNaturality θ f ≫ F.map
₂ β ▷ η.vCompApp θ b = η.vCompApp θ a ◁ H.map…
· 使用定理 `CategoryTheory.Lax.LaxTrans.vComp_naturality_id`：vComp_naturality_id (a 
: B) : η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturality θ (𝟙 a) = (ρ_ (η.vCompApp 
θ a)).hom ≫ (fun_ (η.vCompApp θ a)).i…
· 使用定理 `CategoryTheory.Lax.LaxTrans.vComp_naturality_comp`：vComp_naturality_comp
 {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : η.vCompApp θ a ◁ H.mapComp f g ≫ η.vCompN
aturality θ (f ≫ g) = (α_ (η.vCompApp θ…

--- 原说明 ---
Vertical composition of lax transformations.
-/
def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Lax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.Lax
Trans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by lax
transformations.
-/
scoped instance : CategoryStruct (B ⥤ᴸ C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

@[deprecated (since := "2026-03-16")] alias vComp_app := comp_app
@[deprecated (since := "2026-03-16")] alias vComp_naturality := comp_naturality

end LaxTrans

/-- If `η` is an oplax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Lax.OplaxTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Lax`。
形式化陈述：OplaxTrans (F G : B ⥤ᴸ C) where /-- The component 1-morphisms of an oplax 
transformation. -/ app (a : B) : F.obj a ⟶ G.obj a /-- The 2-morphisms underlyin
g the oplax naturality constraint. -/ naturality {a b : B} (f : a ⟶ b) : F.map f
 ≫ app b ⟶ app a ≫ G.map f /-- Naturality of the oplax naturality constraint. -/
 naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : F.map₂ η ▷ app b ≫ 
naturality g = naturality f ≫ app a ◁ G.map₂ η
参数：F G : B ⥤ᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η` is an oplax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a 
⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities 
and
the compositions modulo some adjustments of domains and codomains of 2-morphisms
.
-/
structure OplaxTrans (F G : B ⥤ᴸ C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality of the oplax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      F.mapId a ▷ app a ≫ naturality (𝟙 a) =
        (λ_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      F.mapComp f g ▷ app c ≫ naturality (f ≫ g) =
        (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            app a ◁ G.mapComp f g := by
    cat_disch

namespace OplaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : B ⥤ᴸ C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

variable (F) in
/-- The identity oplax transformation. -/
/-
**CategoryTheory.Lax.OplaxTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lax
.OplaxTrans`。
形式化陈述：id : OplaxTrans F F where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity oplax transformation.
-/
def id : OplaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv
/-
**CategoryTheory.Lax.OplaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.O
plaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OplaxTrans F F) :=
  ⟨id F⟩

/-- Auxiliary definition for `vComp`. -/
/-
**CategoryTheory.Lax.OplaxTrans.vCompApp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Lax.OplaxTrans`。
形式化陈述：vCompApp (a : B) : F.obj a ⟶ H.obj a
参数：a : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `vComp`.
-/
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a := η.app a ≫ θ.app a

/-- Auxiliary definition for `vComp`. -/
/-
**CategoryTheory.Lax.OplaxTrans.vCompNaturality** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Lax.OplaxTrans`。
形式化陈述：vCompNaturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≫ θ.app b ⟶ (η.a
pp a ≫ θ.app a) ≫ H.map f
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `vComp`.
-/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    F.map f ≫ η.app b ≫ θ.app b ⟶ (η.app a ≫ θ.app a) ≫ H.map f :=
  (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
    η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
/-
**CategoryTheory.Lax.OplaxTrans.vComp_naturality_naturality** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Lax.OplaxTrans`。
形式化陈述：vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) : F.map₂ β
 ▷ η.vCompApp θ b ≫ η.vCompNaturality θ g = η.vCompNaturality θ f ≫ η.vCompApp θ
 a ◁ H.map₂ β
参数：β : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.OplaxTrans.naturality_naturality`：∀ {B : Type u₁} [in
st : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicateg
ory C]   {F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
-/
theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    F.map₂ β ▷ η.vCompApp θ b ≫ η.vCompNaturality θ g =
      η.vCompNaturality θ f ≫ η.vCompApp θ a ◁ H.map₂ β := by
  calc
    _ = 𝟙 _ ⊗≫ (F.map₂ β ▷ η.app b ≫ η.naturality g) ▷ θ.app b ⊗≫
          η.app a ◁ θ.naturality g ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.naturality f ▷ θ.app b ⊗≫
          η.app a ◁ (G.map₂ β ▷ θ.app b ≫ θ.naturality g) ⊗≫ 𝟙 _ := by
      rw [η.naturality_naturality]
      bicategory
    _ = _ := by
      rw [θ.naturality_naturality]
      bicategory
/-
**CategoryTheory.Lax.OplaxTrans.vComp_naturality_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Lax.OplaxTrans`。
形式化陈述：vComp_naturality_id (a : B) : F.mapId a ▷ η.vCompApp θ a ≫ η.vCompNaturali
ty θ (𝟙 a) = (fun_ (η.vCompApp θ a)).hom ≫ (ρ_ (η.vCompApp θ a)).inv ≫ η.vCompAp
p θ a ◁ H.mapId a
参数：a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.OplaxTrans.naturality_id`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 {F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
-/
theorem vComp_naturality_id (a : B) :
    F.mapId a ▷ η.vCompApp θ a ≫ η.vCompNaturality θ (𝟙 a) =
      (λ_ (η.vCompApp θ a)).hom ≫ (ρ_ (η.vCompApp θ a)).inv ≫ η.vCompApp θ a ◁ H.mapId a := by
  calc
    _ = 𝟙 _ ⊗≫ (F.mapId a ▷ η.app a ≫ η.naturality (𝟙 a)) ▷ θ.app a ⊗≫
          η.app a ◁ θ.naturality (𝟙 a) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (G.mapId a ▷ θ.app a ≫ θ.naturality (𝟙 a)) ⊗≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory
    _ = _ := by
      rw [θ.naturality_id]
      bicategory
/-
**CategoryTheory.Lax.OplaxTrans.vComp_naturality_comp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Lax.OplaxTrans`。
形式化陈述：vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.mapComp f g 
▷ η.vCompApp θ c ≫ η.vCompNaturality θ (f ≫ g) = (α_ (F.map f) (F.map g) (η.vCom
pApp θ c)).hom ≫ F.map f ◁ η.vCompNaturality θ g ≫ (α_ (F.map f) (η.vCompApp θ b
) (H.map g)).inv ≫ η.vCompNaturality θ f ▷ H.map g ≫ (α_ (η.vCompApp θ a) (H.map
 f) (H.map g)).hom ≫ η.vCompApp θ a ◁ H.mapComp f g
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Lax.OplaxTrans.naturality_comp`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   {F G : CategoryTheory.LaxFunctor…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    F.mapComp f g ▷ η.vCompApp θ c ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (F.map f) (F.map g) (η.vCompApp θ c)).hom ≫
        F.map f ◁ η.vCompNaturality θ g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).inv ≫
            η.vCompNaturality θ f ▷ H.map g ≫
              (α_ (η.vCompApp θ a) (H.map f) (H.map g)).hom ≫ η.vCompApp θ a ◁ H.mapComp f g := by
  calc
    _ = 𝟙 _ ⊗≫ (F.mapComp f g ▷ η.app c ≫ η.naturality (f ≫ g)) ▷ θ.app c ⊗≫
          η.app a ◁ θ.naturality (f ≫ g) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (F.map f ◁ η.naturality g ⊗≫ η.naturality f ▷ G.map g) ▷ θ.app c ⊗≫
          η.app a ◁ (G.mapComp f g ▷ θ.app c ≫ θ.naturality (f ≫ g)) ⊗≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ ⊗≫ F.map f ◁ η.naturality g ▷ θ.app c ⊗≫
          (η.naturality f ▷ (G.map g ≫ θ.app c) ≫ (η.app a ≫ G.map f) ◁ θ.naturality g) ⊗≫
            η.app a ◁ (θ.naturality f ▷ H.map g ⊗≫ θ.app a ◁ H.mapComp f g) ⊗≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

/-- Vertical composition of oplax transformations. -/
/-
**CategoryTheory.Lax.OplaxTrans.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Lax.OplaxTrans`。
形式化陈述：vComp (η : OplaxTrans F G) (θ : OplaxTrans G H) : OplaxTrans F H where app
参数：η : OplaxTrans F G；θ : OplaxTrans G H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Lax.OplaxTrans.vComp_naturality_naturality`：vComp_natural
ity_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) : F.map₂ β ▷ η.vCompApp θ b ≫
 η.vCompNaturality θ g = η.vCompNaturality θ f …
· 使用定理 `CategoryTheory.Lax.OplaxTrans.vComp_naturality_id`：vComp_naturality_id (
a : B) : F.mapId a ▷ η.vCompApp θ a ≫ η.vCompNaturality θ (𝟙 a) = (fun_ (η.vComp
App θ a)).hom ≫ (ρ_ (η.vCompApp θ a)).i…
· 使用定理 `CategoryTheory.Lax.OplaxTrans.vComp_naturality_comp`：vComp_naturality_co
mp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.mapComp f g ▷ η.vCompApp θ c ≫ η.vCom
pNaturality θ (f ≫ g) = (α_ (F.map f) (F.…

--- 原说明 ---
Vertical composition of oplax transformations.
-/
def vComp (η : OplaxTrans F G) (θ : OplaxTrans G H) : OplaxTrans F H where
  app := vCompApp η θ
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Lax.OplaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.O
plaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by oplax
transformations.
-/
scoped instance : CategoryStruct (B ⥤ᴸ C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vComp

end OplaxTrans

/-- A strong natural transformation between lax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : app a ≫ G.map f ≅ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Lax.StrongTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Lax`。
形式化陈述：StrongTrans (F G : B ⥤ᴸ C) where app (a : B) : F.obj a ⟶ G.obj a naturalit
y {a b : B} (f : a ⟶ b) : app a ≫ G.map f ≅ F.map f ≫ app b naturality_naturalit
y {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : (naturality f).hom ≫ F.map₂ η ▷ app b = 
app a ◁ G.map₂ η ≫ (naturality g).hom
参数：F G : B ⥤ᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong natural transformation between lax functors `F` and `G` is a natural tr
ansformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : app a ≫ G.map f ≅ F.map f ≫ app b` for each 
1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identi
ties and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : B ⥤ᴸ C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ≅ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      (naturality f).hom ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ (naturality g).hom := by
    cat_disch
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ (naturality (𝟙 a)).hom =
        (ρ_ (app a)).hom ≫ (λ_ (app a)).inv ≫ F.mapId a ▷ app a := by
    cat_disch
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ (naturality (f ≫ g)).hom =
      (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    cat_disch

attribute [nolint docBlame] CategoryTheory.Lax.StrongTrans.app
  CategoryTheory.Lax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/-- A structure on a lax transformation that promotes it to a strong transformation.

See `StrongTrans.mkOfLax`. -/
/-
**CategoryTheory.Lax.LaxTrans.StrongCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Lax.LaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
LaxFunctor B C} → (F ⟶ G) → Type (max (max u₁ v₁) w₂)
参数：F ⟶ G；max (max u₁ v₁) w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure on a lax transformation that promotes it to a strong transformation.

See `StrongTrans.mkOfLax`.
-/
structure LaxTrans.StrongCore {F G : B ⥤ᴸ C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : η.app a ≫ G.map f ≅ F.map f ≫ η.app b
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the lax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by cat_disch

attribute [simp] LaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying lax natural transformation of a strong natural transformation. -/
@[simps]
/-
**CategoryTheory.Lax.StrongTrans.toLax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Lax.StrongTrans`。
形式化陈述：toLax {F G : B ⥤ᴸ C} (η : StrongTrans F G) : LaxTrans F G where app
参数：η : StrongTrans F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying lax natural transformation of a strong natural transformation.
-/
def toLax {F G : B ⥤ᴸ C} (η : StrongTrans F G) : LaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from a lax natural transformation whose
naturality 2-morphism is an isomorphism. -/
/-
**CategoryTheory.Lax.StrongTrans.mkOfLax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Lax.StrongTrans`。
形式化陈述：mkOfLax {F G : B ⥤ᴸ C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η) : S
trongTrans F G where app
参数：η : LaxTrans F G；η' : LaxTrans.StrongCore η。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a strong natural transformation from a lax natural transformation whos
e
naturality 2-morphism is an isomorphism.
-/
def mkOfLax {F G : B ⥤ᴸ C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from a lax natural transformation whose
naturality 2-morphism is an isomorphism. -/
/-
**CategoryTheory.Lax.StrongTrans.mkOfLax'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Lax.StrongTrans`。
形式化陈述：mkOfLax' {F G : B ⥤ᴸ C} (η : LaxTrans F G) [forall a b (f : a ⟶ b), IsIso 
(η.naturality f)] : StrongTrans F G where app
参数：η : LaxTrans F G；f : a ⟶ b；η.naturality f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a strong natural transformation from a lax natural transformation whos
e
naturality 2-morphism is an isomorphism.
-/
noncomputable def mkOfLax' {F G : B ⥤ᴸ C} (η : LaxTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : B ⥤ᴸ C)

/-- The identity strong natural transformation. -/
@[simps!]
/-
**CategoryTheory.Lax.StrongTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.La
x.StrongTrans`。
形式化陈述：id : StrongTrans F F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity strong natural transformation.
-/
def id : StrongTrans F F :=
  mkOfLax (LaxTrans.id F) { naturality := fun f ↦ (λ_ (F.map f)) ≪≫ (ρ_ (F.map f)).symm }

@[simp]
/-
**CategoryTheory.Lax.StrongTrans.id.toLax** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Lax.StrongTrans.id`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.LaxFunctor B C), (Category
Theory.Lax.StrongTrans.id F).toLax = CategoryTheory.Lax.LaxTrans.id F
参数：F : CategoryTheory.LaxFunctor B C；CategoryTheory.Lax.StrongTrans.id F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id.toLax : (id F).toLax = LaxTrans.id F :=
  rfl
/-
**CategoryTheory.Lax.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lax.
StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

variable {F} {G H : B ⥤ᴸ C} (η : StrongTrans F G) (θ : StrongTrans G H)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Vertical composition of strong natural transformations. -/
@[simps!]
/-
**CategoryTheory.Lax.StrongTrans.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Lax.StrongTrans`。
形式化陈述：vComp : StrongTrans F H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of strong natural transformations.
-/
def vComp : StrongTrans F H :=
  mkOfLax (LaxTrans.vComp η.toLax θ.toLax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Lax.StrongTrans.categoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Lax.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         CategoryTheory.Categor
yStruct.{max (max (max u₁ v₁) v₂) w₂, max (max (max (max (max u₂ u₁) v₂) v₁) w₂)
 w₁}           (CategoryTheory.LaxFunctor B C)
参数：max (max u₁ v₁) v₂；max (max (max (max u₂ u₁) v₂) v₁) w₂；CategoryTheory.LaxFun
ctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by strong
transformations.
-/
scoped instance categoryStruct : CategoryStruct (B ⥤ᴸ C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vComp

end StrongTrans

end CategoryTheory.Lax

