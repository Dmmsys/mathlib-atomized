/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Transformations between oplax functors

Just as there are natural transformations between functors, there are transformations
between oplax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
oplax functors):
* oplax natural transformations;
* lax natural transformations;
* strong natural transformations.

These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Oplax.LaxTrans F G`: lax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.OplaxTrans F G`: oplax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.StrongTrans F G`: strong transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-isomorphism `F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define three (scoped) `CategoryStruct` instances on `B ⥤ᵒᵖᴸ C`, in the
`Oplax.LaxTrans`, `Oplax.OplaxTrans`, and `Oplax.StrongTrans` namespaces. The arrows in these
`CategoryStruct` instances are given by lax transformations, oplax transformations, and strong
transformations respectively.

We also provide API for going between oplax transformations and strong transformations:
* `OplaxTrans.StrongCore η`: a structure on an oplax transformation between oplax functors that
  promotes it to a strong transformation.
* `StrongTrans.mkOfOplax η η'`: given an oplax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfOplax` gives the corresponding strong transformation.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

@[expose] public section

namespace CategoryTheory.Oplax

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
**CategoryTheory.Oplax.LaxTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Oplax`
。
形式化陈述：LaxTrans (F G : OplaxFunctor B C) where /-- The component 1-morphisms of a
 lax transformation. -/ app (a : B) : F.obj a ⟶ G.obj a /-- The 2-morphisms unde
rlying the lax naturality constraint. -/ naturality {a b : B} (f : a ⟶ b) : app 
a ≫ G.map f ⟶ F.map f ≫ app b naturality_naturality {a b : B} {f g : a ⟶ b} (η :
 f ⟶ g) : naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g
参数：F G : OplaxFunctor B C；a : B。
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
structure LaxTrans (F G : OplaxFunctor B C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    cat_disch
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ F.mapId a ▷ app a =
        app a ◁ G.mapId a ≫ (ρ_ (app a)).hom ≫ (λ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ F.mapComp f g ▷ app c =
        app a ◁ G.mapComp f g ≫ (α_ _ _ _).inv ≫
          naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv := by
    cat_disch

namespace LaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : OplaxFunctor B C}
variable (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
/-- The identity lax transformation. -/
/-
**CategoryTheory.Oplax.LaxTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Opl
ax.LaxTrans`。
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
**CategoryTheory.Oplax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Oplax
.LaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LaxTrans F F) :=
  ⟨id F⟩

/-- Auxiliary definition for `vComp`. -/
/-
**CategoryTheory.Oplax.LaxTrans.vCompApp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Oplax.LaxTrans`。
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
**CategoryTheory.Oplax.LaxTrans.vCompNaturality** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Oplax.LaxTrans`。
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
**CategoryTheory.Oplax.LaxTrans.vComp_naturality_naturality** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Oplax.LaxTrans`。
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
· 使用定理 `CategoryTheory.Oplax.LaxTrans.naturality_naturality`：∀ {B : Type u₁} [in
st : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicateg
ory C]   {F G : CategoryTheory.OplaxFunct…
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
**CategoryTheory.Oplax.LaxTrans.vComp_naturality_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Oplax.LaxTrans`。
形式化陈述：vComp_naturality_id (a : B) : η.vCompNaturality θ (𝟙 a) ≫ F.mapId a ▷ η.vC
ompApp θ a = η.vCompApp θ a ◁ H.mapId a ≫ (ρ_ (η.vCompApp θ a)).hom ≫ (fun_ (η.v
CompApp θ a)).inv
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
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Oplax.LaxTrans.naturality_id`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 {F G : CategoryTheory.OplaxFunct…
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
    η.vCompNaturality θ (𝟙 a) ≫ F.mapId a ▷ η.vCompApp θ a =
      η.vCompApp θ a ◁ H.mapId a ≫ (ρ_ (η.vCompApp θ a)).hom ≫ (λ_ (η.vCompApp θ a)).inv := by
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality (𝟙 a) ⊗≫
          (η.naturality (𝟙 a) ≫ F.mapId a ▷ η.app a) ▷ θ.app a ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality (𝟙 a) ≫ G.mapId a ▷ θ.app a) ⊗≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory
    _ = _ := by
      rw [θ.naturality_id]
      bicategory
/-
**CategoryTheory.Oplax.LaxTrans.vComp_naturality_comp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Oplax.LaxTrans`。
形式化陈述：vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : η.vCompNatural
ity θ (f ≫ g) ≫ F.mapComp f g ▷ η.vCompApp θ c = η.vCompApp θ a ◁ H.mapComp f g 
≫ (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫ η.vCompNaturality θ f ▷ H.map 
g ≫ (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫ F.map f ◁ η.vCompNaturality 
θ g ≫ (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv
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
· 使用定理 `CategoryTheory.Oplax.LaxTrans.naturality_comp`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompNaturality θ (f ≫ g) ≫ F.mapComp f g ▷ η.vCompApp θ c =
      η.vCompApp θ a ◁ H.mapComp f g ≫
        (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
          η.vCompNaturality θ f ▷ H.map g ≫
            (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
              F.map f ◁ η.vCompNaturality θ g ≫ (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv := by
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality (f ≫ g) ⊗≫
          (η.naturality (f ≫ g) ≫ F.mapComp f g ▷ η.app c) ▷ θ.app c ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality (f ≫ g) ≫ G.mapComp f g ▷ θ.app c) ⊗≫
          (η.naturality f ▷ G.map g ⊗≫ F.map f ◁ η.naturality g) ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ⊗≫ θ.naturality f ▷ H.map g) ⊗≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) ⊗≫
            F.map f ◁ η.naturality g ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

/-- Vertical composition of lax transformations. -/
/-
**CategoryTheory.Oplax.LaxTrans.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Oplax.LaxTrans`。
形式化陈述：vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where app a
参数：η : LaxTrans F G；θ : LaxTrans G H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.LaxTrans.vComp_naturality_naturality`：vComp_natural
ity_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) : η.vCompNaturality θ f ≫ F.m
ap₂ β ▷ η.vCompApp θ b = η.vCompApp θ a ◁ H.map…
· 使用定理 `CategoryTheory.Oplax.LaxTrans.vComp_naturality_id`：vComp_naturality_id (
a : B) : η.vCompNaturality θ (𝟙 a) ≫ F.mapId a ▷ η.vCompApp θ a = η.vCompApp θ a
 ◁ H.mapId a ≫ (ρ_ (η.vCompApp θ a)).ho…
· 使用定理 `CategoryTheory.Oplax.LaxTrans.vComp_naturality_comp`：vComp_naturality_co
mp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : η.vCompNaturality θ (f ≫ g) ≫ F.mapComp
 f g ▷ η.vCompApp θ c = η.vCompApp θ a ◁ …

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
/-- `CategoryStruct` on `OplaxFunctor B C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Oplax.LaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Oplax
.LaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `OplaxFunctor B C` where the (1-)morphisms are given by lax
transformations.
-/
scoped instance : CategoryStruct (OplaxFunctor B C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

end LaxTrans

/-- If `η` is an oplax transformation between `F` and `G`, we have a 1-morphism
`η.app a : F.obj a ⟶ G.obj a` for each object `a : B`. We also have a 2-morphism
`η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism `f : a ⟶ b`.
These 2-morphisms satisfy the naturality condition, and preserve the identities and
the compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Oplax.OplaxTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Opla
x`。
形式化陈述：OplaxTrans (F G : B ⥤ᵒᵖᴸ C) where /-- The component 1-morphisms of an opla
x transformation. -/ app (a : B) : F.obj a ⟶ G.obj a /-- The 2-morphisms underly
ing the oplax naturality constraint. -/ naturality {a b : B} (f : a ⟶ b) : F.map
 f ≫ app b ⟶ app a ≫ G.map f naturality_naturality {a b : B} {f g : a ⟶ b} (η : 
f ⟶ g) : F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η
参数：F G : B ⥤ᵒᵖᴸ C；a : B。
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
structure OplaxTrans (F G : B ⥤ᵒᵖᴸ C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] OplaxTrans.naturality_naturality OplaxTrans.naturality_id
  OplaxTrans.naturality_comp

namespace OplaxTrans

variable {F : B ⥤ᵒᵖᴸ C} {G H : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_naturality** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g 
⟶ h) : f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h = f ◁ θ.naturality g ≫ f ◁ θ.
app a ◁ H.map₂ β
参数：f : a' ⟶ G.obj a；β : g ⟶ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_naturality`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_naturality** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b 
⟶ a') : F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h = η.naturality f ▷ h ≫ (α_ _
 _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv
参数：β : f ⟶ g；h : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_naturality`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
-/
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_comp** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) : f
 ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h = f ◁ G.mapComp g h ▷ θ.ap
p c ≫ f ◁ (α_ _ _ _).hom ≫ f ◁ G.map g ◁ θ.naturality h ≫ f ◁ (α_ _ _ _).inv ≫ f
 ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom
参数：f : a' ⟶ G.obj a；g : a ⟶ b；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_comp`：∀ {B : Type u₁} [inst :
 CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory 
C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_comp** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') : 
η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h = F.mapC
omp f g ▷ η.app c ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫ F.map f ◁ η.natura
lity g ▷ h ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ h ≫ η.naturality f ▷ G.map g ▷ h 
≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom
参数：f : a ⟶ b；g : b ⟶ c；h : G.obj c ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.associator_naturality_middle`：associator_natur
ality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) : (f ◁ η) ▷ h ≫
 (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ …
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight_assoc`：∀ {B : Type u} [self 
: CategoryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ 
h) (i : b ⟶ c)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_comp`：∀ {B : Type u₁} [inst :
 CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory 
C]   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_assoc`：∀ {B : Type u} [self : Category
Theory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : 
c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_comp]; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_id** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerLeft_naturality_id (f : a' ⟶ G.obj a) : f ◁ θ.naturality (𝟙 a) ≫ f 
◁ θ.app a ◁ H.mapId a = f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ (θ.app a)).hom ≫ f ◁
 (ρ_ (θ.app a)).inv
参数：f : a' ⟶ G.obj a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_id`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_id** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Oplax.OplaxTrans`。
形式化陈述：whiskerRight_naturality_id (f : G.obj a ⟶ a') : η.naturality (𝟙 a) ▷ f ≫ (
α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f = F.mapId a ▷ η.app a ▷ f ≫ (fun_ (η.app
 a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom
参数：f : G.obj a ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.associator_naturality_middle`：associator_natur
ality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) : (f ◁ η) ▷ h ≫
 (α_ f g' h).hom = (α_ f g h).hom ≫ f ◁ η ▷ …
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight_assoc`：∀ {B : Type u} [self 
: CategoryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ 
h) (i : b ⟶ c)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.naturality_id`：∀ {B : Type u₁} [inst : C
ategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]
   {F G : CategoryTheory.OplaxFunct…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.leftUnitor_whiskerRight`：leftUnitor_whiskerRig
ht (f : a ⟶ b) (g : b ⟶ c) : (fun_ f).hom ▷ g = (α_ (𝟙 a) f g).hom ≫ (fun_ (f ≫ 
g)).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.triangle_assoc_comp_right_inv`：triangle_assoc_
comp_right_inv (f : a ⟶ b) (g : b ⟶ c) : (ρ_ f).inv ▷ g ≫ (α_ f (𝟙 b) g).hom = f
 ◁ (fun_ g).inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_id]; simp

end

variable (F) in
/-- The identity oplax transformation. -/
/-
**CategoryTheory.Oplax.OplaxTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.O
plax.OplaxTrans`。
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
**CategoryTheory.Oplax.OplaxTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Opl
ax.OplaxTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OplaxTrans F F) :=
  ⟨id F⟩

/-- Vertical composition of oplax transformations. -/
/-
**CategoryTheory.Oplax.OplaxTrans.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Oplax.OplaxTrans`。
形式化陈述：vcomp : OplaxTrans F H where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of oplax transformations.
-/
def vcomp : OplaxTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g :=
    calc
      _ =
        (α_ _ _ _).inv ≫
          F.mapComp f g ▷ η.app c ▷ θ.app c ≫
            (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
              F.map f ◁ η.naturality g ▷ θ.app c ≫
                _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
                  (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                    η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫
                        η.app a ◁ θ.naturality f ▷ H.map g ≫
                          _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv := by
        rw [whisker_exchange_assoc]; simp
      _ = _ := by simp

/-- `CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Oplax.OplaxTrans.categoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Oplax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         CategoryTheory.Categor
yStruct.{max (max (max u₁ v₁) v₂) w₂, max (max (max (max (max u₂ u₁) v₂) v₁) w₂)
 w₁}           (CategoryTheory.OplaxFunctor B C)
参数：max (max u₁ v₁) v₂；max (max (max (max u₂ u₁) v₂) v₁) w₂；CategoryTheory.OplaxF
unctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by oplax
transformations.
-/
scoped instance categoryStruct : CategoryStruct (B ⥤ᵒᵖᴸ C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vcomp

end OplaxTrans

/-- A strong natural transformation between oplax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Oplax.StrongTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Opl
ax`。
形式化陈述：StrongTrans (F G : B ⥤ᵒᵖᴸ C) where app (a : B) : F.obj a ⟶ G.obj a natural
ity {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f naturality_natural
ity {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : F.map₂ η ▷ app b ≫ (naturality g).hom 
= (naturality f).hom ≫ app a ◁ G.map₂ η
参数：F G : B ⥤ᵒᵖᴸ C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong natural transformation between oplax functors `F` and `G` is a natural 
transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 
1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identi
ties and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : B ⥤ᵒᵖᴸ C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [nolint docBlame] CategoryTheory.Oplax.StrongTrans.app
  CategoryTheory.Oplax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/-- A structure on an oplax transformation that promotes it to a strong transformation.

See `StrongTrans.mkOfOplax`. -/
/-
**CategoryTheory.Oplax.OplaxTrans.StrongCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Oplax.OplaxTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         {F G : CategoryTheory.
OplaxFunctor B C} → (F ⟶ G) → Type (max (max u₁ v₁) w₂)
参数：F ⟶ G；max (max u₁ v₁) w₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure on an oplax transformation that promotes it to a strong transformati
on.

See `StrongTrans.mkOfOplax`.
-/
structure OplaxTrans.StrongCore {F G : B ⥤ᵒᵖᴸ C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the oplax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by cat_disch

attribute [simp] OplaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
/-
**CategoryTheory.Oplax.StrongTrans.toOplax** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Oplax.StrongTrans`。
形式化陈述：toOplax {F G : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G) : OplaxTrans F G where app
参数：η : StrongTrans F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying oplax natural transformation of a strong natural transformation.
-/
def toOplax {F G : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G) : OplaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-morphism is an isomorphism. -/
/-
**CategoryTheory.Oplax.StrongTrans.mkOfOplax** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Oplax.StrongTrans`。
形式化陈述：mkOfOplax {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCor
e η) : StrongTrans F G where app
参数：η : OplaxTrans F G；η' : OplaxTrans.StrongCore η。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a strong natural transformation from an oplax natural transformation w
hose
naturality 2-morphism is an isomorphism.
-/
def mkOfOplax {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/-- Construct a strong natural transformation from an oplax natural transformation whose
naturality 2-morphism is an isomorphism. -/
/-
**CategoryTheory.Oplax.StrongTrans.mkOfOplax'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Oplax.StrongTrans`。
形式化陈述：mkOfOplax' {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) [forall a b (f : a ⟶ b), 
IsIso (η.naturality f)] : StrongTrans F G where app
参数：η : OplaxTrans F G；f : a ⟶ b；η.naturality f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a strong natural transformation from an oplax natural transformation w
hose
naturality 2-morphism is an isomorphism.
-/
noncomputable def mkOfOplax' {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G)
    [∀ a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : B ⥤ᵒᵖᴸ C)


/-- The identity strong natural transformation. -/
@[simps!]
/-
**CategoryTheory.Oplax.StrongTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Oplax.StrongTrans`。
形式化陈述：id : StrongTrans F F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity strong natural transformation.
-/
def id : StrongTrans F F :=
  mkOfOplax (OplaxTrans.id F) { naturality := fun f ↦ (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm }

@[simp]
/-
**CategoryTheory.Oplax.StrongTrans.id.toOplax** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Oplax.StrongTrans.id`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.OplaxFunctor B C),   (Cate
goryTheory.Oplax.StrongTrans.id F).toOplax = CategoryTheory.Oplax.OplaxTrans.id 
F
参数：F : CategoryTheory.OplaxFunctor B C；CategoryTheory.Oplax.StrongTrans.id F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id.toOplax : (id F).toOplax = OplaxTrans.id F :=
  rfl
/-
**CategoryTheory.Oplax.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Op
lax.StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩


variable {F} {G H : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G) (θ : StrongTrans G H)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Vertical composition of strong natural transformations. -/
@[simps!]
/-
**CategoryTheory.Oplax.StrongTrans.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Oplax.StrongTrans`。
形式化陈述：vcomp : StrongTrans F H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of strong natural transformations.
-/
def vcomp : StrongTrans F H :=
  mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f ↦
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

/-- `CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
/-
**CategoryTheory.Oplax.StrongTrans.categoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Oplax.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         CategoryTheory.Categor
yStruct.{max (max (max u₁ v₁) v₂) w₂, max (max (max (max (max u₂ u₁) v₂) v₁) w₂)
 w₁}           (CategoryTheory.OplaxFunctor B C)
参数：max (max u₁ v₁) v₂；max (max (max (max u₂ u₁) v₂) v₁) w₂；CategoryTheory.OplaxF
unctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by strong
transformations.
-/
scoped instance categoryStruct : CategoryStruct (B ⥤ᵒᵖᴸ C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vcomp

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_naturality** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g 
⟶ h) : f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom = f ◁ (θ.naturality g).
hom ≫ f ◁ θ.app a ◁ H.map₂ β
参数：f : a' ⟶ G.obj a；β : g ⟶ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_naturality`：whisk
erLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) : f ◁ 
G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h = f ◁ θ.natural…
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b 
⟶ a') : F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h = (η.naturality f).hom
 ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv
参数：β : f ⟶ g；h : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_naturality`：whis
kerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') : F.
map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h = η.naturality…
-/
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_comp** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) : f
 ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h = f ◁ G.mapComp g h 
▷ θ.app c ≫ f ◁ (α_ _ _ _).hom ≫ f ◁ G.map g ◁ (θ.naturality h).hom ≫ f ◁ (α_ _ 
_ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom
参数：f : a' ⟶ G.obj a；g : a ⟶ b；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_comp`：whiskerLeft
_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) : f ◁ θ.naturality (
g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h = f ◁ G.mapC…
-/
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_comp** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') : 
(η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h = 
F.mapComp f g ▷ η.app c ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫ F.map f ◁ (η
.naturality g).hom ▷ h ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ h ≫ (η.naturality f).
hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom
参数：f : a ⟶ b；g : b ⟶ c；h : G.obj c ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_comp`：whiskerRig
ht_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') : η.naturality (f 
≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f …
-/
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_comp _ _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_id** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerLeft_naturality_id (f : a' ⟶ G.obj a) : f ◁ (θ.naturality (𝟙 a)).ho
m ≫ f ◁ θ.app a ◁ H.mapId a = f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ (θ.app a)).hom
 ≫ f ◁ (ρ_ (θ.app a)).inv
参数：f : a' ⟶ G.obj a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerLeft_naturality_id`：whiskerLeft_n
aturality_id (f : a' ⟶ G.obj a) : f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId
 a = f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ (θ.app…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toOplax.whiskerLeft_naturality_id _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_id** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Oplax.StrongTrans`。
形式化陈述：whiskerRight_naturality_id (f : G.obj a ⟶ a') : (η.naturality (𝟙 a)).hom ▷
 f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f = F.mapId a ▷ η.app a ▷ f ≫ (fun_ 
(η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom
参数：f : G.obj a ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_id`：whiskerRight
_naturality_id (f : G.obj a ⟶ a') : η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.
app a ◁ G.mapId a ▷ f = F.mapId a ▷ η.app a ▷ f …

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

end

end StrongTrans

end CategoryTheory.Oplax

