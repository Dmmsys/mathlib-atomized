/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.Data.Int.Notation
/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphism of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `Equivalence`: bundled (half-)adjoint equivalences of categories
* `Functor.EssSurj`: type class on a functor `F` containing the data of the preimages
  and the isomorphisms `F.obj (preimage d) ≅ d`.
* `Functor.IsEquivalence`: type class on a functor `F` which is full, faithful and
  essentially surjective.

## Main results

* `Equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `isEquivalence_iff_of_iso`: when `F` and `G` are isomorphic functors,
  `F` is an equivalence iff `G` is.
* `Functor.asEquivalenceFunctor`: construction of an equivalence of categories from
  a functor `F` which satisfies the property `F.IsEquivalence` (i.e. `F` is full, faithful
  and essentially surjective).

## Notation

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- An equivalence of categories.

We define an equivalence between `C` and `D`, with notation `C ≌ D`, as a half-adjoint equivalence:
a pair of functors `F : C ⥤ D` and `G : D ⥤ C` with a unit `η : 𝟭 C ≅ F ⋙ G` and counit
`ε : G ⋙ F ≅ 𝟭 D`, such that the natural isomorphisms `η` and `ε` satisfy the triangle law for
`F`: namely, `Fη ≫ εF = 𝟙 F`. Or, in other words, the composite `F` ⟶ `F ⋙ G ⋙ F` ⟶ `F` is the
identity.

In `unit_inverse_comp`, we show that this is sufficient to establish a full adjoint
equivalence. I.e., the composite `G` ⟶ `G ⋙ F ⋙ G` ⟶ `G` is also the identity.

The triangle equation `functor_unitIso_comp` is written as a family of equalities between
morphisms. It is more complicated if we write it as an equality of natural transformations, because
then we would either have to insert natural transformations like `F ⟶ F𝟭` or abuse defeq. -/
@[ext, stacks 001J]
/-
**CategoryTheory.Equivalence** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D
] where mk' :: /-- The forwards direction of an equivalence. -/ functor : C ⥤ D 
/-- The backwards direction of an equivalence. -/ inverse : D ⥤ C /-- The compos
ition `functor ⋙ inverse` is isomorphic to the identity. -/ unitIso : 𝟭 C ≅ func
tor ⋙ inverse /-- The composition `inverse ⋙ functor` is isomorphic to the ident
ity. -/ counitIso : inverse ⋙ functor ≅ 𝟭 D /-- The triangle law for the forward
s direction of an equivale
参数：C : Type u₁；D : Type u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories.

We define an equivalence between `C` and `D`, with notation `C ≌ D`, as a half-a
djoint equivalence:
a pair of functors `F : C ⥤ D` and `G : D ⥤ C` with a unit `η : 𝟭 C ≅ F ⋙ G` and
 counit
`ε : G ⋙ F ≅ 𝟭 D`, such that the natural isomorphisms `η` and `ε` satisfy the tr
iangle law for
`F`: namely, `Fη ≫ εF = 𝟙 F`. Or, in other words, the composite `F` ⟶ `F ⋙ G ⋙ F
` ⟶ `F` is the
identity.

In `unit_inverse_comp`, we show that this is sufficient to establish a full adjo
int
equivalence. I.e., the composite `G` ⟶ `G ⋙ F ⋙ G` ⟶ `G` is also the identity.

The triangle equation `functor_unitIso_comp` is written as a family of equalitie
s between
morphisms. It is more complicated if we write it as an equality of natural trans
formations, because
then we would either have to insert natural transformations like `F ⟶ F𝟭` or abu
se defeq. -/
-/
structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  /-- The forwards direction of an equivalence. -/
  functor : C ⥤ D
  /-- The backwards direction of an equivalence. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is isomorphic to the identity. -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is isomorphic to the identity. -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  /-- The triangle law for the forwards direction of an equivalence: the unit and counit compose
  to the identity when whiskered along the forwards direction.

  We state this as a family of equalities among morphisms instead of an equality of natural
  transformations to avoid abusing defeq or inserting natural transformations like `F ⟶ F𝟭`. -/
  functor_unitIso_comp (X : C) :
    dsimp% functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by cat_disch

@[inherit_doc Equivalence]
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

@[to_dual existing functor_unitIso_comp]
/-
**CategoryTheory.Equivalence.counitIso_functor_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：counitIso_functor_comp (e : C ≌ D) (X : C) : dsimp% e.counitIso.inv.app (e
.functor.obj X) ≫ e.functor.map (e.unitIso.inv.app X) = 𝟙 (e.functor.obj X)
参数：e : C ≌ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.functor_unitIso_comp`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (self : C ≌ D) (X …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `CategoryTheory.Iso.inv_eq_inv`：inv_eq_inv (f g : X ≅ Y) : f.inv = g.inv 
↔ f.hom = g.hom
-/
theorem counitIso_functor_comp (e : C ≌ D) (X : C) :
    dsimp% e.counitIso.inv.app (e.functor.obj X) ≫ e.functor.map (e.unitIso.inv.app X) =
      𝟙 (e.functor.obj X) := by
  simpa [functor_unitIso_comp] using Iso.inv_eq_inv
    (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X)) (Iso.refl _)

/-- `Equivalence.mk'` is the dual of `Equivalence.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk']
/-
**CategoryTheory.Equivalence.mk''** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：mk'' {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (func
tor : C ⥤ D) (inverse : D ⥤ C) (unitIso : 𝟭 C ≅ functor ⋙ inverse) (counitIso : 
inverse ⋙ functor ≅ 𝟭 D) (functor_unitIso_comp : dsimp% forall (X : C), counitIs
o.inv.app (functor.obj X) ≫ functor.map (unitIso.inv.app X) = 𝟙 (functor.obj X))
 : Equivalence C D where functor; inverse; unitIso; counitIso functor_unitIso_co
mp X
参数：functor : C ⥤ D；inverse : D ⥤ C；unitIso : 𝟭 C ≅ functor ⋙ inverse；counitIso :
 inverse ⋙ functor ≅ 𝟭 D；functor_unitIso_comp : dsimp% forall (X : C), counitIso
.inv.app (functor.obj X) ≫ functor.map (unitIso.inv.app X) = 𝟙 (functor.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equivalence.mk'` is the dual of `Equivalence.mk`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev mk''
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (functor : C ⥤ D) (inverse : D ⥤ C)
    (unitIso : 𝟭 C ≅ functor ⋙ inverse) (counitIso : inverse ⋙ functor ≅ 𝟭 D)
    (functor_unitIso_comp : dsimp% ∀ (X : C),
      counitIso.inv.app (functor.obj X) ≫ functor.map (unitIso.inv.app X) = 𝟙 (functor.obj X)) :
    Equivalence C D where
  functor; inverse; unitIso; counitIso
  functor_unitIso_comp X := by
    simpa [functor_unitIso_comp] using Iso.inv_eq_inv
      (functor.mapIso (unitIso.app X) ≪≫ counitIso.app (functor.obj X)) (Iso.refl _)


/-- The unit of an equivalence of categories. -/
@[to_dual unitInv /-- The inverse of the unit of an equivalence of categories. -/]
/-
**CategoryTheory.Equivalence.unit** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of an equivalence of categories.
-/
abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse :=
  e.unitIso.hom

/-- The counit of an equivalence of categories. -/
@[to_dual counitInv /-- The inverse of the counit of an equivalence of categories. -/]
/-
**CategoryTheory.Equivalence.counit** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Equivalence`。
形式化陈述：counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of an equivalence of categories.
-/
abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom

@[reassoc +to_dual]
/-
**CategoryTheory.Equivalence.unitIso_hom_inv_id_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：unitIso_hom_inv_id_app (e : C ≌ D) (X : C) : dsimp% e.unit.app X ≫ e.unitI
nv.app X = 𝟙 X
参数：e : C ≌ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitIso_hom_inv_id_app (e : C ≌ D) (X : C) :
    dsimp% e.unit.app X ≫ e.unitInv.app X = 𝟙 X := by
  simp

@[reassoc +to_dual]
/-
**CategoryTheory.Equivalence.unitIso_inv_hom_id_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：unitIso_inv_hom_id_app (e : C ≌ D) (X : C) : dsimp% e.unitInv.app X ≫ e.un
it.app X = 𝟙 _
参数：e : C ≌ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitIso_inv_hom_id_app (e : C ≌ D) (X : C) :
    dsimp% e.unitInv.app X ≫ e.unit.app X = 𝟙 _ := by
  simp

@[reassoc +to_dual]
/-
**CategoryTheory.Equivalence.counitIso_hom_inv_id_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Equivalence`。
形式化陈述：counitIso_hom_inv_id_app (e : C ≌ D) (Y : D) : dsimp% e.counit.app Y ≫ e.c
ounitInv.app Y = 𝟙 _
参数：e : C ≌ D；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitIso_hom_inv_id_app (e : C ≌ D) (Y : D) :
    dsimp% e.counit.app Y ≫ e.counitInv.app Y = 𝟙 _ := by
  simp

@[reassoc +to_dual]
/-
**CategoryTheory.Equivalence.counitIso_inv_hom_id_app** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Equivalence`。
形式化陈述：counitIso_inv_hom_id_app (e : C ≌ D) (Y : D) : dsimp% e.counitInv.app Y ≫ 
e.counit.app Y = 𝟙 Y
参数：e : C ≌ D；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitIso_inv_hom_id_app (e : C ≌ D) (Y : D) :
    dsimp% e.counitInv.app Y ≫ e.counit.app Y = 𝟙 Y := by
  simp

section CategoryStructure

/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (C ≌ D) where
  Hom e f := e.functor ⟶ f.functor
  id e := 𝟙 e.functor
  comp {a b c} f g := (f ≫ g : a.functor ⟶ _)

/-- Promote a natural transformation `e.functor ⟶ f.functor` to a morphism in `C ≌ D`. -/
@[to_dual self]
/-
**CategoryTheory.Equivalence.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equ
ivalence`。
形式化陈述：mkHom {e f : C ≌ D} (η : e.functor ⟶ f.functor) : e ⟶ f
参数：η : e.functor ⟶ f.functor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a natural transformation `e.functor ⟶ f.functor` to a morphism in `C ≌ D
`.
-/
def mkHom {e f : C ≌ D} (η : e.functor ⟶ f.functor) : e ⟶ f := η

/-- Recover a natural transformation between `e.functor` and `f.functor` from the data of
a morphism `e ⟶ f`. -/
@[to_dual self]
/-
**CategoryTheory.Equivalence.asNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：asNatTrans {e f : C ≌ D} (η : e ⟶ f) : e.functor ⟶ f.functor
参数：η : e ⟶ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recover a natural transformation between `e.functor` and `f.functor` from the da
ta of
a morphism `e ⟶ f`.
-/
def asNatTrans {e f : C ≌ D} (η : e ⟶ f) : e.functor ⟶ f.functor := η

@[ext, to_dual self]
/-
**CategoryTheory.Equivalence.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.E
quivalence`。
形式化陈述：hom_ext {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β) : α 
= β
参数：h : asNatTrans α = asNatTrans β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β) : α = β := h

@[simp, to_dual self]
/-
**CategoryTheory.Equivalence.mkHom_asNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：mkHom_asNatTrans {e f : C ≌ D} (η : e.functor ⟶ f.functor) : mkHom (asNatT
rans η) = η
参数：η : e.functor ⟶ f.functor。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_asNatTrans {e f : C ≌ D} (η : e.functor ⟶ f.functor) :
    mkHom (asNatTrans η) = η :=
  rfl

@[simp, to_dual self]
/-
**CategoryTheory.Equivalence.asNatTrans_mkHom** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：asNatTrans_mkHom {e f : C ≌ D} (η : e ⟶ f) : asNatTrans (mkHom η) = η
参数：η : e ⟶ f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma asNatTrans_mkHom {e f : C ≌ D} (η : e ⟶ f) :
    asNatTrans (mkHom η) = η :=
  rfl

@[simp]
/-
**CategoryTheory.Equivalence.id_asNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：id_asNatTrans {e : C ≌ D} : asNatTrans (𝟙 e) = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_asNatTrans {e : C ≌ D} : asNatTrans (𝟙 e) = 𝟙 _ := rfl

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.Equivalence.comp_asNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：comp_asNatTrans {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g) : asNatTrans (α ≫ 
β) = asNatTrans α ≫ asNatTrans β
参数：α : e ⟶ f；β : f ⟶ g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_asNatTrans {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g) :
    asNatTrans (α ≫ β) = asNatTrans α ≫ asNatTrans β :=
  rfl

@[simp]
/-
**CategoryTheory.Equivalence.mkHom_id_functor** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：mkHom_id_functor {e : C ≌ D} : mkHom (𝟙 e.functor) = 𝟙 e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_id_functor {e : C ≌ D} : mkHom (𝟙 e.functor) = 𝟙 e := rfl

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.Equivalence.mkHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：mkHom_comp {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.
functor) : mkHom (α ≫ β) = mkHom α ≫ mkHom β
参数：α : e.functor ⟶ f.functor；β : f.functor ⟶ g.functor。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_comp {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor) :
    mkHom (α ≫ β) = mkHom α ≫ mkHom β :=
  rfl

/-- Construct an isomorphism in `C ≌ D` from a natural isomorphism between the functors
of the equivalences. -/
@[simps]
/-
**CategoryTheory.Equivalence.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equ
ivalence`。
形式化陈述：mkIso {e f : C ≌ D} (η : e.functor ≅ f.functor) : e ≅ f where hom
参数：η : e.functor ≅ f.functor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in `C ≌ D` from a natural isomorphism between the funct
ors
of the equivalences.
-/
def mkIso {e f : C ≌ D} (η : e.functor ≅ f.functor) : e ≅ f where
  hom := mkHom η.hom
  inv := mkHom η.inv

attribute [to_dual existing mkIso_inv] mkIso_hom

variable (C D) in
/-- The `functor` functor that sends an equivalence of categories to its functor. -/
@[simps!]
/-
**CategoryTheory.Equivalence.functorFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Equivalence`。
形式化陈述：functorFunctor : (C ≌ D) ⥤ C ⥤ D where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `functor` functor that sends an equivalence of categories to its functor.
-/
def functorFunctor : (C ≌ D) ⥤ C ⥤ D where
  obj f := f.functor
  map α := asNatTrans α

end CategoryStructure

/-! While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.Equivalence_mk'_unit** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (functor : CategoryTheory.Functo
r C D) (inverse : CategoryTheory.Functor D C)   (unit_iso : CategoryTheory.Funct
or.id C ≅ functor.comp inverse)   (counit_iso : inverse.comp functor ≅ CategoryT
heory.Functor.id D)   (f :     ∀ (X : C),       CategoryTheory.CategoryStruct.co
mp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (functor.obj X)) =    
     CategoryTheory.CategoryStruct.id (functor.obj X)),   { functor := functor, 
inverse := inverse, unitIso := unit_iso, counitIso := counit_iso,         functo
r_unitIso_comp := f }.unit =     unit_iso.hom
参数：functor : CategoryTheory.Functor C D；inverse : CategoryTheory.Functor D C；uni
t_iso : CategoryTheory.Functor.id C ≅ functor.comp inverse；counit_iso : inverse.
comp functor ≅ CategoryTheory.Functor.id D；f :     ∀ (X : C),       CategoryTheo
ry.CategoryStruct.comp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (f
unctor.obj X)) =         CategoryTheory.CategoryStruct.id (functor.obj X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding.
-/
theorem Equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom :=
  rfl

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.Equivalence_mk'_counit** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (functor : CategoryTheory.Functo
r C D) (inverse : CategoryTheory.Functor D C)   (unit_iso : CategoryTheory.Funct
or.id C ≅ functor.comp inverse)   (counit_iso : inverse.comp functor ≅ CategoryT
heory.Functor.id D)   (f :     ∀ (X : C),       CategoryTheory.CategoryStruct.co
mp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (functor.obj X)) =    
     CategoryTheory.CategoryStruct.id (functor.obj X)),   { functor := functor, 
inverse := inverse, unitIso := unit_iso, counitIso := counit_iso,         functo
r_unitIso_comp := f }.counit =     counit_iso.hom
参数：functor : CategoryTheory.Functor C D；inverse : CategoryTheory.Functor D C；uni
t_iso : CategoryTheory.Functor.id C ≅ functor.comp inverse；counit_iso : inverse.
comp functor ≅ CategoryTheory.Functor.id D；f :     ∀ (X : C),       CategoryTheo
ry.CategoryStruct.comp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (f
unctor.obj X)) =         CategoryTheory.CategoryStruct.id (functor.obj X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom :=
  rfl

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.Equivalence_mk'_unitInv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (functor : CategoryTheory.Functo
r C D) (inverse : CategoryTheory.Functor D C)   (unit_iso : CategoryTheory.Funct
or.id C ≅ functor.comp inverse)   (counit_iso : inverse.comp functor ≅ CategoryT
heory.Functor.id D)   (f :     ∀ (X : C),       CategoryTheory.CategoryStruct.co
mp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (functor.obj X)) =    
     CategoryTheory.CategoryStruct.id (functor.obj X)),   { functor := functor, 
inverse := inverse, unitIso := unit_iso, counitIso := counit_iso,         functo
r_unitIso_comp := f }.unitInv =     unit_iso.inv
参数：functor : CategoryTheory.Functor C D；inverse : CategoryTheory.Functor D C；uni
t_iso : CategoryTheory.Functor.id C ≅ functor.comp inverse；counit_iso : inverse.
comp functor ≅ CategoryTheory.Functor.id D；f :     ∀ (X : C),       CategoryTheo
ry.CategoryStruct.comp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (f
unctor.obj X)) =         CategoryTheory.CategoryStruct.id (functor.obj X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equivalence_mk'_unitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.Equivalence_mk'_counitInv** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (functor : CategoryTheory.Functo
r C D) (inverse : CategoryTheory.Functor D C)   (unit_iso : CategoryTheory.Funct
or.id C ≅ functor.comp inverse)   (counit_iso : inverse.comp functor ≅ CategoryT
heory.Functor.id D)   (f :     ∀ (X : C),       CategoryTheory.CategoryStruct.co
mp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (functor.obj X)) =    
     CategoryTheory.CategoryStruct.id (functor.obj X)),   { functor := functor, 
inverse := inverse, unitIso := unit_iso, counitIso := counit_iso,         functo
r_unitIso_comp := f }.counitInv =     counit_iso.inv
参数：functor : CategoryTheory.Functor C D；inverse : CategoryTheory.Functor D C；uni
t_iso : CategoryTheory.Functor.id C ≅ functor.comp inverse；counit_iso : inverse.
comp functor ≅ CategoryTheory.Functor.id D；f :     ∀ (X : C),       CategoryTheo
ry.CategoryStruct.comp (functor.map (unit_iso.hom.app X)) (counit_iso.hom.app (f
unctor.obj X)) =         CategoryTheory.CategoryStruct.id (functor.obj X)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equivalence_mk'_counitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl

@[to_dual (attr := reassoc) counitInv_naturality]
/-
**CategoryTheory.Equivalence.counit_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：counit_naturality (e : C ≌ D) {X Y : D} (f : X ⟶ Y) : dsimp% e.functor.map
 (e.inverse.map f) ≫ e.counit.app Y = e.counit.app X ≫ f
参数：e : C ≌ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem counit_naturality (e : C ≌ D) {X Y : D} (f : X ⟶ Y) :
    dsimp% e.functor.map (e.inverse.map f) ≫ e.counit.app Y = e.counit.app X ≫ f :=
  e.counit.naturality f

@[to_dual (attr := reassoc) unitInv_naturality]
/-
**CategoryTheory.Equivalence.unit_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：unit_naturality (e : C ≌ D) {X Y : C} (f : X ⟶ Y) : dsimp% e.unit.app X ≫ 
e.inverse.map (e.functor.map f) = f ≫ e.unit.app Y
参数：e : C ≌ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem unit_naturality (e : C ≌ D) {X Y : C} (f : X ⟶ Y) :
    dsimp% e.unit.app X ≫ e.inverse.map (e.functor.map f) = f ≫ e.unit.app Y :=
  (e.unit.naturality f).symm

@[to_dual (attr := reassoc (attr := simp)) counitInv_functor_comp]
/-
**CategoryTheory.Equivalence.functor_unit_comp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：functor_unit_comp (e : C ≌ D) (X : C) : dsimp% e.functor.map (e.unit.app X
) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X)
参数：e : C ≌ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.functor_unitIso_comp`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (self : C ≌ D) (X …
-/
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    dsimp% e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
  e.functor_unitIso_comp X

@[to_dual counitInv_app_functor]
/-
**CategoryTheory.Equivalence.counit_app_functor** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Equivalence`。
形式化陈述：counit_app_functor (e : C ≌ D) (X : C) : e.counit.app (e.functor.obj X) = 
e.functor.map (e.unitInv.app X)
参数：e : C ≌ D；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.functor_unit_comp`：functor_unit_comp (e : C ≌
 D) (X : C) : dsimp% e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj 
X) = 𝟙 (e.functor.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `CategoryTheory.Iso.hom_comp_eq_id`：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
-/
theorem counit_app_functor (e : C ≌ D) (X : C) :
    e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X) := by
  simpa using Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)) (f := e.counit.app _)

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[to_dual (attr := reassoc (attr := simp)) inverse_counitInv_comp]
/-
**CategoryTheory.Equivalence.unit_inverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：unit_inverse_comp (e : C ≌ D) (Y : D) : dsimp% e.unit.app (e.inverse.obj Y
) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y)
参数：e : C ≌ D；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.app_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F
 G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.app_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F
 G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Equivalence.unit_naturality`：unit_naturality (e : C ≌ D) 
{X Y : C} (f : X ⟶ Y) : dsimp% e.unit.app X ≫ e.inverse.map (e.functor.map f) = 
f ≫ e.unit.app Y
· 使用定理 `CategoryTheory.Equivalence.counit_naturality`：counit_naturality (e : C ≌
 D) {X Y : D} (f : X ⟶ Y) : dsimp% e.functor.map (e.inverse.map f) ≫ e.counit.ap
p Y = e.counit.app X ≫ f
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.counitInv_naturality`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (e : C ≌ D) {X Y :…
· 使用定理 `CategoryTheory.Equivalence.unitInv_naturality`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (e : C ≌ D) {X Y :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001
-/
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    dsimp% e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _), ← map_id e.inverse, ← counitInv_functor_comp, map_comp]
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _)), Iso.app_hom,
    Iso.app_inv]
  slice_lhs 2 3 => rw [← e.unit_naturality]
  slice_lhs 1 2 => rw [← e.unit_naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [← map_comp e.inverse]
    dsimp
    rw [e.counit_naturality, e.counitIso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 2 3 =>
    dsimp only [Functor.mapIso_inv, Iso.app_inv]
    rw [← map_comp e.inverse, ← e.counitInv_naturality, map_comp]
  slice_lhs 3 4 => rw [e.unitInv_naturality]
  slice_lhs 4 5 =>
    rw [← map_comp e.inverse, ← map_comp e.functor, e.unitIso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [map_id, map_id]
  rw [id_comp]
  slice_lhs 3 4 => rw [← e.unitInv_naturality]
  slice_lhs 2 3 =>
    rw [← map_comp e.inverse, e.counitInv_naturality, e.counitIso.hom_inv_id_app]
  simp

@[to_dual unitInv_app_inverse]
/-
**CategoryTheory.Equivalence.unit_app_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：unit_app_inverse (e : C ≌ D) (Y : D) : e.unit.app (e.inverse.obj Y) = e.in
verse.map (e.counitInv.app Y)
参数：e : C ≌ D；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.unit_inverse_comp`：unit_inverse_comp (e : C ≌
 D) (Y : D) : dsimp% e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app 
Y) = 𝟙 (e.inverse.obj Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `CategoryTheory.Iso.comp_hom_eq_id`：comp_hom_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : f ≫ α.hom = 𝟙 Y ↔ f = α.inv
-/
theorem unit_app_inverse (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  simpa using Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)) (f := e.unit.app _)

@[to_dual none, reassoc, simp]
/-
**CategoryTheory.Equivalence.fun_inv_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) : e.functor.map (e.inverse.m
ap f) = e.counit.app X ≫ f ≫ e.counitInv.app Y
参数：e : C ≌ D；X Y : D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm

@[to_dual none, reassoc, simp]
/-
**CategoryTheory.Equivalence.inv_fun_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) : e.inverse.map (e.functor.m
ap f) = e.unitInv.app X ≫ f ≫ e.unit.app Y
参数：e : C ≌ D；X Y : C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm

section

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointifyη η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `Equivalence.mk`. -/
/-
**CategoryTheory.Equivalence.adjointify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we
 can upgrade it
to a refined natural isomorphism `adjointifyη η : 𝟭 C ≅ F ⋙ G` which exhibits th
e properties
required for a half-adjoint equivalence. See `Equivalence.mk`.
-/
def adjointifyη : 𝟭 C ≅ F ⋙ G := by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]
/-
**CategoryTheory.Equivalence.adjointify_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointify_η_ε (X : C) :
    F.map ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp [adjointifyη, Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

end

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
/-
**CategoryTheory.Equivalence.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equiva
lence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) →           (G : CategoryTheory.Functor D C) →         
    (CategoryTheory.Functor.id C ≅ F.comp G) → (G.comp F ≅ CategoryTheory.Functo
r.id D) → (C ≌ D)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D C；CategoryTheory.
Functor.id C ≅ F.comp G；G.comp F ≅ CategoryTheory.Functor.id D；C ≌ D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.adjointify_η_ε`：adjointify_η_ε (X : C) : F.ma
p ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X)

--- 原说明 ---
Every equivalence of categories consisting of functors `F` and `G` such that `F 
⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed int
o a half-adjoint
    equivalence without changing `F` or `G`.
-/
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

/-- Equivalence of categories is reflexive. -/
@[refl, simps]
/-
**CategoryTheory.Equivalence.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equi
valence`。
形式化陈述：refl : C ≌ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of categories is reflexive.
-/
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[implicit_reducible, symm, simps]
/-
**CategoryTheory.Equivalence.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equi
valence`。
形式化陈述：symm (e : C ≌ D) : D ≌ C
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.inverse_counitInv_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (Y : D…

--- 原说明 ---
Equivalence of categories is symmetric.
-/
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

@[simp]
/-
**CategoryTheory.Equivalence.mkHom_id_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：mkHom_id_inverse {e : C ≌ D} : mkHom (𝟙 e.inverse) = 𝟙 e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_id_inverse {e : C ≌ D} : mkHom (𝟙 e.inverse) = 𝟙 e.symm := rfl

@[simp]
/-
**CategoryTheory.Equivalence.symm_counit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：symm_counit (e : C ≌ D) : e.symm.counit = e.unitInv
参数：e : C ≌ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_counit (e : C ≌ D) : e.symm.counit = e.unitInv := rfl

@[simp]
/-
**CategoryTheory.Equivalence.symm_unit** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Equivalence`。
形式化陈述：symm_unit (e : C ≌ D) : e.symm.unit = e.counitInv
参数：e : C ≌ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_unit (e : C ≌ D) : e.symm.unit = e.counitInv := rfl

variable {E : Type u₃} [Category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps]
/-
**CategoryTheory.Equivalence.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equ
ivalence`。
形式化陈述：trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where functor
参数：e : C ≌ D；f : D ≌ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of categories is transitive.
-/
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight (e.functor.rightUnitor.symm ≪≫
    isoWhiskerLeft _ f.unitIso ≪≫ (Functor.associator _ _ _).symm) _ ≪≫ Functor.associator _ _ _
  counitIso := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ((Functor.associator _ _ _) ≪≫
      isoWhiskerLeft _ e.counitIso ≪≫ f.inverse.rightUnitor) _ ≪≫ f.counitIso
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    simp only [comp_id, id_comp, map_comp, fun_inv_map, comp_obj, id_obj, counitInv,
      functor_unit_comp_assoc, assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
/-
**CategoryTheory.Equivalence.funInvIdAssoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F
参数：e : C ≌ D；F : C ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a functor with both functors of an equivalence yields a naturally isom
orphic
functor.
-/
def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[to_dual (attr := simp) funInvIdAssoc_inv_app]
/-
**CategoryTheory.Equivalence.funInvIdAssoc_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) : (funInvIdAssoc e F
).hom.app X = F.map (e.unitInv.app X)
参数：e : C ≌ D；F : C ⥤ E；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).hom.app X = F.map (e.unitInv.app X) := by
  dsimp [funInvIdAssoc]
  simp

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
/-
**CategoryTheory.Equivalence.invFunIdAssoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F
参数：e : C ≌ D；F : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a functor with both functors of an equivalence yields a naturally isom
orphic
functor.
-/
def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[to_dual (attr := simp) invFunIdAssoc_inv_app]
/-
**CategoryTheory.Equivalence.invFunIdAssoc_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) : (invFunIdAssoc e F
).hom.app X = F.map (e.counit.app X)
参数：e : C ≌ D；F : D ⥤ E；X : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).hom.app X = F.map (e.counit.app X) := by
  dsimp [invFunIdAssoc]
  simp

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/-
**CategoryTheory.Equivalence.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Equivalence`。
形式化陈述：congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`.
-/
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E where
  functor := (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/-
**CategoryTheory.Equivalence.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`.
-/
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D where
  functor := (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

variable (E) in
/-- Promoting `Equivalence.congrRight` to a functor. -/
@[simps]
/-
**CategoryTheory.Equivalence.congrRightFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：congrRightFunctor : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where obj e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promoting `Equivalence.congrRight` to a functor.
-/
def congrRightFunctor : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  obj e := e.congrRight
  map {e f} α := mkHom <| (whiskeringRight _ _ _).map <| asNatTrans α

section CancellationLemmas

variable (e : C ≌ D)

/- We need special forms of `cancel_natIso_hom_right(_assoc)` and
`cancel_natIso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unitIso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos)

`cancel_unitInv_left` is not a `simp` lemma because it would be redundant.
-/
@[to_dual cancel_unitInv_left, simp]
/-
**CategoryTheory.Equivalence.cancel_unit_right** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：cancel_unit_right {X Y : C} (f f' : X ⟶ Y) : f ≫ e.unit.app Y = f' ≫ e.uni
t.app Y ↔ f = f'
参数：f f' : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
We need special forms of `cancel_natIso_hom_right(_assoc)` and
`cancel_natIso_inv_right(_assoc)` for units and counits, because neither `simp` 
or `rw` will apply
those lemmas in this setting without providing `e.unitIso` (or similar) as an ex
plicit argument.
We also provide the lemmas for length four compositions, since they're occasiona
lly useful.
(e.g. in proving that equivalences take monos to monos)

`cancel_unitInv_left` is not a `simp` lemma because it would be redundant.
-/
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) :
    f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' := by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_unit_left]
/-
**CategoryTheory.Equivalence.cancel_unitInv_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)
) : f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f'
参数：f f' : X ⟶ e.inverse.obj (e.functor.obj Y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[to_dual (attr := simp) cancel_counitInv_left]
/-
**CategoryTheory.Equivalence.cancel_counit_right** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Equivalence`。
形式化陈述：cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y))
 : f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f'
参数：f f' : X ⟶ e.functor.obj (e.inverse.obj Y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by simp only [cancel_mono]

/-
`cancel_counit_left` is not a `simp` lemma because it would be redundant.
-/
@[to_dual cancel_counit_left, simp]
/-
**CategoryTheory.Equivalence.cancel_counitInv_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) : f ≫ e.counitInv.app Y = 
f' ≫ e.counitInv.app Y ↔ f = f'
参数：f f' : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`cancel_counit_left` is not a `simp` lemma because it would be redundant.
-/
theorem cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) :
    f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.cancel_unit_right_assoc** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Equivalence`。
形式化陈述：cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X
') (g' : X' ⟶ Y) : f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ 
g'
参数：f : W ⟶ X；g : X ⟶ Y；f' : W ⟶ X'；g' : X' ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.cancel_counitInv_right_assoc** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Equivalence`。
形式化陈述：cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : 
W ⟶ X') (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y 
↔ f ≫ g = f' ≫ g'
参数：f : W ⟶ X；g : X ⟶ Y；f' : W ⟶ X'；g' : X' ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.cancel_unit_right_assoc'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Equivalence`。
形式化陈述：cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : 
Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) : f ≫ g ≫ h ≫ e.unit.app Z = f
' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h'
参数：f : W ⟶ X；g : X ⟶ Y；h : Y ⟶ Z；f' : W ⟶ X'；g' : X' ⟶ Y'；h' : Y' ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [← Category.assoc, cancel_mono]

@[simp, to_dual none]
/-
**CategoryTheory.Equivalence.cancel_counitInv_right_assoc'** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Equivalence`。
形式化陈述：cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) 
(h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) : f ≫ g ≫ h ≫ e.counitInv
.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h'
参数：f : W ⟶ X；g : X ⟶ Y；h : Y ⟶ Z；f' : W ⟶ X'；g' : X' ⟶ Y'；h' : Y' ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔
    f ≫ g ≫ h = f' ≫ g' ≫ h' := by simp only [← Category.assoc, cancel_mono]

end CancellationLemmas

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.
/-- Natural number powers of an auto-equivalence.  Use `(^)` instead. -/
/-
**CategoryTheory.Equivalence.powNat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → (C ≌ C) → ℕ 
→ (C ≌ C)
参数：C ≌ C；C ≌ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural number powers of an auto-equivalence.  Use `(^)` instead.
-/
def powNat (e : C ≌ C) : ℕ → (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (powNat e (n + 1))

/-- Powers of an auto-equivalence.  Use `(^)` instead. -/
/-
**CategoryTheory.Equivalence.pow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equiv
alence`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → (C ≌ C) → ℤ 
→ (C ≌ C)
参数：C ≌ C；C ≌ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Powers of an auto-equivalence.  Use `(^)` instead.
-/
def pow (e : C ≌ C) : ℤ → (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (C ≌ C) ℤ :=
  ⟨pow⟩

@[simp]
/-
**CategoryTheory.Equivalence.pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Equivalence`。
形式化陈述：pow_zero (e : C ≌ C) : e ^ (0 : Int) = Equivalence.refl
参数：e : C ≌ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_zero (e : C ≌ C) : e ^ (0 : ℤ) = Equivalence.refl :=
  rfl

@[simp]
/-
**CategoryTheory.Equivalence.pow_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.E
quivalence`。
形式化陈述：pow_one (e : C ≌ C) : e ^ (1 : Int) = e
参数：e : C ≌ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_one (e : C ≌ C) : e ^ (1 : ℤ) = e :=
  rfl

@[simp]
/-
**CategoryTheory.Equivalence.pow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：pow_neg_one (e : C ≌ C) : e ^ (-1 : Int) = e.symm
参数：e : C ≌ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : ℤ) = e.symm :=
  rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.
-- Note: the better formulation of this would involve `HasShift`.
end

/-- The functor of an equivalence of categories is essentially surjective. -/
@[stacks 02C3]
/-
**CategoryTheory.Equivalence.essSurj_functor** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：essSurj_functor (e : C ≌ E) : e.functor.EssSurj
参数：e : C ≌ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor of an equivalence of categories is essentially surjective.
-/
instance essSurj_functor (e : C ≌ E) : e.functor.EssSurj :=
  ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩
/-
**CategoryTheory.Equivalence.essSurj_inverse** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：essSurj_inverse (e : C ≌ E) : e.inverse.EssSurj
参数：e : C ≌ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance essSurj_inverse (e : C ≌ E) : e.inverse.EssSurj :=
  e.symm.essSurj_functor

/-- The functor of an equivalence of categories is fully faithful. -/
/-
**CategoryTheory.Equivalence.fullyFaithfulFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：fullyFaithfulFunctor (e : C ≌ E) : e.functor.FullyFaithful where preimage 
{X Y} f
参数：e : C ≌ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor of an equivalence of categories is fully faithful.
-/
def fullyFaithfulFunctor (e : C ≌ E) : e.functor.FullyFaithful where
  preimage {X Y} f := e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

/-- The inverse of an equivalence of categories is fully faithful. -/
/-
**CategoryTheory.Equivalence.fullyFaithfulInverse** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：fullyFaithfulInverse (e : C ≌ E) : e.inverse.FullyFaithful where preimage 
{X Y} f
参数：e : C ≌ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an equivalence of categories is fully faithful.
-/
def fullyFaithfulInverse (e : C ≌ E) : e.inverse.FullyFaithful where
  preimage {X Y} f := e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

/-- The functor of an equivalence of categories is faithful. -/
@[stacks 02C3]
/-
**CategoryTheory.Equivalence.faithful_functor** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：faithful_functor (e : C ≌ E) : e.functor.Faithful
参数：e : C ≌ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective

--- 原说明 ---
The functor of an equivalence of categories is faithful.
-/
instance faithful_functor (e : C ≌ E) : e.functor.Faithful :=
  e.fullyFaithfulFunctor.faithful
/-
**CategoryTheory.Equivalence.faithful_inverse** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：faithful_inverse (e : C ≌ E) : e.inverse.Faithful
参数：e : C ≌ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance faithful_inverse (e : C ≌ E) : e.inverse.Faithful :=
  e.fullyFaithfulInverse.faithful

/-- The functor of an equivalence of categories is full. -/
@[stacks 02C3]
/-
**CategoryTheory.Equivalence.full_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Equivalence`。
形式化陈述：full_functor (e : C ≌ E) : e.functor.Full
参数：e : C ≌ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive

--- 原说明 ---
The functor of an equivalence of categories is full.
-/
instance full_functor (e : C ≌ E) : e.functor.Full :=
  e.fullyFaithfulFunctor.full
/-
**CategoryTheory.Equivalence.full_inverse** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Equivalence`。
形式化陈述：full_inverse (e : C ≌ E) : e.inverse.Full
参数：e : C ≌ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance full_inverse (e : C ≌ E) : e.inverse.Full :=
  e.fullyFaithfulInverse.full

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose functor is `G`. -/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Equivalence.changeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：changeFunctor (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G) : C ≌ D where 
functor
参数：e : C ≌ D；iso : e.functor ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose functor is `G`.
-/
def changeFunctor (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G) : C ≌ D where
  functor := G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso

/-- Compatibility of `changeFunctor` with identity isomorphisms of functors -/
/-
**CategoryTheory.Equivalence.changeFunctor_refl** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Equivalence`。
形式化陈述：changeFunctor_refl (e : C ≌ D) : e.changeFunctor (Iso.refl _) = e
参数：e : C ≌ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.ext`：∀ {C : Type u₁} {D : Type u₂} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D} 
  {x y : C ≌ D},   x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.changeFunctor_unitIso_hom_app`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (e : C ≌ D) {G : C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Equivalence.changeFunctor_counitIso_hom_app`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   (e : C ≌ D) {G : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Compatibility of `changeFunctor` with identity isomorphisms of functors
-/
theorem changeFunctor_refl (e : C ≌ D) : e.changeFunctor (Iso.refl _) = e := by cat_disch

/-- Compatibility of `changeFunctor` with the composition of isomorphisms of functors -/
/-
**CategoryTheory.Equivalence.changeFunctor_trans** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Equivalence`。
形式化陈述：changeFunctor_trans (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso
₂ : G ≅ G') : (e.changeFunctor iso₁).changeFunctor iso₂ = e.changeFunctor (iso₁ 
≪≫ iso₂)
参数：e : C ≌ D；iso₁ : e.functor ≅ G；iso₂ : G ≅ G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.ext`：∀ {C : Type u₁} {D : Type u₂} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v₂, u₂} D} 
  {x y : C ≌ D},   x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equivalence.changeFunctor_unitIso_hom_app`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (e : C ≌ D) {G : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.changeFunctor_counitIso_hom_app`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   (e : C ≌ D) {G : C…

--- 原说明 ---
Compatibility of `changeFunctor` with the composition of isomorphisms of functor
s
-/
theorem changeFunctor_trans (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G') :
    (e.changeFunctor iso₁).changeFunctor iso₂ = e.changeFunctor (iso₁ ≪≫ iso₂) := by cat_disch

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose inverse is `G`. -/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Equivalence.changeInverse** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Equivalence`。
形式化陈述：changeInverse (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G) : C ≌ D where 
functor
参数：e : C ≌ D；iso : e.inverse ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose inverse is `G`.
-/
def changeInverse (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G) : C ≌ D where
  functor := e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc, assoc, iso.hom_inv_id_app, comp_id, functor_unit_comp]

end Equivalence

/-- A functor is an equivalence of categories if it is faithful, full and
essentially surjective. -/
/-
**CategoryTheory.Functor.IsEquivalence** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is an equivalence of categories if it is faithful, full and
essentially surjective.
-/
class Functor.IsEquivalence (F : C ⥤ D) : Prop where
  faithful : F.Faithful := by infer_instance
  full : F.Full := by infer_instance
  essSurj : F.EssSurj := by infer_instance
/-
**CategoryTheory.Equivalence.isEquivalence_functor** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ≌ D), F.functor.IsEquival
ence
参数：F : C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Equivalence.isEquivalence_functor (F : C ≌ D) : IsEquivalence F.functor where
/-
**CategoryTheory.Equivalence.isEquivalence_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : C ≌ D), F.inverse.IsEquival
ence
参数：F : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance Equivalence.isEquivalence_inverse (F : C ≌ D) : IsEquivalence F.inverse :=
  F.symm.isEquivalence_functor

namespace Functor

namespace IsEquivalence

attribute [instance] faithful full essSurj

/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
/-
**CategoryTheory.Functor.IsEquivalence.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsEquivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 (G : CategoryTheory.Functor D C) (η : CategoryTheory.Functor.id C ≅ F.comp G)  
 (ε : G.comp F ≅ CategoryTheory.Functor.id D), F.IsEquivalence
参数：G : CategoryTheory.Functor D C；η : CategoryTheory.Functor.id C ≅ F.comp G；ε :
 G.comp F ≅ CategoryTheory.Functor.id D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To see that a functor is an equivalence, it suffices to provide an inverse funct
or `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors.
-/
protected lemma mk' {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    IsEquivalence F :=
  inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)

end IsEquivalence

/-- A quasi-inverse `D ⥤ C` to a functor that `F : C ⥤ D` that is an equivalence,
i.e. faithful, full, and essentially surjective. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.inv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：inv (F : C ⥤ D) [F.IsEquivalence] : D ⥤ C where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A quasi-inverse `D ⥤ C` to a functor that `F : C ⥤ D` that is an equivalence,
i.e. faithful, full, and essentially surjective.
-/
noncomputable def inv (F : C ⥤ D) [F.IsEquivalence] : D ⥤ C where
  obj X := F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp {X Y Z} f g := by apply F.map_injective; simp

/-- Interpret a functor that is an equivalence as an equivalence. -/
@[simps functor, simps -isSimp inverse, simps! -isSimp unitIso_hom_app unitIso_inv_app
  counitIso_hom_app counitIso_inv_app, stacks 02C3]
/-
**CategoryTheory.Functor.asEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：asEquivalence (F : C ⥤ D) [F.IsEquivalence] : C ≌ D where functor
参数：F : C ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
noncomputable def asEquivalence (F : C ⥤ D) [F.IsEquivalence] : C ≌ D where
  functor := F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])
/-
**CategoryTheory.Functor.isEquivalence_refl** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isEquivalence_refl : IsEquivalence (𝟭 C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance isEquivalence_refl : IsEquivalence (𝟭 C) :=
  Equivalence.refl.isEquivalence_functor
/-
**CategoryTheory.Functor.isEquivalence_inv** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：isEquivalence_inv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance isEquivalence_inv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  F.asEquivalence.symm.isEquivalence_functor

variable {E : Type u₃} [Category.{v₃} E]
/-
**CategoryTheory.Functor.isEquivalence_trans** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [F.IsEquivalence] [G.IsEquivalence], (F.comp G).IsEquivalence
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Full.comp`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance isEquivalence_trans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] :
    IsEquivalence (F ⋙ G) where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringLeft C D E).obj F) :=
  inferInstanceAs <| IsEquivalence (Equivalence.congrLeft F.asEquivalence).inverse
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringRight E C D).obj F) :=
  inferInstanceAs <| IsEquivalence (Equivalence.congrRight F.asEquivalence).functor

end Functor

namespace Functor

@[simp]
/-
**CategoryTheory.Functor.fun_inv_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) : F.map (F
.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y
参数：F : C ⥤ D；X Y : D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_2`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y :=
  (NatIso.naturality_2 (α := F.asEquivalence.counitIso) (f := f)).symm

@[simp]
/-
**CategoryTheory.Functor.inv_fun_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) : F.inv.ma
p (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y
参数：F : C ⥤ D；X Y : C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y :=
  (NatIso.naturality_1 (α := F.asEquivalence.unitIso) (f := f)).symm
/-
**CategoryTheory.Functor.isEquivalence_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：isEquivalence_of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEqu
ivalence
参数：e : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma isEquivalence_of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence :=
  ((asEquivalence F).changeFunctor e).isEquivalence_functor
/-
**CategoryTheory.Functor.isEquivalence_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：isEquivalence_iff_of_iso {F G : C ⥤ D} (e : F ≅ G) : F.IsEquivalence ↔ G.I
sEquivalence
参数：e : F ≅ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_iso`：isEquivalence_of_iso {F G :
 C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence
-/
lemma isEquivalence_iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsEquivalence ↔ G.IsEquivalence :=
  ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

/-- If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalence. -/
/-
**CategoryTheory.Functor.isEquivalence_of_comp_right** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：isEquivalence_of_comp_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤
 E) [IsEquivalence G] [IsEquivalence (F ⋙ G)] : IsEquivalence F
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isEquivalence_iff_of_iso`：isEquivalence_iff_of_is
o {F G : C ⥤ D} (e : F ≅ G) : F.IsEquivalence ↔ G.IsEquivalence
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalenc
e.
-/
lemma isEquivalence_of_comp_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence G] [IsEquivalence (F ⋙ G)] : IsEquivalence F := by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

/-- If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalence. -/
/-
**CategoryTheory.Functor.isEquivalence_of_comp_left** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：isEquivalence_of_comp_left {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ 
E) [IsEquivalence F] [IsEquivalence (F ⋙ G)] : IsEquivalence G
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.isEquivalence_iff_of_iso`：isEquivalence_iff_of_is
o {F G : C ⥤ D} (e : F ≅ G) : F.IsEquivalence ↔ G.IsEquivalence
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalenc
e.
-/
lemma isEquivalence_of_comp_left {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence F] [IsEquivalence (F ⋙ G)] : IsEquivalence G := by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

end Functor

namespace Equivalence

/-
**CategoryTheory.Equivalence.essSurjInducedFunctor** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : (inducedFunctor e).EssSu
rj where mem_essImage Y
参数：e : C' ≃ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
instance essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : (inducedFunctor e).EssSurj where
  mem_essImage Y := ⟨e.symm Y, by simpa using ⟨default⟩⟩
/-
**CategoryTheory.Equivalence.inducedFunctorOfEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：∀ {D : Type u₂} [inst : CategoryTheory.Category.{v₂, u₂} D] {C' : Type u_1
} (e : C' ≃ D),   (CategoryTheory.inducedFunctor ⇑e).IsEquivalence
参数：e : C' ≃ D；CategoryTheory.inducedFunctor ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InducedCategory.faithful`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.induced
Functor F).Faithful
· 使用定理 `CategoryTheory.InducedCategory.full`：∀ {C : Type u₁} {D : Type u₂} [inst
 : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.inducedFunc
tor F).Full
-/
noncomputable instance inducedFunctorOfEquiv {C' : Type*} (e : C' ≃ D) :
    IsEquivalence (inducedFunctor e) where
/-
**CategoryTheory.Equivalence.fullyFaithfulToEssImage** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Equivalence`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.Full] [F.Faithful], F.toEssImage.IsEquivalence
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.toEssImage`：∀ {C : Type u₁} {D : Type u₂
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Full.toEssImage`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.EssSurj.toEssImage`：∀ {C : Type u₁} {D : Type u₂}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
-/
noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [F.Full] [F.Faithful] :
    IsEquivalence F.toEssImage where

end Equivalence

/-- An equality of properties of objects of a category `C` induces an equivalence of the
respective induced full subcategories of `C`. -/
@[simps]
/-
**CategoryTheory.ObjectProperty.fullSubcategoryCongr** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P P' 
: CategoryTheory.ObjectProperty C} → P = P' → (P.FullSubcategory ≌ P'.FullSubcat
egory)
参数：P.FullSubcategory ≌ P'.FullSubcategory。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of properties of objects of a category `C` induces an equivalence of
 the
respective induced full subcategories of `C`.
-/
def ObjectProperty.fullSubcategoryCongr {P P' : ObjectProperty C} (h : P = P') :
    P.FullSubcategory ≌ P'.FullSubcategory where
  functor := ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.symm.le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

namespace Iso

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E}

/-- Construct an isomorphism `F ⋙ H.inverse ≅ G` from an isomorphism `F ≅ G ⋙ H.functor`. -/
@[simps!]
/-
**CategoryTheory.Iso.compInverseIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：compInverseIso {H : D ≌ E} (i : F ≅ G ⋙ H.functor) : F ⋙ H.inverse ≅ G
参数：i : F ≅ G ⋙ H.functor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism `F ⋙ H.inverse ≅ G` from an isomorphism `F ≅ G ⋙ H.func
tor`.
-/
def compInverseIso {H : D ≌ E} (i : F ≅ G ⋙ H.functor) : F ⋙ H.inverse ≅ G :=
  isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

/-- Construct an isomorphism `G ≅ F ⋙ H.inverse` from an isomorphism `G ⋙ H.functor ≅ F`. -/
@[simps!]
/-
**CategoryTheory.Iso.isoCompInverse** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：isoCompInverse {H : D ≌ E} (i : G ⋙ H.functor ≅ F) : G ≅ F ⋙ H.inverse
参数：i : G ⋙ H.functor ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism `G ≅ F ⋙ H.inverse` from an isomorphism `G ⋙ H.functor 
≅ F`.
-/
def isoCompInverse {H : D ≌ E} (i : G ⋙ H.functor ≅ F) : G ≅ F ⋙ H.inverse :=
  G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

/-- Construct an isomorphism `G.inverse ⋙ F ≅ H` from an isomorphism `F ≅ G.functor ⋙ H`. -/
@[simps!]
/-
**CategoryTheory.Iso.inverseCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：inverseCompIso {G : C ≌ D} (i : F ≅ G.functor ⋙ H) : G.inverse ⋙ F ≅ H
参数：i : F ≅ G.functor ⋙ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism `G.inverse ⋙ F ≅ H` from an isomorphism `F ≅ G.functor 
⋙ H`.
-/
def inverseCompIso {G : C ≌ D} (i : F ≅ G.functor ⋙ H) : G.inverse ⋙ F ≅ H :=
  isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

/-- Construct an isomorphism `H ≅ G.inverse ⋙ F` from an isomorphism `G.functor ⋙ H ≅ F`. -/
@[simps!]
/-
**CategoryTheory.Iso.isoInverseComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：isoInverseComp {G : C ≌ D} (i : G.functor ⋙ H ≅ F) : H ≅ G.inverse ⋙ F
参数：i : G.functor ⋙ H ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism `H ≅ G.inverse ⋙ F` from an isomorphism `G.functor ⋙ H 
≅ F`.
-/
def isoInverseComp {G : C ≌ D} (i : G.functor ⋙ H ≅ F) : H ≅ G.inverse ⋙ F :=
  H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.inverse ≅ G.inverse` from an isomorphism `G.functor ≅ G.functor`. -/
@[simps!]
/-
**CategoryTheory.Iso.isoInverseOfIsoFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Iso`。
形式化陈述：isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) : G.inv
erse ≅ G'.inverse
参数：i : G.functor ≅ G'.functor。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a special case, given two equivalences `G` and `G'` between the same categori
es,
construct an isomorphism `G.inverse ≅ G.inverse` from an isomorphism `G.functor 
≅ G.functor`.
-/
def isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) : G.inverse ≅ G'.inverse :=
  isoCompInverse ((isoWhiskerLeft G.inverse i).symm ≪≫ G.counitIso) ≪≫ leftUnitor G'.inverse

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.functor ≅ G.functor` from an isomorphism `G.inverse ≅ G.inverse`. -/
@[simps!]
/-
**CategoryTheory.Iso.isoFunctorOfIsoInverse** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Iso`。
形式化陈述：isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) : G.fun
ctor ≅ G'.functor
参数：i : G.inverse ≅ G'.inverse。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a special case, given two equivalences `G` and `G'` between the same categori
es,
construct an isomorphism `G.functor ≅ G.functor` from an isomorphism `G.inverse 
≅ G.inverse`.
-/
def isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) : G.functor ≅ G'.functor :=
  isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

/-- Sanity check: `isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i)` is just `i`. -/
@[simp]
/-
**CategoryTheory.Iso.isoFunctorOfIsoInverse_isoInverseOfIsoFunctor** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：isoFunctorOfIsoInverse_isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functo
r ≅ G'.functor) : isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i) = i
参数：i : G.functor ≅ G'.functor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isoFunctorOfIsoInverse_hom_app`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {G G' : C ≌ D} (i …
· 使用定理 `CategoryTheory.Iso.isoInverseOfIsoFunctor_inv_app`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {G G' : C ≌ D} (i …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Equivalence.counitInv_functor_comp_assoc`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (e : C ≌ D) (X : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Sanity check: `isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i)` is just `i`.
-/
lemma isoFunctorOfIsoInverse_isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) :
    isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i) = i := by
  ext X
  simp [← NatTrans.naturality]

@[simp]
/-
**CategoryTheory.Iso.isoInverseOfIsoFunctor_isoFunctorOfIsoInverse** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：isoInverseOfIsoFunctor_isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.invers
e ≅ G'.inverse) : isoInverseOfIsoFunctor (isoFunctorOfIsoInverse i) = i
参数：i : G.inverse ≅ G'.inverse。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Iso.isoFunctorOfIsoInverse_isoInverseOfIsoFunctor`：isoFun
ctorOfIsoInverse_isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.funct
or) : isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i…
-/
lemma isoInverseOfIsoFunctor_isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) :
    isoInverseOfIsoFunctor (isoFunctorOfIsoInverse i) = i :=
  isoFunctorOfIsoInverse_isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

end Iso

end CategoryTheory

