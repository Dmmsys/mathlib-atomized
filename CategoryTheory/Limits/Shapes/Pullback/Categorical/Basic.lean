/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.CatCospanTransform

/-! # Categorical pullbacks

This file defines the basic properties of categorical pullbacks.

Given a pair of functors `(F : A ⥤ B, G : C ⥤ B)`, we define the category
`CategoricalPullback F G` as the category of triples
`(a : A, c : C, e : F.obj a ≅ G.obj b)`.

The category `CategoricalPullback F G` sits in a canonical `CatCommSq`, and we formalize that
this square is a "limit" in the following sense: functors `X ⥤ CategoricalPullback F G` are
equivalent to pairs of functors `(L : X ⥤ A, R : X ⥤ C)` equipped with a natural isomorphism
`L ⋙ F ≅ R ⋙ G`.

We formalize this by introducing a category `CatCommSqOver F G X` that encodes
exactly this data, and we prove that the category of functors `X ⥤ CategoricalPullback F G` is
equivalent to `CatCommSqOver F G X`.

## Main declarations

* `CategoricalPullback F G`: the type of the categorical pullback.
* `π₁ F G : CategoricalPullback F G` and `π₂ F G : CategoricalPullback F G`: the canonical
  projections.
* `CategoricalPullback.catCommSq`: the canonical `CatCommSq (π₁ F G) (π₂ F G) F G` which exhibits
  `CategoricalPullback F G` as the pullback (in the (2,1)-categorical sense)
  of the cospan of `F` and `G`.
* `CategoricalPullback.functorEquiv F G X`: the equivalence of categories between functors
  `X ⥤ CategoricalPullback F G` and `CatCommSqOver F G X`, where the latter is an abbrev for
  `CategoricalPullback (whiskeringRight X A B|>.obj F) (whiskeringRight X C B|>.obj G)`.

## References
* [Kerodon: section 1.4.5.2](https://kerodon.net/tag/032Y)
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
  example 5.3.9, although we take a slightly different (equivalent) model of the object.

## TODOs:
* 2-functoriality of the construction with respect to "transformation of categorical
  cospans".
* Full equivalence-invariance of the notion (follows from suitable 2-functoriality).
* Define a `CatPullbackSquare` typeclass extending `CatCommSq`that encodes the
  fact that a given `CatCommSq` defines an equivalence between the top left
  corner and the categorical pullback of its legs.
* Define a `IsCatPullbackSquare` propclass.
* Define the "categorical fiber" of a functor at an object of the target category.
* Pasting calculus for categorical pullback squares.
* Categorical pullback squares attached to Grothendieck constructions of pseudofunctors.
* Stability of (co)fibered categories under categorical pullbacks.

### Implementations note:
In this file, a few proofs could be removed in favor of letting autoParams fill them
in automatically: they are kept intentionally for performance reasons.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃

namespace CategoryTheory.Limits

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)

/-- The `CategoricalPullback F G` is the category of triples
`(a : A, c : C, F a ≅ G c)`.
Morphisms `(a, c, e) ⟶ (a', c', e')` are pairs of morphisms
`(f₁ : a ⟶ a', f₂ : c ⟶ c')` compatible with the specified
isomorphisms. -/
@[kerodon 032Z]
/-
**CategoryTheory.Limits.CategoricalPullback** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：{A : Type u₁} →   {B : Type u₂} →     {C : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} A] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} B] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             Ca
tegoryTheory.Functor A B → CategoryTheory.Functor C B → Type (max (max u₁ u₃) v₂
)
参数：max (max u₁ u₃) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `CategoricalPullback F G` is the category of triples
`(a : A, c : C, F a ≅ G c)`.
Morphisms `(a, c, e) ⟶ (a', c', e')` are pairs of morphisms
`(f₁ : a ⟶ a', f₂ : c ⟶ c')` compatible with the specified
isomorphisms.
-/
structure CategoricalPullback where
  /-- the first component element -/
  fst : A
  /-- the second component element -/
  snd : C
  /-- the structural isomorphism `F.obj fst ≅ G.obj snd` -/
  iso : F.obj fst ≅ G.obj snd

namespace CategoricalPullback

/-- A notation for the categorical pullback. -/
scoped notation:max L:max " ⊡ " R:max => CategoricalPullback L R

variable {F G}

/-- The Hom types for the categorical pullback are given by pairs of maps compatible with the
structural isomorphisms. -/
@[ext]
/-
**CategoryTheory.Limits.CategoricalPullback.Hom** 是 Mathlib 中的一个结构，位于命名空间 `Categ
oryTheory.Limits.CategoricalPullback`。
形式化陈述：Hom (x y : F ⊡ G) where /-- the first component of `f : Hom x y` is a morp
hism `x.fst ⟶ y.fst` -/ fst : x.fst ⟶ y.fst /-- the second component of `f : Hom
 x y` is a morphism `x.snd ⟶ y.snd` -/ snd : x.snd ⟶ y.snd /-- the compatibility
 condition on `fst` and `snd` with respect to the structure isomorphisms -/ w : 
F.map fst ≫ y.iso.hom = x.iso.hom ≫ G.map snd
参数：x y : F ⊡ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hom types for the categorical pullback are given by pairs of maps compatible
 with the
structural isomorphisms.
-/
structure Hom (x y : F ⊡ G) where
  /-- the first component of `f : Hom x y` is a morphism `x.fst ⟶ y.fst` -/
  fst : x.fst ⟶ y.fst
  /-- the second component of `f : Hom x y` is a morphism `x.snd ⟶ y.snd` -/
  snd : x.snd ⟶ y.snd
  /-- the compatibility condition on `fst` and `snd` with respect to the structure
  isomorphisms -/
  w : F.map fst ≫ y.iso.hom = x.iso.hom ≫ G.map snd := by cat_disch

attribute [reassoc (attr := simp)] Hom.w

@[simps! id_fst id_snd comp_fst comp_snd]
/-
**CategoryTheory.Limits.CategoricalPullback.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.CategoricalPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CategoricalPullback F G) where
  Hom x y := CategoricalPullback.Hom x y
  id x :=
    { fst := 𝟙 x.fst
      snd := 𝟙 x.snd }
  comp f g :=
    { fst := f.fst ≫ g.fst
      snd := f.snd ≫ g.snd }

attribute [reassoc] comp_fst comp_snd

/-- Naturality square for morphisms in the inverse direction. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CategoricalPullback.Hom.w'** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.CategoricalPullback.Hom`。
形式化陈述：∀ {A : Type u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Categor
y.{v₁, u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [inst_2 : Category
Theory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor A B} {G : CategoryTheo
ry.Functor C B}   {x y : CategoryTheory.Limits.CategoricalPullback F G} (f : x ⟶
 y),   CategoryTheory.CategoryStruct.comp (G.map f.snd) y.iso.inv =     Category
Theory.CategoryStruct.comp x.iso.inv (F.map f.fst)
参数：f : x ⟶ y；G.map f.snd；F.map f.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.Hom.w`：∀ {A : Type u₁} {B : Ty
pe u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} B] [ins…

--- 原说明 ---
Naturality square for morphisms in the inverse direction.
-/
lemma Hom.w' {x y : F ⊡ G} (f : x ⟶ y) :
    G.map f.snd ≫ y.iso.inv = x.iso.inv ≫ F.map f.fst := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, f.w]

/-- Extensionality principle for morphisms in `CategoricalPullback F G`. -/
@[ext]
/-
**CategoryTheory.Limits.CategoricalPullback.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.CategoricalPullback`。
形式化陈述：hom_ext {x y : F ⊡ G} {f g : x ⟶ y} (hₗ : f.fst = g.fst) (hᵣ : f.snd = g.s
nd) : f = g
参数：hₗ : f.fst = g.fst；hᵣ : f.snd = g.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.Hom.ext`：∀ {A : Type u₁} {B : 
Type u₂} {C : Type u₃} {inst : CategoryTheory.Category.{v₁, u₁} A}   {inst_1 : C
ategoryTheory.Category.{v₂, u₂} B} {ins…

--- 原说明 ---
Extensionality principle for morphisms in `CategoricalPullback F G`.
-/
theorem hom_ext {x y : F ⊡ G} {f g : x ⟶ y}
    (hₗ : f.fst = g.fst) (hᵣ : f.snd = g.snd) : f = g := by
  apply Hom.ext <;> assumption

section

variable (F G)

/-- `CategoricalPullback.π₁ F G` is the first projection `CategoricalPullback F G ⥤ A`. -/
@[simps]
/-
**CategoryTheory.Limits.CategoricalPullback.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.CategoricalPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoricalPullback.π₁ F G` is the first projection `CategoricalPullback F G ⥤ 
A`.
-/
def π₁ : F ⊡ G ⥤ A where
  obj x := x.fst
  map f := f.fst

/-- `CategoricalPullback.π₂ F G` is the second projection `CategoricalPullback F G ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Limits.CategoricalPullback.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.CategoricalPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CategoricalPullback.π₂ F G` is the second projection `CategoricalPullback F G ⥤
 C`.
-/
def π₂ : F ⊡ G ⥤ C where
  obj x := x.snd
  map f := f.snd

set_option backward.defeqAttrib.useBackward true in
/-- The canonical categorical commutative square in which `CategoricalPullback F G` sits. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.catCommSq** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：catCommSq : CatCommSq (π₁ F G) (π₂ F G) F G where iso
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical categorical commutative square in which `CategoricalPullback F G` 
sits.
-/
instance catCommSq : CatCommSq (π₁ F G) (π₂ F G) F G where
  iso := NatIso.ofComponents (fun x ↦ x.iso)

variable {F G} in
/-- Constructor for isomorphisms in `CategoricalPullback F G`. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.CategoricalPullback`。
形式化陈述：mkIso {x y : F ⊡ G} (eₗ : x.fst ≅ y.fst) (eᵣ : x.snd ≅ y.snd) (w : F.map e
ₗ.hom ≫ y.iso.hom = x.iso.hom ≫ G.map eᵣ.hom
参数：eₗ : x.fst ≅ y.fst；eᵣ : x.snd ≅ y.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `CategoricalPullback F G`.
-/
def mkIso {x y : F ⊡ G}
    (eₗ : x.fst ≅ y.fst) (eᵣ : x.snd ≅ y.snd)
    (w : F.map eₗ.hom ≫ y.iso.hom = x.iso.hom ≫ G.map eᵣ.hom := by cat_disch) :
    x ≅ y where
  hom := ⟨eₗ.hom, eᵣ.hom, w⟩
  inv := ⟨eₗ.inv, eᵣ.inv, by simpa using F.map eₗ.inv ≫= w.symm =≫ G.map eᵣ.inv⟩

section

variable {x y : F ⊡ G} (f : x ⟶ y) [IsIso f]

/-
**CategoryTheory.Limits.CategoricalPullback.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.CategoricalPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso f.fst :=
  inferInstanceAs (IsIso ((π₁ _ _).mapIso (asIso f)).hom)
/-
**CategoryTheory.Limits.CategoricalPullback.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits.CategoricalPullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso f.snd :=
  inferInstanceAs (IsIso ((π₂ _ _).mapIso (asIso f)).hom)

@[simp, push ←]
/-
**CategoryTheory.Limits.CategoricalPullback.inv_fst** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CategoricalPullback`。
形式化陈述：inv_fst : (inv f).fst = inv f.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.instIsIsoFst`：∀ {A : Type u₁} 
{B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_
1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_fst : (inv f).fst = inv f.fst := by
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_fst]

@[simp, push ←]
/-
**CategoryTheory.Limits.CategoricalPullback.inv_snd** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.CategoricalPullback`。
形式化陈述：inv_snd : (inv f).snd = inv f.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.instIsIsoSnd`：∀ {A : Type u₁} 
{B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_
1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_snd : (inv f).snd = inv f.snd := by
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  simp [← comp_snd]

end

/-
**CategoryTheory.Limits.CategoricalPullback.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：isIso_iff {x y : F ⊡ G} (f : x ⟶ y) : IsIso f ↔ (IsIso f.fst ∧ IsIso f.snd
) where mp h
参数：f : x ⟶ y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.instIsIsoFst`：∀ {A : Type u₁} 
{B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_
1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.instIsIsoSnd`：∀ {A : Type u₁} 
{B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_
1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.Hom.w`：∀ {A : Type u₁} {B : Ty
pe u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.hom_ext`：hom_ext {x y : F ⊡ G}
 {f g : x ⟶ y} (hₗ : f.fst = g.fst) (hᵣ : f.snd = g.snd) : f = g
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
lemma isIso_iff {x y : F ⊡ G} (f : x ⟶ y) :
    IsIso f ↔ (IsIso f.fst ∧ IsIso f.snd) where
  mp h := ⟨inferInstance, inferInstance⟩
  mpr | ⟨h₁, h₂⟩ => ⟨⟨inv f.fst, inv f.snd, by cat_disch⟩, by cat_disch⟩

end

section

open CategoryTheory.Functor

variable (X : Type u₄) [Category.{v₄} X]

variable (F G) in
/-- The data of a categorical commutative square over a cospan `F, G` with cone point `X` is
that of a functor `T : X ⥤ A`, a functor `L : X ⥤ C`, and a `CatCommSq T L F G`.
Note that this is *exactly* what an object of
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)` is,
so `CatCommSqOver F G X` is in equivalent to
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)`,
though it is defined separately for performance reasons. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver** 是 Mathlib 中的一个归纳类型，位
于命名空间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：{A : Type u₁} →   {B : Type u₂} →     {C : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} A] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} B] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             Ca
tegoryTheory.Functor A B →               CategoryTheory.Functor C B →           
      (X : Type u₄) →                   [CategoryTheory.Category.{v₄, u₄} X] → T
ype (max (max (max (max (max (max u₁ u₃) u₄) v₁) v₂) v₃) v₄)
参数：X : Type u₄；max (max (max (max (max (max u₁ u₃) u₄) v₁) v₂) v₃) v₄。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a categorical commutative square over a cospan `F, G` with cone poin
t `X` is
that of a functor `T : X ⥤ A`, a functor `L : X ⥤ C`, and a `CatCommSq T L F G`.
Note that this is *exactly* what an object of
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)` is,
so `CatCommSqOver F G X` is in equivalent to
`((whiskeringRight X A B).obj F) ⊡ ((whiskeringRight X C B).obj G)`,
though it is defined separately for performance reasons.
-/
structure CatCommSqOver where
  /-- The first projection functor. -/
  fst : X ⥤ A
  /-- The second projection functor. -/
  snd : X ⥤ C
  /-- The structural natural isomorphism. -/
  iso : fst ⋙ F ≅ snd ⋙ G

namespace CatCommSqOver

/-- The Hom types for the categorical commutative squares over X are given by pairs of natural
transformations compatible with the structural isomorphisms. -/
@[ext]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Hom** 是 Mathlib 中的一个结构
，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：Hom (x y : CatCommSqOver F G X) where /-- the first component of `f : Hom 
x y` is a morphism `x.fst ⟶ y.fst` -/ fst : x.fst ⟶ y.fst /-- the second compone
nt of `f : Hom x y` is a morphism `x.snd ⟶ y.snd` -/ snd : x.snd ⟶ y.snd /-- the
 compatibility condition on `fst` and `snd` with respect to the structure isomor
phisms -/ w : whiskerRight fst F ≫ y.iso.hom = x.iso.hom ≫ whiskerRight snd G
参数：x y : CatCommSqOver F G X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hom types for the categorical commutative squares over X are given by pairs 
of natural
transformations compatible with the structural isomorphisms.
-/
structure Hom (x y : CatCommSqOver F G X) where
  /-- the first component of `f : Hom x y` is a morphism `x.fst ⟶ y.fst` -/
  fst : x.fst ⟶ y.fst
  /-- the second component of `f : Hom x y` is a morphism `x.snd ⟶ y.snd` -/
  snd : x.snd ⟶ y.snd
  /-- the compatibility condition on `fst` and `snd` with respect to the structure
  isomorphisms -/
  w : whiskerRight fst F ≫ y.iso.hom = x.iso.hom ≫ whiskerRight snd G := by cat_disch

attribute [reassoc (attr := simp)] Hom.w

@[simps! id_fst_app id_snd_app comp_fst_app comp_snd_app]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CatCommSqOver F G X) where
  Hom x y := CatCommSqOver.Hom X x y
  id x :=
    { fst := 𝟙 x.fst
      snd := 𝟙 x.snd }
  comp f g :=
    { fst := f.fst ≫ g.fst
      snd := f.snd ≫ g.snd }

@[ext]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：hom_ext {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (
h₂ : f.snd = g.snd) : f = g
参数：h₁ : f.fst = g.fst；h₂ : f.snd = g.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Hom.ext`：∀ {A : 
Type u₁} {B : Type u₂} {C : Type u₃} {inst : CategoryTheory.Category.{v₁, u₁} A}
   {inst_1 : CategoryTheory.Category.{v₂, u₂} B} {ins…
-/
lemma hom_ext {S S' : CatCommSqOver F G X} {f g : S ⟶ S'}
    (h₁ : f.fst = g.fst) (h₂ : f.snd = g.snd) : f = g :=
  Hom.ext h₁ h₂

/-- Interpret a `CatCommSqOver F G X` as a `CatCommSq`. -/
@[simps]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.asSquare** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：asSquare (S : CatCommSqOver F G X) : CatCommSq S.fst S.snd F G where iso
参数：S : CatCommSqOver F G X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `CatCommSqOver F G X` as a `CatCommSq`.
-/
instance asSquare (S : CatCommSqOver F G X) : CatCommSq S.fst S.snd F G where
  iso := S.iso

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.iso_hom_naturality** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`
。
形式化陈述：iso_hom_naturality (S : CatCommSqOver F G X) {x x' : X} (f : x ⟶ x') : F.m
ap (S.fst.map f) ≫ S.iso.hom.app x' = S.iso.hom.app x ≫ G.map (S.snd.map f)
参数：S : CatCommSqOver F G X；f : x ⟶ x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma iso_hom_naturality (S : CatCommSqOver F G X) {x x' : X} (f : x ⟶ x') :
    F.map (S.fst.map f) ≫ S.iso.hom.app x' =
    S.iso.hom.app x ≫ G.map (S.snd.map f) :=
  S.iso.hom.naturality f

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.w_app** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：w_app {S S' : CatCommSqOver F G X} (φ : S ⟶ S') (x : X) : F.map (φ.fst.app
 x) ≫ S'.iso.hom.app x = S.iso.hom.app x ≫ G.map (φ.snd.app x)
参数：φ : S ⟶ S'；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.Hom.w`：∀ {A : Ty
pe u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]  
 [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
-/
lemma w_app {S S' : CatCommSqOver F G X} (φ : S ⟶ S') (x : X) :
    F.map (φ.fst.app x) ≫ S'.iso.hom.app x =
    S.iso.hom.app x ≫ G.map (φ.snd.app x) :=
  NatTrans.congr_app φ.w x

variable (F G)

/-- The "first projection" of a CatCommSqOver as a functor. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.fstFunctor** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：fstFunctor : CatCommSqOver F G X ⥤ X ⥤ A where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "first projection" of a CatCommSqOver as a functor.
-/
def fstFunctor : CatCommSqOver F G X ⥤ X ⥤ A where
  obj S := S.fst
  map f := f.fst

/-- The "second projection" of a CatCommSqOver as a functor. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.sndFunctor** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：sndFunctor : CatCommSqOver F G X ⥤ X ⥤ C where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "second projection" of a CatCommSqOver as a functor.
-/
def sndFunctor : CatCommSqOver F G X ⥤ X ⥤ C where
  obj S := S.snd
  map f := f.snd

set_option backward.defeqAttrib.useBackward true in
/-- The structure isomorphism of a `CatCommSqOver` as a natural transformation. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.e** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：e : fstFunctor F G X ⋙ (whiskeringRight X A B).obj F ≅ sndFunctor F G X ⋙ 
(whiskeringRight X C B).obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure isomorphism of a `CatCommSqOver` as a natural transformation.
-/
def e :
    fstFunctor F G X ⋙ (whiskeringRight X A B).obj F ≅
    sndFunctor F G X ⋙ (whiskeringRight X C B).obj G :=
  NatIso.ofComponents (fun S ↦ S.iso)

set_option backward.defeqAttrib.useBackward true in
variable {F G X} in
/-- A constructor for isomorphisms in CatCommSqOver -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.mkIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：mkIso {S S' : CatCommSqOver F G X} (eₗ : S.fst ≅ S'.fst) (eᵣ : S.snd ≅ S'.
snd) (w : whiskerRight eₗ.hom F ≫ S'.iso.hom = S.iso.hom ≫ whiskerRight eᵣ.hom G
参数：eₗ : S.fst ≅ S'.fst；eᵣ : S.snd ≅ S'.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for isomorphisms in CatCommSqOver
-/
def mkIso {S S' : CatCommSqOver F G X}
    (eₗ : S.fst ≅ S'.fst) (eᵣ : S.snd ≅ S'.snd)
    (w : whiskerRight eₗ.hom F ≫ S'.iso.hom = S.iso.hom ≫ whiskerRight eᵣ.hom G := by cat_disch) :
    S ≅ S' where
  hom := ⟨eₗ.hom, eᵣ.hom, w⟩
  inv := ⟨eₗ.inv, eᵣ.inv, by
    ext t
    simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using
      congr_app (whiskerRight eₗ.inv F ≫= w.symm =≫ whiskerRight eᵣ.inv G) t⟩

end CatCommSqOver

section functorEquiv

variable (F G)

-- We need to split up the definition of `functorEquiv` to avoid timeouts.

set_option backward.defeqAttrib.useBackward true in
/-- Interpret a functor to the categorical pullback as a `CatCommSqOver`. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.toCatCommSqOver** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：toCatCommSqOver : (X ⥤ F ⊡ G) ⥤ CatCommSqOver F G X where obj J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a functor to the categorical pullback as a `CatCommSqOver`.
-/
def toCatCommSqOver : (X ⥤ F ⊡ G) ⥤ CatCommSqOver F G X where
  obj J :=
    { fst := J ⋙ π₁ F G
      snd := J ⋙ π₂ F G
      iso :=
        associator _ _ _ ≪≫
          isoWhiskerLeft J (catCommSq F G).iso ≪≫
          (associator _ _ _).symm }
  map {J J'} F :=
    { fst := whiskerRight F (π₁ _ _)
      snd := whiskerRight F (π₂ _ _) }
  map_id := by intros; ext <;> simp
  map_comp := by intros; ext <;> simp

/-- Interpret a `CatCommSqOver` as a functor to the categorical pullback. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategorical
Pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.Ca
tCommSqOver`。
形式化陈述：{A : Type u₁} →   {B : Type u₂} →     {C : Type u₃} →       [inst : Catego
ryTheory.Category.{v₁, u₁} A] →         [inst_1 : CategoryTheory.Category.{v₂, u
₂} B] →           [inst_2 : CategoryTheory.Category.{v₃, u₃} C] →             (F
 : CategoryTheory.Functor A B) →               (G : CategoryTheory.Functor C B) 
→                 (X : Type u₄) →                   [inst_3 : CategoryTheory.Cat
egory.{v₄, u₄} X] →                     CategoryTheory.Functor (CategoryTheory.L
imits.CategoricalPullback.CatCommSqOver F G X)                       (CategoryTh
eory.Functor X (CategoryTheory.Limits.CategoricalPullback F G))
参数：F : CategoryTheory.Functor A B；G : CategoryTheory.Functor C B；X : Type u₄；Cat
egoryTheory.Limits.CategoricalPullback.CatCommSqOver F G X；CategoryTheory.Functo
r X (CategoryTheory.Limits.CategoricalPullback F G)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `CatCommSqOver` as a functor to the categorical pullback.
-/
def CatCommSqOver.toFunctorToCategoricalPullback :
    (CatCommSqOver F G X) ⥤ X ⥤ F ⊡ G where
  obj S :=
    { obj x :=
        { fst := S.fst.obj x
          snd := S.snd.obj x
          iso := S.iso.app x }
      map {x y} f :=
        { fst := S.fst.map f
          snd := S.snd.map f } }
  map {S S'} φ :=
    { app x :=
        { fst := φ.fst.app x
          snd := φ.snd.app x } }
  map_id := by intros; ext <;> simp
  map_comp := by intros; ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The universal property of categorical pullbacks, stated as an equivalence
of categories between functors `X ⥤ (F ⊡ G)` and categorical commutative squares
over X. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.functorEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：functorEquiv : (X ⥤ F ⊡ G) ≌ CatCommSqOver F G X where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of categorical pullbacks, stated as an equivalence
of categories between functors `X ⥤ (F ⊡ G)` and categorical commutative squares
over X.
-/
def functorEquiv : (X ⥤ F ⊡ G) ≌ CatCommSqOver F G X where
  functor := toCatCommSqOver F G X
  inverse := CatCommSqOver.toFunctorToCategoricalPullback F G X
  unitIso :=
    NatIso.ofComponents
      (fun _ ↦ NatIso.ofComponents (fun _ ↦ CategoricalPullback.mkIso (.refl _) (.refl _)
        (by simp))) (by intros; ext <;> simp)
  counitIso :=
    NatIso.ofComponents
      (fun _ ↦ CatCommSqOver.mkIso
        (NatIso.ofComponents
          (fun _ ↦ .refl _) (by intros; simp))
        (NatIso.ofComponents
          (fun _ ↦ .refl _) (by intros; simp))
        (by ext; simp))
  functor_unitIso_comp := by intros; ext <;> simp

variable {F G X}

set_option backward.defeqAttrib.useBackward true in
/-- A constructor for natural isomorphisms of functors `X ⥤ CategoricalPullback`: to
construct such an isomorphism, it suffices to produce isomorphisms after whiskering with
the projections, and compatible with the canonical 2-commutative square . -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.mkNatIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：mkNatIso {J K : X ⥤ F ⊡ G} (e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G) (e₂ : J ⋙ π₂ F G
 ≅ K ⋙ π₂ F G) (coh : whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫ whiskerLe
ft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫ (associator _ _ _).inv = (assoc
iator _ _ _).hom ≫ whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫ (as
sociator _ _ _).inv ≫ whiskerRight e₂.hom G
参数：e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G；e₂ : J ⋙ π₂ F G ≅ K ⋙ π₂ F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for natural isomorphisms of functors `X ⥤ CategoricalPullback`: to
construct such an isomorphism, it suffices to produce isomorphisms after whisker
ing with
the projections, and compatible with the canonical 2-commutative square .
-/
def mkNatIso {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G) (e₂ : J ⋙ π₂ F G ≅ K ⋙ π₂ F G)
    (coh :
      whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by cat_disch) :
    J ≅ K :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (e₁.app x) (e₂.app x)
      (by simpa using NatTrans.congr_app coh x))
    (fun {_ _} f ↦ by
      ext
      · exact e₁.hom.naturality f
      · exact e₂.hom.naturality f)

/-- To check equality of two natural transformations of functors to a `CategoricalPullback`, it
suffices to do so after whiskering with the projections. -/
@[ext]
/-
**CategoryTheory.Limits.CategoricalPullback.natTrans_ext** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：natTrans_ext {J K : X ⥤ F ⊡ G} {α β : J ⟶ K} (e₁ : whiskerRight α (π₁ F G)
 = whiskerRight β (π₁ F G)) (e₂ : whiskerRight α (π₂ F G) = whiskerRight β (π₂ F
 G)) : α = β
参数：e₁ : whiskerRight α (π₁ F G) = whiskerRight β (π₁ F G)；e₂ : whiskerRight α (π
₂ F G) = whiskerRight β (π₂ F G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.hom_ext`：hom_ext {x y : F ⊡ G}
 {f g : x ⟶ y} (hₗ : f.fst = g.fst) (hᵣ : f.snd = g.snd) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
To check equality of two natural transformations of functors to a `CategoricalPu
llback`, it
suffices to do so after whiskering with the projections.
-/
lemma natTrans_ext
    {J K : X ⥤ F ⊡ G} {α β : J ⟶ K}
    (e₁ : whiskerRight α (π₁ F G) = whiskerRight β (π₁ F G))
    (e₂ : whiskerRight α (π₂ F G) = whiskerRight β (π₂ F G)) :
    α = β := by
  ext x
  · exact congrArg (fun t ↦ t.app x) e₁
  · exact congrArg (fun t ↦ t.app x) e₂

section

variable {J K : X ⥤ F ⊡ G}
    (e₁ : J ⋙ π₁ F G ≅ K ⋙ π₁ F G) (e₂ : J ⋙ π₂ F G ≅ K ⋙ π₂ F G)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Limits.CategoricalPullback.toCatCommSqOver_mapIso_mkNatIso_eq_m
kIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：toCatCommSqOver_mapIso_mkNatIso_eq_mkIso (coh : whiskerRight e₁.hom F ≫ (a
ssociator _ _ _).hom ≫ whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
 (associator _ _ _).inv = (associator _ _ _).hom ≫ whiskerLeft J (CatCommSq.iso 
(π₁ F G) (π₂ F G) F G).hom ≫ (associator _ _ _).inv ≫ whiskerRight e₂.hom G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.toCatCommSqOver_map_fst_app`：∀
 {A : Type u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, 
u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.mkNatIso_hom_app_fst`：∀ {A : T
ype u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] 
  [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.mkIso_hom_fst`：∀
 {A : Type u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, 
u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.toCatCommSqOver_map_snd_app`：∀
 {A : Type u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, 
u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.mkNatIso_hom_app_snd`：∀ {A : T
ype u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] 
  [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.mkIso_hom_snd`：∀
 {A : Type u₁} {B : Type u₂} {C : Type u₃} [inst : CategoryTheory.Category.{v₁, 
u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [ins…
-/
lemma toCatCommSqOver_mapIso_mkNatIso_eq_mkIso
    (coh :
      whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by cat_disch) :
    (toCatCommSqOver F G X).mapIso (mkNatIso e₁ e₂ coh) =
    CatCommSqOver.mkIso e₁ e₂
      (by simpa [functorEquiv, toCatCommSqOver] using coh) := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparing mkNatIso with the corresponding construction one can deduce from
`functorEquiv`. -/
/-
**CategoryTheory.Limits.CategoricalPullback.mkNatIso_eq** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits.CategoricalPullback`。
形式化陈述：mkNatIso_eq (coh : whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫ whiske
rLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫ (associator _ _ _).inv = (as
sociator _ _ _).hom ≫ whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫ 
(associator _ _ _).inv ≫ whiskerRight e₂.hom G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.toCatCommSqOver_mapIso_mkNatIs
o_eq_mkIso`：toCatCommSqOver_mapIso_mkNatIso_eq_mkIso (coh : whiskerRight e₁.hom 
F ≫ (associator _ _ _).hom ≫ whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.natTrans_ext`：natTrans_ext {J 
K : X ⥤ F ⊡ G} {α β : J ⟶ K} (e₁ : whiskerRight α (π₁ F G) = whiskerRight β (π₁ 
F G)) (e₂ : whiskerRight α (π₂ F G) = whiske…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Comparing mkNatIso with the corresponding construction one can deduce from
`functorEquiv`.
-/
lemma mkNatIso_eq
    (coh :
      whiskerRight e₁.hom F ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom G := by cat_disch) :
    mkNatIso e₁ e₂ coh =
    (functorEquiv F G X).fullyFaithfulFunctor.preimageIso
      (CatCommSqOver.mkIso e₁ e₂
        (by simpa [functorEquiv, toCatCommSqOver] using coh)) := by
  rw [← toCatCommSqOver_mapIso_mkNatIso_eq_mkIso e₁ e₂ coh]
  dsimp [Equivalence.fullyFaithfulFunctor]
  ext <;> simp

end

end functorEquiv

end

section Bifunctoriality

namespace CatCommSqOver
open CategoryTheory.Functor

section transform

variable {A₁ : Type u₄} {B₁ : Type u₅} {C₁ : Type u₆}
  [Category.{v₄} A₁] [Category.{v₅} B₁] [Category.{v₆} C₁]
  {F₁ : A₁ ⥤ B₁} {G₁ : C₁ ⥤ B₁}

set_option backward.defeqAttrib.useBackward true in
/-- Functorially transform a `CatCommSqOver F G X` by whiskering it with a
`CatCospanTransform`. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：transform (X : Type u₇) [Category.{v₇} X] : CatCospanTransform F G F₁ G₁ ⥤
 CatCommSqOver F G X ⥤ CatCommSqOver F₁ G₁ X where obj ψ
参数：X : Type u₇。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorially transform a `CatCommSqOver F G X` by whiskering it with a
`CatCospanTransform`.
-/
def transform (X : Type u₇) [Category.{v₇} X] :
    CatCospanTransform F G F₁ G₁ ⥤
      CatCommSqOver F G X ⥤ CatCommSqOver F₁ G₁ X where
  obj ψ :=
    { obj S :=
      { fst := S.fst ⋙ ψ.left
        snd := S.snd ⋙ ψ.right
        iso :=
          (Functor.associator ..) ≪≫
            isoWhiskerLeft S.fst ψ.squareLeft.iso.symm ≪≫
            (Functor.associator ..).symm ≪≫
            isoWhiskerRight S.iso ψ.base ≪≫
            (Functor.associator ..) ≪≫
            isoWhiskerLeft S.snd ψ.squareRight.iso ≪≫
            (Functor.associator ..).symm }
      map {x y} f :=
        { fst := whiskerRight f.fst ψ.left
          snd := whiskerRight f.snd ψ.right
          w := by
            ext x
            simp [← Functor.map_comp_assoc] }
      map_id := by intros; ext <;> simp
      map_comp := by intros; ext <;> simp }
  map {ψ ψ'} η :=
    { app S :=
      { fst.app y := η.left.app (S.fst.obj y)
        fst.naturality {x y} f := by simp
        snd.app y := η.right.app (S.snd.obj y)
        snd.naturality {x y} f := by simp
        w := by
          ext t
          have := ψ.squareLeft.iso.inv.app (S.fst.obj t) ≫=
            η.left_coherence_app (S.fst.obj t)
          simp only [Iso.inv_hom_id_app_assoc] at this
          simp [this] } }
  map_id := by intros; ext <;> simp
  map_comp := by intros; ext <;> simp

variable {A₂ : Type u₇} {B₂ : Type u₈} {C₂ : Type u₉}
  [Category.{v₇} A₂] [Category.{v₈} B₂] [Category.{v₉} C₂]
  {F₂ : A₂ ⥤ B₂} {G₂ : C₂ ⥤ B₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The construction `CatCommSqOver.transform` respects vertical composition
of `CatCospanTransform`s. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformObjComp** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：transformObjComp (X : Type u₁₀) [Category.{v₁₀} X] (ψ : CatCospanTransform
 F G F₁ G₁) (ψ' : CatCospanTransform F₁ G₁ F₂ G₂) : (transform X).obj (ψ.comp ψ'
) ≅ (transform X).obj ψ ⋙ (transform X).obj ψ'
参数：X : Type u₁₀；ψ : CatCospanTransform F G F₁ G₁；ψ' : CatCospanTransform F₁ G₁ F
₂ G₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The construction `CatCommSqOver.transform` respects vertical composition
of `CatCospanTransform`s.
-/
def transformObjComp (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform F G F₁ G₁) (ψ' : CatCospanTransform F₁ G₁ F₂ G₂) :
    (transform X).obj (ψ.comp ψ') ≅ (transform X).obj ψ ⋙ (transform X).obj ψ' :=
  NatIso.ofComponents (fun _ =>
    CatCommSqOver.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm)
    (fun {x y} f ↦ by ext <;> simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The construction `CatCommSqOver.transform` respects the identity
`CatCospanTransform`s. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformObjId** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：transformObjId (X : Type u₄) [Category.{v₄} X] (F : A ⥤ B) (G : C ⥤ B) : (
transform X).obj (CatCospanTransform.id F G) ≅ 𝟭 _
参数：X : Type u₄；F : A ⥤ B；G : C ⥤ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The construction `CatCommSqOver.transform` respects the identity
`CatCospanTransform`s.
-/
def transformObjId (X : Type u₄) [Category.{v₄} X]
    (F : A ⥤ B) (G : C ⥤ B) :
    (transform X).obj (CatCospanTransform.id F G) ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ =>
    CatCommSqOver.mkIso
      (Functor.rightUnitor _)
      (Functor.rightUnitor _)

open scoped CatCospanTransform

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform_map_whiskerL
eft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatComm
SqOver`。
形式化陈述：transform_map_whiskerLeft (X : Type u₇) [Category.{v₇} X] (ψ : CatCospanTr
ansform F G F₁ G₁) {φ φ' : CatCospanTransform F₁ G₁ F₂ G₂} (α : φ ⟶ φ') : (trans
form X).map (ψ ◁ α) = (transformObjComp X ψ φ).hom ≫ whiskerLeft (transform X |>
.obj ψ) (transform X |>.map α) ≫ (transformObjComp X ψ φ').inv
参数：X : Type u₇；ψ : CatCospanTransform F G F₁ G₁；α : φ ⟶ φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma transform_map_whiskerLeft
    (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F₁ G₁)
    {φ φ' : CatCospanTransform F₁ G₁ F₂ G₂} (α : φ ⟶ φ') :
    (transform X).map (ψ ◁ α) =
    (transformObjComp X ψ φ).hom ≫
      whiskerLeft (transform X |>.obj ψ) (transform X |>.map α) ≫
      (transformObjComp X ψ φ').inv := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform_map_whiskerR
ight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCom
mSqOver`。
形式化陈述：transform_map_whiskerRight (X : Type u₇) [Category.{v₇} X] {ψ ψ' : CatCosp
anTransform F G F₁ G₁} (α : ψ ⟶ ψ') (φ : CatCospanTransform F₁ G₁ F₂ G₂) : (tran
sform X).map (α ▷ φ) = (transformObjComp X ψ φ).hom ≫ whiskerRight (transform X 
|>.map α) (transform X |>.obj φ) ≫ (transformObjComp X ψ' φ).inv
参数：X : Type u₇；α : ψ ⟶ ψ'；φ : CatCospanTransform F₁ G₁ F₂ G₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma transform_map_whiskerRight
    (X : Type u₇) [Category.{v₇} X]
    {ψ ψ' : CatCospanTransform F G F₁ G₁} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform F₁ G₁ F₂ G₂) :
    (transform X).map (α ▷ φ) =
    (transformObjComp X ψ φ).hom ≫
      whiskerRight (transform X |>.map α) (transform X |>.obj φ) ≫
      (transformObjComp X ψ' φ).inv := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform_map_associat
or** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommS
qOver`。
形式化陈述：transform_map_associator {A₃ : Type u₁₀} {B₃ : Type u₁₁} {C₃ : Type u₁₂} [
Category.{v₁₀} A₃] [Category.{v₁₁} B₃] [Category.{v₁₂} C₃] {F₃ : A₃ ⥤ B₃} {G₃ : 
C₃ ⥤ B₃} (X : Type u₁₃) [Category.{v₁₃} X] (ψ : CatCospanTransform F G F₁ G₁) (φ
 : CatCospanTransform F₁ G₁ F₂ G₂) (τ : CatCospanTransform F₂ G₂ F₃ G₃) : (trans
form X).map (α_ ψ φ τ).hom = (transformObjComp X (ψ.comp φ) τ).hom ≫ whiskerRigh
t (transformObjComp X ψ φ).hom (transform X |>.obj τ) ≫ ((transform X |>.obj ψ).
associator (transform X |>
参数：X : Type u₁₃；ψ : CatCospanTransform F G F₁ G₁；φ : CatCospanTransform F₁ G₁ F₂
 G₂；τ : CatCospanTransform F₂ G₂ F₃ G₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transform_map_associator
    {A₃ : Type u₁₀} {B₃ : Type u₁₁} {C₃ : Type u₁₂}
    [Category.{v₁₀} A₃] [Category.{v₁₁} B₃] [Category.{v₁₂} C₃]
    {F₃ : A₃ ⥤ B₃} {G₃ : C₃ ⥤ B₃}
    (X : Type u₁₃) [Category.{v₁₃} X]
    (ψ : CatCospanTransform F G F₁ G₁) (φ : CatCospanTransform F₁ G₁ F₂ G₂)
    (τ : CatCospanTransform F₂ G₂ F₃ G₃) :
    (transform X).map (α_ ψ φ τ).hom =
    (transformObjComp X (ψ.comp φ) τ).hom ≫
      whiskerRight (transformObjComp X ψ φ).hom (transform X |>.obj τ) ≫
      ((transform X |>.obj ψ).associator
        (transform X |>.obj φ) (transform X |>.obj τ)).hom ≫
      whiskerLeft (transform X |>.obj ψ) (transformObjComp X φ τ).inv ≫
      (transformObjComp X ψ (φ.comp τ)).inv := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform_map_leftUnit
or** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommS
qOver`。
形式化陈述：transform_map_leftUnitor (X : Type u₇) [Category.{v₇} X] (ψ : CatCospanTra
nsform F G F₁ G₁) : (transform X).map (fun_ ψ).hom = (transformObjComp X (.id F 
G) ψ).hom ≫ whiskerRight (transformObjId X F G).hom (transform X |>.obj ψ) ≫ (tr
ansform X |>.obj ψ).leftUnitor.hom
参数：X : Type u₇；ψ : CatCospanTransform F G F₁ G₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transform_map_leftUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F₁ G₁) :
    (transform X).map (λ_ ψ).hom =
    (transformObjComp X (.id F G) ψ).hom ≫
      whiskerRight (transformObjId X F G).hom (transform X |>.obj ψ) ≫
      (transform X |>.obj ψ).leftUnitor.hom := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transform_map_rightUni
tor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatComm
SqOver`。
形式化陈述：transform_map_rightUnitor (X : Type u₇) [Category.{v₇} X] (ψ : CatCospanTr
ansform F G F₁ G₁) : (transform X).map (ρ_ ψ).hom = (transformObjComp X ψ (.id F
₁ G₁)).hom ≫ whiskerLeft (transform X |>.obj ψ) (transformObjId X F₁ G₁).hom ≫ (
transform X |>.obj ψ).rightUnitor.hom
参数：X : Type u₇；ψ : CatCospanTransform F G F₁ G₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transform_map_rightUnitor (X : Type u₇) [Category.{v₇} X]
    (ψ : CatCospanTransform F G F₁ G₁) :
    (transform X).map (ρ_ ψ).hom =
    (transformObjComp X ψ (.id F₁ G₁)).hom ≫
      whiskerLeft (transform X |>.obj ψ) (transformObjId X F₁ G₁).hom ≫
      (transform X |>.obj ψ).rightUnitor.hom := by
  ext <;> simp

end transform

section precompose

variable (F G)

variable
    {X : Type u₄} {Y : Type u₅} {Z : Type u₆}
    [Category.{v₄} X] [Category.{v₅} Y] [Category.{v₆} Z]

set_option backward.defeqAttrib.useBackward true in
/-- A functor `U : X ⥤ Y` (functorially) induces a functor
`CatCommSqOver F G Y ⥤ CatCommSqOver F G X` by whiskering left the underlying
categorical commutative square by U. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：precompose : (X ⥤ Y) ⥤ CatCommSqOver F G Y ⥤ CatCommSqOver F G X where obj
 U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `U : X ⥤ Y` (functorially) induces a functor
`CatCommSqOver F G Y ⥤ CatCommSqOver F G X` by whiskering left the underlying
categorical commutative square by U.
-/
def precompose :
    (X ⥤ Y) ⥤ CatCommSqOver F G Y ⥤ CatCommSqOver F G X where
  obj U :=
    { obj S :=
        { fst := U ⋙ S.fst
          snd := U ⋙ S.snd
          iso :=
            (Functor.associator _ _ _) ≪≫
              isoWhiskerLeft U S.iso ≪≫
              (Functor.associator _ _ _).symm }
      map {S S'} φ :=
        { fst := whiskerLeft U φ.fst
          snd := whiskerLeft U φ.snd }
      map_id := by intros; ext <;> simp
      map_comp := by intros; ext <;> simp }
  map {U V} α :=
    { app x :=
      { fst := whiskerRight α x.fst
        snd := whiskerRight α x.snd } }
  map_id := by intros; ext <;> simp
  map_comp := by intros; ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X) in
/-- The construction `precompose` respects functor identities. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjId** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：precomposeObjId : (precompose F G).obj (𝟭 X) ≅ 𝟭 (CatCommSqOver F G X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The construction `precompose` respects functor identities.
-/
def precomposeObjId :
    (precompose F G).obj (𝟭 X) ≅ 𝟭 (CatCommSqOver F G X) :=
  NatIso.ofComponents fun _ =>
    CatCommSqOver.mkIso (Functor.leftUnitor _) (Functor.leftUnitor _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The construction `precompose` respects functor composition. -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjComp** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`。
形式化陈述：precomposeObjComp (U : X ⥤ Y) (V : Y ⥤ Z) : (precompose F G).obj (U ⋙ V) ≅
 (precompose F G).obj V ⋙ (precompose F G).obj U
参数：U : X ⥤ Y；V : Y ⥤ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The construction `precompose` respects functor composition.
-/
def precomposeObjComp (U : X ⥤ Y) (V : Y ⥤ Z) :
    (precompose F G).obj (U ⋙ V) ≅
    (precompose F G).obj V ⋙ (precompose F G).obj U :=
  NatIso.ofComponents fun _ =>
    CatCommSqOver.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose_map_whisker
Left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCom
mSqOver`。
形式化陈述：precompose_map_whiskerLeft (U : X ⥤ Y) {V W : Y ⥤ Z} (α : V ⟶ W) : (precom
pose F G).map (whiskerLeft U α) = (precomposeObjComp F G U V).hom ≫ whiskerRight
 (precompose F G |>.map α) (precompose F G |>.obj U) ≫ (precomposeObjComp F G U 
W).inv
参数：U : X ⥤ Y；α : V ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma precompose_map_whiskerLeft (U : X ⥤ Y) {V W : Y ⥤ Z} (α : V ⟶ W) :
    (precompose F G).map (whiskerLeft U α) =
    (precomposeObjComp F G U V).hom ≫
      whiskerRight (precompose F G |>.map α) (precompose F G |>.obj U) ≫
      (precomposeObjComp F G U W).inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose_map_whisker
Right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCo
mmSqOver`。
形式化陈述：precompose_map_whiskerRight {U V : X ⥤ Y} (α : U ⟶ V) (W : Y ⥤ Z) : (preco
mpose F G).map (whiskerRight α W) = (precomposeObjComp F G U W).hom ≫ whiskerLef
t (precompose F G |>.obj W) (precompose F G |>.map α) ≫ (precomposeObjComp F G V
 W).inv
参数：α : U ⟶ V；W : Y ⥤ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
lemma precompose_map_whiskerRight {U V : X ⥤ Y} (α : U ⟶ V) (W : Y ⥤ Z) :
    (precompose F G).map (whiskerRight α W) =
    (precomposeObjComp F G U W).hom ≫
      whiskerLeft (precompose F G |>.obj W) (precompose F G |>.map α) ≫
      (precomposeObjComp F G V W).inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose_map_associa
tor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatComm
SqOver`。
形式化陈述：precompose_map_associator {T : Type u₇} [Category.{v₇} T] (U : X ⥤ Y) (V :
 Y ⥤ Z) (W : Z ⥤ T) : (precompose F G).map (U.associator V W).hom = (precomposeO
bjComp F G (U ⋙ V) W).hom ≫ whiskerLeft (precompose F G |>.obj W) (precomposeObj
Comp F G U V).hom ≫ ((precompose F G |>.obj W).associator _ _).inv ≫ whiskerRigh
t (precomposeObjComp F G V W).inv (precompose F G |>.obj U) ≫ (precomposeObjComp
 F G _ _).inv
参数：U : X ⥤ Y；V : Y ⥤ Z；W : Z ⥤ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma precompose_map_associator {T : Type u₇} [Category.{v₇} T]
    (U : X ⥤ Y) (V : Y ⥤ Z) (W : Z ⥤ T) :
    (precompose F G).map (U.associator V W).hom =
    (precomposeObjComp F G (U ⋙ V) W).hom ≫
      whiskerLeft (precompose F G |>.obj W) (precomposeObjComp F G U V).hom ≫
      ((precompose F G |>.obj W).associator _ _).inv ≫
      whiskerRight (precomposeObjComp F G V W).inv (precompose F G |>.obj U) ≫
      (precomposeObjComp F G _ _).inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose_map_leftUni
tor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatComm
SqOver`。
形式化陈述：precompose_map_leftUnitor (U : X ⥤ Y) : (precompose F G).map U.leftUnitor.
hom = (precomposeObjComp F G (𝟭 _) U).hom ≫ whiskerLeft (precompose F G |>.obj U
) (precomposeObjId F G X).hom ≫ (Functor.rightUnitor _).hom
参数：U : X ⥤ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma precompose_map_leftUnitor (U : X ⥤ Y) :
    (precompose F G).map U.leftUnitor.hom =
    (precomposeObjComp F G (𝟭 _) U).hom ≫
      whiskerLeft (precompose F G |>.obj U) (precomposeObjId F G X).hom ≫
      (Functor.rightUnitor _).hom := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precompose_map_rightUn
itor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.CatCom
mSqOver`。
形式化陈述：precompose_map_rightUnitor (U : X ⥤ Y) : (precompose F G).map U.rightUnito
r.hom = (precomposeObjComp F G U (𝟭 _)).hom ≫ whiskerRight (precomposeObjId F G 
Y).hom (precompose F G |>.obj U) ≫ (Functor.leftUnitor _).hom
参数：U : X ⥤ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma precompose_map_rightUnitor (U : X ⥤ Y) :
    (precompose F G).map U.rightUnitor.hom =
    (precomposeObjComp F G U (𝟭 _)).hom ≫
      whiskerRight (precomposeObjId F G Y).hom (precompose F G |>.obj U) ≫
      (Functor.leftUnitor _).hom := by
  ext <;> simp

end precompose

section compatibility

variable {A₁ : Type u₄} {B₁ : Type u₅} {C₁ : Type u₆}
  [Category.{v₄} A₁] [Category.{v₅} B₁] [Category.{v₆} C₁]
  {F₁ : A₁ ⥤ B₁} {G₁ : C₁ ⥤ B₁}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical compatibility square between (the object components of)
`precompose` and `transform`.
This is a "naturality square" if we think as `transform _|>.obj _` as the
(app component of the) map component of a pseudofunctor from the bicategory of
categorical cospans with value in pseudofunctors
(its value on the categorical cospan `F, G` being the pseudofunctor
`precompose F G|>.obj _`). -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjTransform
ObjSquare** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.C
atCommSqOver`。
形式化陈述：precomposeObjTransformObjSquare {X : Type u₇} {Y : Type u₈} [Category.{v₇}
 X] [Category.{v₈} Y] (ψ : CatCospanTransform F G F₁ G₁) (U : X ⥤ Y) : CatCommSq
 (precompose F G |>.obj U) (transform Y |>.obj ψ) (transform X |>.obj ψ) (precom
pose F₁ G₁ |>.obj U) where iso
参数：ψ : CatCospanTransform F G F₁ G₁；U : X ⥤ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical compatibility square between (the object components of)
`precompose` and `transform`.
This is a "naturality square" if we think as `transform _|>.obj _` as the
(app component of the) map component of a pseudofunctor from the bicategory of
categorical cospans with value in pseudofunctors
(its value on the categorical cospan `F, G` being the pseudofunctor
`precompose F G|>.obj _`).
-/
instance precomposeObjTransformObjSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F₁ G₁) (U : X ⥤ Y) :
    CatCommSq
      (precompose F G |>.obj U) (transform Y |>.obj ψ)
      (transform X |>.obj ψ) (precompose F₁ G₁ |>.obj U) where
  iso := NatIso.ofComponents (fun _ =>
    CatCommSqOver.mkIso
      (Functor.associator _ _ _)
      (Functor.associator _ _ _))
    (fun {x y} f ↦ by ext <;> simp)

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

set_option backward.defeqAttrib.useBackward true in
/-- The square `precomposeObjTransformObjSquare` is itself natural. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjTransform
ObjSquare_iso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Ca
tegoricalPullback.CatCommSqOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square `precomposeObjTransformObjSquare` is itself natural.
-/
lemma precomposeObjTransformObjSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (ψ : CatCospanTransform F G F₁ G₁)
    {U V : X ⥤ Y} (α : U ⟶ V) :
    whiskerRight (precompose F G |>.map α) (transform X |>.obj ψ) ≫
      (CatCommSq.iso _ (transform Y |>.obj ψ) _ (precompose F₁ G₁ |>.obj V)).hom =
    (CatCommSq.iso _ (transform Y |>.obj ψ) _ (precompose F₁ G₁ |>.obj U)).hom ≫
      whiskerLeft (transform Y |>.obj ψ) (precompose F₁ G₁ |>.map α) := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The square `precomposeObjTransformOBjSquare` respects identities. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjTransform
ObjSquare_iso_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Categorica
lPullback.CatCommSqOver`。
形式化陈述：precomposeObjTransformObjSquare_iso_hom_id (ψ : CatCospanTransform F G F₁ 
G₁) (X : Type u₇) [Category.{v₇} X] : (CatCommSq.iso (precompose F G |>.obj <| 𝟭
 X) (transform X |>.obj ψ) (transform X |>.obj ψ) (precompose F₁ G₁ |>.obj <| 𝟭 
X)).hom ≫ whiskerLeft (transform X |>.obj ψ) (precomposeObjId F₁ G₁ X).hom = whi
skerRight (precomposeObjId F G X).hom (transform X |>.obj ψ) ≫ (Functor.leftUnit
or _).hom ≫ (Functor.rightUnitor _).inv
参数：ψ : CatCospanTransform F G F₁ G₁；X : Type u₇。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The square `precomposeObjTransformOBjSquare` respects identities.
-/
lemma precomposeObjTransformObjSquare_iso_hom_id
    (ψ : CatCospanTransform F G F₁ G₁) (X : Type u₇) [Category.{v₇} X] :
    (CatCommSq.iso (precompose F G |>.obj <| 𝟭 X) (transform X |>.obj ψ)
      (transform X |>.obj ψ) (precompose F₁ G₁ |>.obj <| 𝟭 X)).hom ≫
      whiskerLeft (transform X |>.obj ψ) (precomposeObjId F₁ G₁ X).hom =
    whiskerRight (precomposeObjId F G X).hom (transform X |>.obj ψ) ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The square `precomposeTransformSquare` respects compositions. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.precomposeObjTransform
ObjSquare_iso_hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Categori
calPullback.CatCommSqOver`。
形式化陈述：precomposeObjTransformObjSquare_iso_hom_comp {X : Type u₇} {Y : Type u₈} {
Z : Type u₉} [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z] (ψ : CatCospa
nTransform F G F₁ G₁) (U : X ⥤ Y) (V : Y ⥤ Z) : (CatCommSq.iso (precompose F G |
>.obj <| U ⋙ V) (transform Z |>.obj ψ) (transform X |>.obj ψ) (precompose F₁ G₁ 
|>.obj <| U ⋙ V)).hom ≫ whiskerLeft (transform Z |>.obj ψ) (precomposeObjComp F₁
 G₁ U V).hom = whiskerRight (precomposeObjComp F G U V).hom (transform X |>.obj 
ψ) ≫ (Functor.associator _
参数：ψ : CatCospanTransform F G F₁ G₁；U : X ⥤ Y；V : Y ⥤ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The square `precomposeTransformSquare` respects compositions.
-/
lemma precomposeObjTransformObjSquare_iso_hom_comp
    {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
    [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z]
    (ψ : CatCospanTransform F G F₁ G₁)
    (U : X ⥤ Y) (V : Y ⥤ Z) :
    (CatCommSq.iso (precompose F G |>.obj <| U ⋙ V) (transform Z |>.obj ψ)
      (transform X |>.obj ψ) (precompose F₁ G₁ |>.obj <| U ⋙ V)).hom ≫
      whiskerLeft (transform Z |>.obj ψ) (precomposeObjComp F₁ G₁ U V).hom =
    whiskerRight (precomposeObjComp F G U V).hom (transform X |>.obj ψ) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (precompose F G |>.obj V)
        (CatCommSq.iso _ (transform _ |>.obj ψ) _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom
        (precompose F₁ G₁ |>.obj U) ≫
      (Functor.associator _ _ _).hom := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical compatibility square between (the object components of)
`transform` and `precompose`.
This is a "naturality square" if we think as `precompose` as the
(app component of the) map component of a pseudofunctor from the opposite
bicategory of categories to pseudofunctors of categorical cospans
(its value on `X` being the pseudofunctor `transform X _`). -/
@[simps!]
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformObjPrecompose
ObjSquare** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.CategoricalPullback.C
atCommSqOver`。
形式化陈述：transformObjPrecomposeObjSquare {X : Type u₇} {Y : Type u₈} [Category.{v₇}
 X] [Category.{v₈} Y] (U : X ⥤ Y) (ψ : CatCospanTransform F G F₁ G₁) : CatCommSq
 (transform Y |>.obj ψ) (precompose F G |>.obj U) (precompose F₁ G₁ |>.obj U) (t
ransform X |>.obj ψ) where iso
参数：U : X ⥤ Y；ψ : CatCospanTransform F G F₁ G₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical compatibility square between (the object components of)
`transform` and `precompose`.
This is a "naturality square" if we think as `precompose` as the
(app component of the) map component of a pseudofunctor from the opposite
bicategory of categories to pseudofunctors of categorical cospans
(its value on `X` being the pseudofunctor `transform X _`).
-/
instance transformObjPrecomposeObjSquare
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F₁ G₁) :
    CatCommSq
      (transform Y |>.obj ψ) (precompose F G |>.obj U)
      (precompose F₁ G₁ |>.obj U) (transform X |>.obj ψ) where
  iso := NatIso.ofComponents (fun _ =>
    CatCommSqOver.mkIso
      (Functor.associator _ _ _).symm
      (Functor.associator _ _ _).symm)
    (fun {x y} f ↦ by ext <;> simp)

-- Compare the next 3 lemmas with the components of a strong natural transform
-- of pseudofunctors

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The square `transformObjPrecomposeObjSquare` is itself natural. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformObjPrecompose
ObjSquare_iso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Ca
tegoricalPullback.CatCommSqOver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square `transformObjPrecomposeObjSquare` is itself natural.
-/
lemma transformObjPrecomposeObjSquare_iso_hom_naturality₂
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) {ψ ψ' : CatCospanTransform F G F₁ G₁} (η : ψ ⟶ ψ') :
    whiskerRight (transform Y |>.map η) (precompose F₁ G₁ |>.obj U) ≫
      (CatCommSq.iso _ (precompose F G |>.obj U) _ (transform X |>.obj ψ')).hom =
    (CatCommSq.iso _ (precompose F G |>.obj U) _ (transform X |>.obj ψ)).hom ≫
      whiskerLeft (precompose F G |>.obj U) (transform X |>.map η) := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The square `transformObjPrecomposeObjSquare` respects identities. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformObjPrecompose
ObjSquare_iso_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Categorica
lPullback.CatCommSqOver`。
形式化陈述：transformObjPrecomposeObjSquare_iso_hom_id {X : Type u₇} {Y : Type u₈} [Ca
tegory.{v₇} X] [Category.{v₈} Y] (U : X ⥤ Y) (F : A ⥤ B) (G : C ⥤ B) : (CatCommS
q.iso (transform Y |>.obj <| .id F G) (precompose F G |>.obj U) (precompose F G 
|>.obj U) (transform X |>.obj <| .id F G)).hom ≫ whiskerLeft (precompose F G |>.
obj U) (transformObjId X F G).hom = whiskerRight (transformObjId Y F G).hom (pre
compose F G |>.obj U) ≫ (precompose F G |>.obj U).leftUnitor.hom ≫ (precompose F
 G |>.obj U).rightUnitor.i
参数：U : X ⥤ Y；F : A ⥤ B；G : C ⥤ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The square `transformObjPrecomposeObjSquare` respects identities.
-/
lemma transformObjPrecomposeObjSquare_iso_hom_id
    {X : Type u₇} {Y : Type u₈} [Category.{v₇} X] [Category.{v₈} Y]
    (U : X ⥤ Y) (F : A ⥤ B) (G : C ⥤ B) :
    (CatCommSq.iso (transform Y |>.obj <| .id F G) (precompose F G |>.obj U)
      (precompose F G |>.obj U) (transform X |>.obj <| .id F G)).hom ≫
      whiskerLeft (precompose F G |>.obj U) (transformObjId X F G).hom =
    whiskerRight (transformObjId Y F G).hom (precompose F G |>.obj U) ≫
      (precompose F G |>.obj U).leftUnitor.hom ≫
      (precompose F G |>.obj U).rightUnitor.inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The square `transformPrecomposeSquare` respects compositions. -/
/-
**CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.transformPrecomposeObj
Square_iso_hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.Categorical
Pullback.CatCommSqOver`。
形式化陈述：transformPrecomposeObjSquare_iso_hom_comp {A₂ : Type u₇} {B₂ : Type u₈} {C
₂ : Type u₉} [Category.{v₇} A₂] [Category.{v₈} B₂] [Category.{v₉} C₂] {F₂ : A₂ ⥤
 B₂} {G₂ : C₂ ⥤ B₂} {X : Type u₁₀} {Y : Type u₁₁} [Category.{v₁₀} X] [Category.{
v₁₁} Y] (U : X ⥤ Y) (ψ : CatCospanTransform F G F₁ G₁) (ψ' : CatCospanTransform 
F₁ G₁ F₂ G₂) : (CatCommSq.iso (transform Y |>.obj <| ψ.comp ψ') (precompose F G 
|>.obj U) (precompose F₂ G₂ |>.obj U) (transform X |>.obj <| ψ.comp ψ')).hom ≫ w
hiskerLeft (precompose F G
参数：U : X ⥤ Y；ψ : CatCospanTransform F G F₁ G₁；ψ' : CatCospanTransform F₁ G₁ F₂ G
₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.hom_ext`：hom_ext
 {S S' : CatCommSqOver F G X} {f g : S ⟶ S'} (h₁ : f.fst = g.fst) (h₂ : f.snd = 
g.snd) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The square `transformPrecomposeSquare` respects compositions.
-/
lemma transformPrecomposeObjSquare_iso_hom_comp
    {A₂ : Type u₇} {B₂ : Type u₈} {C₂ : Type u₉}
    [Category.{v₇} A₂] [Category.{v₈} B₂] [Category.{v₉} C₂]
    {F₂ : A₂ ⥤ B₂} {G₂ : C₂ ⥤ B₂}
    {X : Type u₁₀} {Y : Type u₁₁} [Category.{v₁₀} X] [Category.{v₁₁} Y]
    (U : X ⥤ Y) (ψ : CatCospanTransform F G F₁ G₁)
    (ψ' : CatCospanTransform F₁ G₁ F₂ G₂) :
    (CatCommSq.iso (transform Y |>.obj <| ψ.comp ψ') (precompose F G |>.obj U)
      (precompose F₂ G₂ |>.obj U) (transform X |>.obj <| ψ.comp ψ')).hom ≫
      whiskerLeft (precompose F G |>.obj U) (transformObjComp X ψ ψ').hom =
    whiskerRight (transformObjComp Y ψ ψ').hom (precompose F₂ G₂ |>.obj U) ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (transform Y |>.obj ψ)
        (CatCommSq.iso _ (precompose F₁ G₁ |>.obj U)
          _ (transform X |>.obj ψ')).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (CatCommSq.iso _ _ _ _).hom (transform X |>.obj ψ') ≫
      (Functor.associator _ _ _).hom := by
  ext <;> simp

end compatibility

end CatCommSqOver

end Bifunctoriality

end CategoricalPullback

end

end CategoryTheory.Limits

