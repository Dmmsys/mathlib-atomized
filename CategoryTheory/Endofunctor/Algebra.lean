/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Robert Y. Lewis, Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/

@[expose] public section


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/--
Definition of `Algebra` / `Algebra` 的定义

English:
structure Algebra
  parameters: (F : C ⥤ C)
  axioms and operations (2):
    - a : C
    - str : F.obj a ⟶ a

中文:
结构 代数
  参数: (F : C ⥤ C)
  公理与运算 (2 个):
    - a : C
    - str : F.obj a ⟶ a
-/
structure Algebra (F : C ⥤ C) where
  /-- carrier of the algebra -/
  a : C
  /-- structure morphism of the algebra -/
  str : F.obj a ⟶ a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (Algebra (𝟭 C))
  body: ⟨⟨default, 𝟙 _⟩⟩

中文:
实例 [可居
  签名: C] : 可居 (代数 (𝟭 C))
  定义体: ⟨⟨default, 𝟙 _⟩⟩
-/
instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

/-
```
        str
   F A₀ -----> A₀
    | |
F f | | f
    V V
   F A₁ -----> A₁
        str
```
-/
/-- A morphism between algebras of endofunctor `F` -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A₀ A₁ : Algebra F)
  axioms and operations (2):
    - f : A₀.1 ⟶ A₁.1
    - h : F.map f ≫ A₁.str = A₀.str ≫ f  [default: by cat_disch]

中文:
结构 态射
  参数: (A₀ A₁ : 代数 F)
  公理与运算 (2 个):
    - f : A₀.1 ⟶ A₁.1
    - h : F.map f ≫ A₁.str = A₀.str ≫ f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (A₀ A₁ : Algebra F) where
  /-- underlying morphism between the carriers -/
  f : A₀.1 ⟶ A₁.1
  /-- compatibility condition -/
  h : F.map f ≫ A₁.str = A₀.str ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Hom A A where f
  body: 𝟙 _

中文:
定义 id
  签名: : 态射 A A where f
  定义体: 𝟙 _
-/
def id : Hom A A where f := 𝟙 _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Hom A A)
  body: ⟨{ f := 𝟙 _ }⟩

中文:
实例 :
  签名: 可居 (态射 A A)
  定义体: ⟨{ f := 𝟙 _ }⟩
-/
instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : Hom A₀ A₁) (g : Hom A₁ A₂)
  body: f.1 ≫ g.1

中文:
定义 comp
  签名: (f : 态射 A₀ A₁) (g : 态射 A₁ A₂)
  定义体: f.1 ≫ g.1
-/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  statement: f = g
  proof: Hom.ext w

@[simp]

中文:
引理 ext
  条件: {A B : 代数 F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  结论: f = g
  证明: Hom.ext w

@[simp]

Depends on / 依赖: Hom.ext, cat_disch
-/
lemma ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  statement: Algebra.Hom.id A = 𝟙 A
  proof: rfl

@[simp]

中文:
定理 id_eq_id
  结论: 代数.态射.id A = 𝟙 A
  证明: rfl

@[simp]
-/
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  statement: (𝟙 _ : A ⟶ A).1 = 𝟙 A.1
  proof: rfl

中文:
定理 id_f
  结论: (𝟙 _ : A ⟶ A).1 = 𝟙 A.1
  证明: rfl
-/
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl

variable (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  statement: Algebra.Hom.comp f g = f ≫ g
  proof: rfl

@[simp]

中文:
定理 comp_eq_comp
  结论: 代数.态射.comp f g = f ≫ g
  证明: rfl

@[simp]
-/
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  statement: (f ≫ g).1 = f.1 ≫ g.1
  proof: rfl

中文:
定理 comp_f
  结论: (f ≫ g).1 = f.1 ≫ g.1
  证明: rfl
-/
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Algebra F) := { }

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by cat_disch)
  body: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

中文:
定义 isoMk
  签名: (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by cat_disch)
  定义体: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp_assoc, cat_disch, eq_comp_inv, h.eq_comp_inv, h.hom, h.inv, map_comp_assoc
-/
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by cat_disch) :
    A₀ ≅ A₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv]; rw [Category.assoc]; rw [← w]; rw [← Functor.map_comp_assoc]
        simp }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: (F : C ⥤ C)
  body: A.1
  map := Hom.f

中文:
定义 forget
  签名: (F : C ⥤ C)
  定义体: A.1
  map := Hom.f
-/
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj A := A.1
  map := Hom.f

/--
theorem `iso_of_iso` / 定理 `iso_of_iso`

English:
theorem iso_of_iso
  given: (f : A₀ ⟶ A₁) [IsIso f.1]
  statement: IsIso f
  proof: ⟨⟨{ f := inv f.1
      h := by simp }, by cat_disch, by cat_disch⟩⟩

中文:
定理 iso_of_iso
  条件: (f : A₀ ⟶ A₁) [是同构 f.1]
  结论: 是同构 f
  证明: ⟨⟨{ f := inv f.1
      h := by simp }, by cat_disch, by cat_disch⟩⟩

Depends on / 依赖: cat_disch
-/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by simp }, by cat_disch, by cat_disch⟩⟩

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : (forget F).ReflectsIsomorphisms where reflects
  body: iso_of_iso

中文:
实例 forget_reflects_iso
  签名: : (forget F).反映同构 where reflects
  定义体: iso_of_iso

Depends on / 依赖: iso_of_iso
-/
instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget F).Faithful
  body: { }

中文:
实例 forget_faithful
  签名: : (forget F).忠实
  定义体: { }
-/
instance forget_faithful : (forget F).Faithful := { }

/--
theorem `epi_of_epi` / 定理 `epi_of_epi`

English:
theorem epi_of_epi
  given: {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1]
  statement: Epi f
  proof: (forget F).epi_of_epi_map h

中文:
定理 epi_of_epi
  条件: {X Y : 代数 F} (f : X ⟶ Y) [h : 满态射 f.1]
  结论: 满态射 f
  证明: (forget F).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/--
theorem `mono_of_mono` / 定理 `mono_of_mono`

English:
theorem mono_of_mono
  given: {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1]
  statement: Mono f
  proof: (forget F).mono_of_mono_map h

中文:
定理 mono_of_mono
  条件: {X Y : 代数 F} (f : X ⟶ Y) [h : 单态射 f.1]
  结论: 单态射 f
  证明: (forget F).mono_of_mono_map h

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
/--
Definition of `functorOfNatTrans` / `functorOfNatTrans` 的定义

English:
definition functorOfNatTrans
  signature: {F G : C ⥤ C} (α : G ⟶ F)
  body: { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

中文:
定义 functorOf自然数Trans
  签名: {F G : C ⥤ C} (α : G ⟶ F)
  定义体: { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

Depends on / 依赖: A.str
-/
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps!]
/--
Definition of `functorOfNatTransId` / `functorOfNatTransId` 的定义

English:
definition functorOfNatTransId
  signature: : functorOfNatTrans (𝟙 F) ≅ 𝟭 _
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransId
  签名: : functorOf自然数Trans (𝟙 F) ≅ 𝟭 _
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
/--
Definition of `functorOfNatTransComp` / `functorOfNatTransComp` 的定义

English:
definition functorOfNatTransComp
  signature: {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂)
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransComp
  签名: {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂)
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
/--
Definition of `functorOfNatTransEq` / `functorOfNatTransEq` 的定义

English:
definition functorOfNatTransEq
  signature: {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β)
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransEq
  签名: {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β)
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
/--
Definition of `equivOfNatIso` / `equivOfNatIso` 的定义

English:
definition equivOfNatIso
  signature: {F G : C ⥤ C} (α : F ≅ G)
  body: functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

中文:
定义 equivOf自然数Iso
  签名: {F G : C ⥤ C} (α : F ≅ G)
  定义体: functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

Depends on / 依赖: functorOfNatTrans
-/
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Initial

variable {A : Algebra F} (h : Limits.IsInitial A)
/-- The inverse of the structure map of an initial algebra -/
@[simp]
/--
Definition of `strInv` / `strInv` 的定义

English:
definition strInv
  signature: : A.1 ⟶ F.obj A.1
  body: (h.to ⟨F.obj A.a, F.map A.str⟩).f

中文:
定义 strInv
  签名: : A.1 ⟶ F.obj A.1
  定义体: (h.to ⟨F.obj A.a, F.map A.str⟩).f

Depends on / 依赖: A.str, F.map, F.obj, h.to
-/
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.a, F.map A.str⟩).f

/--
theorem `left_inv'` / 定理 `left_inv'`

English:
theorem left_inv'
  proof: Limits.IsInitial.hom_ext h _ (𝟙 A)

中文:
定理 left_inv'
  证明: Limits.IsInitial.hom_ext h _ (𝟙 A)

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.hom_ext, hom_ext
-/
theorem left_inv' :
    ⟨strInv h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv, ← Hom.h]⟩ = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  statement: strInv h ≫ A.str = 𝟙 _
  proof: congr_arg Hom.f (left_inv' h)

中文:
定理 left_inv
  结论: strInv h ≫ A.str = 𝟙 _
  证明: congr_arg Hom.f (left_inv' h)

Depends on / 依赖: Hom.f, congr_arg, left_inv
-/
theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  statement: A.str ≫ strInv h = 𝟙 _
  proof: by
  rw [strInv]; rw [← (h.to ⟨F.obj A.1]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact left_inv h

中文:
定理 right_inv
  结论: A.str ≫ strInv h = 𝟙 _
  证明: by
  rw [strInv]; rw [← (h.to ⟨F.obj A.1]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact left_inv h

Depends on / 依赖: A.str, F.map, F.map_comp, F.map_id, F.obj, h.to, left_inv, map_comp, map_id, strInv
-/
theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [strInv]; rw [← (h.to ⟨F.obj A.1]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact left_inv h

/--
theorem `str_isIso` / 定理 `str_isIso`

English:
theorem str_isIso
  given: (h : Limits.IsInitial A)
  statement: IsIso A.str
  proof: { out := ⟨strInv h, right_inv _, left_inv _⟩ }

中文:
定理 str_isIso
  条件: (h : Limits.IsInitial A)
  结论: 是同构 A.str
  证明: { out := ⟨strInv h, right_inv _, left_inv _⟩ }

Depends on / 依赖: left_inv, right_inv, strInv
-/
theorem str_isIso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

/--
Definition of `Coalgebra` / `Coalgebra` 的定义

English:
structure Coalgebra
  parameters: (F : C ⥤ C)
  axioms and operations (2):
    - V : C
    - str : V ⟶ F.obj V

中文:
结构 余algebra
  参数: (F : C ⥤ C)
  公理与运算 (2 个):
    - V : C
    - str : V ⟶ F.obj V
-/
structure Coalgebra (F : C ⥤ C) where
  /-- carrier of the coalgebra -/
  V : C
  /-- structure morphism of the coalgebra -/
  str : V ⟶ F.obj V

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (Coalgebra (𝟭 C))
  body: ⟨⟨default, 𝟙 _⟩⟩

中文:
实例 [可居
  签名: C] : 可居 (余algebra (𝟭 C))
  定义体: ⟨⟨default, 𝟙 _⟩⟩
-/
instance [Inhabited C] : Inhabited (Coalgebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Coalgebra

variable {F : C ⥤ C} (V : Coalgebra F) {V₀ V₁ V₂ : Coalgebra F}

/-
```
        str
    V₀ -----> F V₀
    | |
  f | | F f
    V V
    V₁ -----> F V₁
        str
```
-/
/-- A morphism between coalgebras of an endofunctor `F` -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (V₀ V₁ : Coalgebra F)
  axioms and operations (2):
    - f : V₀.1 ⟶ V₁.1
    - h : V₀.str ≫ F.map f = f ≫ V₁.str  [default: by cat_disch]

中文:
结构 态射
  参数: (V₀ V₁ : 余algebra F)
  公理与运算 (2 个):
    - f : V₀.1 ⟶ V₁.1
    - h : V₀.str ≫ F.map f = f ≫ V₁.str  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (V₀ V₁ : Coalgebra F) where
  /-- underlying morphism between two carriers -/
  f : V₀.1 ⟶ V₁.1
  /-- compatibility condition -/
  h : V₀.str ≫ F.map f = f ≫ V₁.str := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Hom V V where f
  body: 𝟙 _

中文:
定义 id
  签名: : 态射 V V where f
  定义体: 𝟙 _
-/
def id : Hom V V where f := 𝟙 _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Hom V V)
  body: ⟨{ f := 𝟙 _ }⟩

中文:
实例 :
  签名: 可居 (态射 V V)
  定义体: ⟨{ f := 𝟙 _ }⟩
-/
instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : Hom V₀ V₁) (g : Hom V₁ V₂)
  body: f.1 ≫ g.1

中文:
定义 comp
  签名: (f : 态射 V₀ V₁) (g : 态射 V₁ V₂)
  定义体: f.1 ≫ g.1
-/
def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  statement: f = g
  proof: Hom.ext w

@[simp]

中文:
引理 ext
  条件: {A B : 余algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  结论: f = g
  证明: Hom.ext w

@[simp]

Depends on / 依赖: Hom.ext, cat_disch
-/
lemma ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  statement: Coalgebra.Hom.id V = 𝟙 V
  proof: rfl

@[simp]

中文:
定理 id_eq_id
  结论: 余algebra.态射.id V = 𝟙 V
  证明: rfl

@[simp]
-/
theorem id_eq_id : Coalgebra.Hom.id V = 𝟙 V :=
  rfl

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  statement: (𝟙 _ : V ⟶ V).1 = 𝟙 V.1
  proof: rfl

中文:
定理 id_f
  结论: (𝟙 _ : V ⟶ V).1 = 𝟙 V.1
  证明: rfl
-/
theorem id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1 :=
  rfl

variable (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

@[simp]
/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  statement: Coalgebra.Hom.comp f g = f ≫ g
  proof: rfl

@[simp]

中文:
定理 comp_eq_comp
  结论: 余algebra.态射.comp f g = f ≫ g
  证明: rfl

@[simp]
-/
theorem comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  statement: (f ≫ g).1 = f.1 ≫ g.1
  proof: rfl

中文:
定理 comp_f
  结论: (f ≫ g).1 = f.1 ≫ g.1
  证明: rfl
-/
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Coalgebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Coalgebra F) := { }

/-- To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the Vs which
commutes with the structure morphisms.
-/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by cat_disch)
  body: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← Category.assoc]; rw [← w]; rw [Category.assoc]; rw [← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

中文:
定义 isoMk
  签名: (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by cat_disch)
  定义体: { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← Category.assoc]; rw [← w]; rw [Category.assoc]; rw [← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

Depends on / 依赖: Category, Category.assoc, Category.comp_id, F.map_comp, Functor, Functor.map_id, Iso.hom_inv_id, cat_disch, comp_id, eq_inv_comp, h.eq_inv_comp, h.hom, h.inv, hom_inv_id, map_comp, map_id
-/
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by cat_disch) :
    V₀ ≅ V₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp]; rw [← Category.assoc]; rw [← w]; rw [Category.assoc]; rw [← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

/-- The forgetful functor from the category of coalgebras, forgetting the coalgebraic structure. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: (F : C ⥤ C)
  body: A.1
  map f := f.1

中文:
定义 forget
  签名: (F : C ⥤ C)
  定义体: A.1
  map f := f.1
-/
def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj A := A.1
  map f := f.1

/--
theorem `iso_of_iso` / 定理 `iso_of_iso`

English:
theorem iso_of_iso
  given: (f : V₀ ⟶ V₁) [IsIso f.1]
  statement: IsIso f
  proof: ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1]; rw [← Category.assoc]; rw [← f.h]; rw [Category.assoc]
        simp }, by cat_disch, by cat_disch⟩⟩

中文:
定理 iso_of_iso
  条件: (f : V₀ ⟶ V₁) [是同构 f.1]
  结论: 是同构 f
  证明: ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1]; rw [← Category.assoc]; rw [← f.h]; rw [Category.assoc]
        simp }, by cat_disch, by cat_disch⟩⟩

Depends on / 依赖: Category, Category.assoc, IsIso.eq_inv_comp, cat_disch, eq_inv_comp
-/
theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1]; rw [← Category.assoc]; rw [← f.h]; rw [Category.assoc]
        simp }, by cat_disch, by cat_disch⟩⟩

/--
Instance `forget_reflects_iso` / 实例 `forget_reflects_iso`

English:
instance forget_reflects_iso
  signature: : (forget F).ReflectsIsomorphisms where reflects
  body: iso_of_iso

中文:
实例 forget_reflects_iso
  签名: : (forget F).反映同构 where reflects
  定义体: iso_of_iso

Depends on / 依赖: iso_of_iso
-/
instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget F).Faithful
  body: { }

中文:
实例 forget_faithful
  签名: : (forget F).忠实
  定义体: { }
-/
instance forget_faithful : (forget F).Faithful := { }

/--
theorem `epi_of_epi` / 定理 `epi_of_epi`

English:
theorem epi_of_epi
  given: {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1]
  statement: Epi f
  proof: (forget F).epi_of_epi_map h

中文:
定理 epi_of_epi
  条件: {X Y : 余algebra F} (f : X ⟶ Y) [h : 满态射 f.1]
  结论: 满态射 f
  证明: (forget F).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map, forget
-/
theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/--
theorem `mono_of_mono` / 定理 `mono_of_mono`

English:
theorem mono_of_mono
  given: {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1]
  statement: Mono f
  proof: (forget F).mono_of_mono_map h

中文:
定理 mono_of_mono
  条件: {X Y : 余algebra F} (f : X ⟶ Y) [h : 单态射 f.1]
  结论: 单态射 f
  证明: (forget F).mono_of_mono_map h

Depends on / 依赖: forget, mono_of_mono_map
-/
theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
@[simps]
/--
Definition of `functorOfNatTrans` / `functorOfNatTrans` 的定义

English:
definition functorOfNatTrans
  signature: {F G : C ⥤ C} (α : F ⟶ G)
  body: { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

中文:
定义 functorOf自然数Trans
  签名: {F G : C ⥤ C} (α : F ⟶ G)
  定义体: { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

Depends on / 依赖: Category, Category.assoc, V.str, naturality
-/
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G where
  obj V :=
    { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity transformation induces the identity endofunctor on the category of coalgebras. -/
@[simps!]
/--
Definition of `functorOfNatTransId` / `functorOfNatTransId` 的定义

English:
definition functorOfNatTransId
  signature: : functorOfNatTrans (𝟙 F) ≅ 𝟭 _
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransId
  签名: : functorOf自然数Trans (𝟙 F) ≅ 𝟭 _
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps!]
/--
Definition of `functorOfNatTransComp` / `functorOfNatTransComp` 的定义

English:
definition functorOfNatTransComp
  signature: {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂)
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransComp
  签名: {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂)
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents, preservesFiniteBiproductsOfPreservesBiproducts
-/
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `α` and `β` are two equal natural transformations, then the functors of coalgebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps!]
/--
Definition of `functorOfNatTransEq` / `functorOfNatTransEq` 的定义

English:
definition functorOfNatTransEq
  signature: {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β)
  body: NatIso.ofComponents fun X => isoMk (Iso.refl _)

中文:
定义 functorOf自然数TransEq
  签名: {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β)
  定义体: NatIso.ofComponents fun X => isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
/--
Definition of `equivOfNatIso` / `equivOfNatIso` 的定义

English:
definition equivOfNatIso
  signature: {F G : C ⥤ C} (α : F ≅ G)
  body: functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

中文:
定义 equivOf自然数Iso
  签名: {F G : C ⥤ C} (α : F ≅ G)
  定义体: functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

Depends on / 依赖: functorOfNatTrans
-/
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where
  functor := functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Terminal

variable {A : Coalgebra F} (h : Limits.IsTerminal A)

/-- The inverse of the structure map of a terminal coalgebra -/
@[simp]
/--
Definition of `strInv` / `strInv` 的定义

English:
definition strInv
  signature: : F.obj A.1 ⟶ A.1
  body: (h.from ⟨F.obj A.V, F.map A.str⟩).f

中文:
定义 strInv
  签名: : F.obj A.1 ⟶ A.1
  定义体: (h.from ⟨F.obj A.V, F.map A.str⟩).f

Depends on / 依赖: A.str, F.map, F.obj, h.from
-/
def strInv : F.obj A.1 ⟶ A.1 :=
  (h.from ⟨F.obj A.V, F.map A.str⟩).f

/--
theorem `right_inv'` / 定理 `right_inv'`

English:
theorem right_inv'
  proof: Limits.IsTerminal.hom_ext h _ (𝟙 A)

中文:
定理 right_inv'
  证明: Limits.IsTerminal.hom_ext h _ (𝟙 A)

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.hom_ext, hom_ext
-/
theorem right_inv' :
    ⟨A.str ≫ strInv h, by rw [Category.assoc, F.map_comp, strInv, ← Hom.h] ⟩ = 𝟙 A :=
  Limits.IsTerminal.hom_ext h _ (𝟙 A)

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  statement: A.str ≫ strInv h = 𝟙 _
  proof: congr_arg Hom.f (right_inv' h)

中文:
定理 right_inv
  结论: A.str ≫ strInv h = 𝟙 _
  证明: congr_arg Hom.f (right_inv' h)

Depends on / 依赖: Hom.f, congr_arg, right_inv
-/
theorem right_inv : A.str ≫ strInv h = 𝟙 _ :=
  congr_arg Hom.f (right_inv' h)

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  statement: strInv h ≫ A.str = 𝟙 _
  proof: by
  rw [strInv]; rw [← (h.from ⟨F.obj A.V]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact right_inv h

中文:
定理 left_inv
  结论: strInv h ≫ A.str = 𝟙 _
  证明: by
  rw [strInv]; rw [← (h.from ⟨F.obj A.V]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact right_inv h

Depends on / 依赖: A.str, F.map, F.map_comp, F.map_id, F.obj, h.from, map_comp, map_id, right_inv, strInv
-/
theorem left_inv : strInv h ≫ A.str = 𝟙 _ := by
  rw [strInv]; rw [← (h.from ⟨F.obj A.V]; rw [F.map A.str⟩).h]; rw [← F.map_id]; rw [← F.map_comp]
  congr
  exact right_inv h

/--
theorem `str_isIso` / 定理 `str_isIso`

English:
theorem str_isIso
  given: (h : Limits.IsTerminal A)
  statement: IsIso A.str
  proof: { out := ⟨strInv h, right_inv _, left_inv _⟩ }

中文:
定理 str_isIso
  条件: (h : Limits.是终止 A)
  结论: 是同构 A.str
  证明: { out := ⟨strInv h, right_inv _, left_inv _⟩ }

Depends on / 依赖: left_inv, right_inv, strInv
-/
theorem str_isIso (h : Limits.IsTerminal A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Terminal

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

/--
theorem `Algebra.homEquiv_naturality_str` / 定理 `Algebra.homEquiv_naturality_str`

English:
theorem Algebra.homEquiv_naturality_str
  given: (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂)
  proof: by
  rw [← Adjunction.homEquiv_naturality_right]; rw [← Adjunction.homEquiv_naturality_left]; rw [f.h]

中文:
定理 代数.homEquiv_naturality_str
  条件: (adj : F ⊣ G) (A₁ A₂ : 代数 F) (f : A₁ ⟶ A₂)
  证明: by
  rw [← Adjunction.homEquiv_naturality_right]; rw [← Adjunction.homEquiv_naturality_left]; rw [f.h]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, homEquiv_naturality_left, homEquiv_naturality_right
-/
theorem Algebra.homEquiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.a A₁.a) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.a A₂.a) A₂.str := by
  rw [← Adjunction.homEquiv_naturality_right]; rw [← Adjunction.homEquiv_naturality_left]; rw [f.h]

/--
theorem `Coalgebra.homEquiv_naturality_str_symm` / 定理 `Coalgebra.homEquiv_naturality_str_symm`

English:
theorem Coalgebra.homEquiv_naturality_str_symm
  given: (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂)
  proof: by
  rw [← Adjunction.homEquiv_naturality_left_symm]; rw [← Adjunction.homEquiv_naturality_right_symm]; rw [f.h]

中文:
定理 余algebra.homEquiv_naturality_str_symm
  条件: (adj : F ⊣ G) (V₁ V₂ : 余algebra G) (f : V₁ ⟶ V₂)
  证明: by
  rw [← Adjunction.homEquiv_naturality_left_symm]; rw [← Adjunction.homEquiv_naturality_right_symm]; rw [f.h]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm, Functor, Functor.map_comp, biproduct, classical, eqToHom_map, homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, map_comp
-/
theorem Coalgebra.homEquiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str =
    (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f := by
  rw [← Adjunction.homEquiv_naturality_left_symm]; rw [← Adjunction.homEquiv_naturality_right_symm]; rw [f.h]

/-- Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` a
coalgebra over `G` defined via adjunction applied to the structure map. -/
@[simps!]
/--
Definition of `Algebra.toCoalgebraOf` / `Algebra.toCoalgebraOf` 的定义

English:
definition Algebra.toCoalgebraOf
  signature: (adj : F ⊣ G)
  body: { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

中文:
定义 代数.toCoalgebraOf
  签名: (adj : F ⊣ G)
  定义体: { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

Depends on / 依赖: Algebra, Algebra.homEquiv_naturality_str, adj.homEquiv, homEquiv, homEquiv_naturality_str
-/
def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G where
  obj A :=
    { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

/-- Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G` an algebra over
`F` defined via adjunction applied to the structure map. -/
@[simps!]
/--
Definition of `Coalgebra.toAlgebraOf` / `Coalgebra.toAlgebraOf` 的定义

English:
definition Coalgebra.toAlgebraOf
  signature: (adj : F ⊣ G)
  body: { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

中文:
定义 余algebra.toAlgebraOf
  签名: (adj : F ⊣ G)
  定义体: { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

Depends on / 依赖: Coalgebra, Coalgebra.homEquiv_naturality_str_symm, adj.homEquiv, homEquiv, homEquiv_naturality_str_symm, invFun
-/
def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F where
  obj V :=
    { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to an algebra over the left adjoint a coalgebra over its right
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `AlgCoalgEquiv.unitIso` / `AlgCoalgEquiv.unitIso` 的定义

English:
definition AlgCoalgEquiv.unitIso
  signature: (adj : F ⊣ G)
  body: NatIso.ofComponents (fun _ => Algebra.isoMk <| Iso.refl _)

中文:
定义 AlgCoalgEquiv.unitIso
  签名: (adj : F ⊣ G)
  定义体: NatIso.ofComponents (fun _ => Algebra.isoMk <| Iso.refl _)

Depends on / 依赖: Algebra, Algebra.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def AlgCoalgEquiv.unitIso (adj : F ⊣ G) :
    𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj :=
  NatIso.ofComponents (fun _ => Algebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction, assigning to a coalgebra over the right adjoint an algebra over the left
adjoint and going back is isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `AlgCoalgEquiv.counitIso` / `AlgCoalgEquiv.counitIso` 的定义

English:
definition AlgCoalgEquiv.counitIso
  signature: (adj : F ⊣ G)
  body: NatIso.ofComponents (fun _ => Coalgebra.isoMk <| Iso.refl _)

中文:
定义 AlgCoalgEquiv.counitIso
  签名: (adj : F ⊣ G)
  定义体: NatIso.ofComponents (fun _ => Coalgebra.isoMk <| Iso.refl _)

Depends on / 依赖: Coalgebra, Coalgebra.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G) :=
  NatIso.ofComponents (fun _ => Coalgebra.isoMk <| Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is left adjoint to `G`, then the category of algebras over `F` is equivalent to the
category of coalgebras over `G`. -/
@[simps!]
/--
Definition of `algebraCoalgebraEquiv` / `algebraCoalgebraEquiv` 的定义

English:
definition algebraCoalgebraEquiv
  signature: (adj : F ⊣ G)
  body: Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    simp

中文:
定义 algebraCoalgebraEquiv
  签名: (adj : F ⊣ G)
  定义体: Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    simp

Depends on / 依赖: Algebra, Algebra.toCoalgebraOf, F.obj, HasBiproduct, hasBiproduct_of_preserves, toCoalgebraOf
-/
def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where
  functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    simp

end Adjunction

end Endofunctor

end CategoryTheory
