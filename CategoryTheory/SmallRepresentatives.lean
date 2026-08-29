/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Representatives of small categories

Given a type `Ω : Type w`, we construct a structure `SmallCategoryOfSet Ω : Type w`
which consists of the data and axioms that allows to define a category
structure such that the type of objects and morphisms identify to subtypes of `Ω`.

This allows to define a small family of small categories
`SmallCategoryOfSet.categoryFamily : SmallCategoryOfSet Ω → Type w`
which, up to equivalence, represents all categories such that
types of objects and morphisms have cardinalities less than or equal to
that of `Ω` (see `SmallCategoryOfSet.exists_equivalence`).

Given a cardinal `κ : Cardinal.{w}`, we also provide a small family of categories
`SmallCategoryCardinalLT.categoryFamily κ` which represents (up to isomorphism)
any category `C` such that `HasCardinalLT C κ` holds.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (Ω : Type w)

/--
Definition of `SmallCategoryOfSet` / `SmallCategoryOfSet` 的定义

English:
structure SmallCategoryOfSet
  parameters: where
  axioms and operations (7):
    - obj : Set Ω
    - hom((X Y : obj)) : Set Ω
    - id((X : obj)) : hom X X
    - comp({X Y Z : obj} (f : hom X Y) (g : hom Y Z)) : hom X Z
    - id_comp({X Y : obj} (f : hom X Y)) : comp (id _) f = f  [default: by cat_disch]
    - comp_id({X Y : obj} (f : hom X Y)) : comp f (id _) = f  [default: by cat_disch]
    - assoc({X Y Z T : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z T)) : comp (comp f g) h = comp f (comp g h)  [default: by cat_disch]

中文:
结构 SmallCategoryOfSet
  参数: where
  公理与运算 (7 个):
    - obj : 集合 Ω
    - hom((X Y : obj)) : 集合 Ω
    - id((X : obj)) : hom X X
    - comp({X Y Z : obj} (f : hom X Y) (g : hom Y Z)) : hom X Z
    - id_comp({X Y : obj} (f : hom X Y)) : comp (id _) f = f  [默认: by cat_disch]
    - comp_id({X Y : obj} (f : hom X Y)) : comp f (id _) = f  [默认: by cat_disch]
    - assoc({X Y Z T : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z T)) : comp (comp f g) h = comp f (comp g h)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, comp_id
-/
structure SmallCategoryOfSet where
  /-- objects -/
  obj : Set Ω
  /-- morphisms -/
  hom (X Y : obj) : Set Ω
  /-- identity morphisms -/
  id (X : obj) : hom X X
  /-- the composition of morphisms -/
  comp {X Y Z : obj} (f : hom X Y) (g : hom Y Z) : hom X Z
  id_comp {X Y : obj} (f : hom X Y) : comp (id _) f = f := by cat_disch
  comp_id {X Y : obj} (f : hom X Y) : comp f (id _) = f := by cat_disch
  assoc {X Y Z T : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z T) :
      comp (comp f g) h = comp f (comp g h) := by cat_disch

namespace SmallCategoryOfSet

attribute [simp] id_comp comp_id assoc

@[simps]
instance (S : SmallCategoryOfSet Ω) : SmallCategory S.obj where
  Hom X Y := S.hom X Y
  id := S.id
  comp := S.comp

/--
Definition of `categoryFamily` / `categoryFamily` 的定义

English:
abbreviation categoryFamily
  signature: : SmallCategoryOfSet Ω -> Type w
  body: fun S => S.obj

中文:
缩写 categoryFamily
  签名: : SmallCategoryOfSet Ω -> 类型 w
  定义体: fun S => S.obj

Depends on / 依赖: S.obj
-/
abbrev categoryFamily : SmallCategoryOfSet Ω -> Type w := fun S => S.obj

end SmallCategoryOfSet

variable (C : Type u) [Category.{v} C]

/--
Definition of `CoreSmallCategoryOfSet` / `CoreSmallCategoryOfSet` 的定义

English:
structure CoreSmallCategoryOfSet
  parameters: where
  axioms and operations (4):
    - obj : Set Ω
    - hom((X Y : obj)) : Set Ω
    - objEquiv : obj ≃ C
    - homEquiv({X Y : obj}) : hom X Y ≃ (objEquiv X ⟶ objEquiv Y)

中文:
结构 余reSmallCategoryOfSet
  参数: where
  公理与运算 (4 个):
    - obj : 集合 Ω
    - hom((X Y : obj)) : 集合 Ω
    - objEquiv : obj ≃ C
    - homEquiv({X Y : obj}) : hom X Y ≃ (objEquiv X ⟶ objEquiv Y)
-/
structure CoreSmallCategoryOfSet where
  /-- objects -/
  obj : Set Ω
  /-- morphisms -/
  hom (X Y : obj) : Set Ω
  /-- a bijection between the types of objects -/
  objEquiv : obj ≃ C
  /-- a bijection between the types of morphisms -/
  homEquiv {X Y : obj} : hom X Y ≃ (objEquiv X ⟶ objEquiv Y)

namespace CoreSmallCategoryOfSet

variable {Ω C} (h : CoreSmallCategoryOfSet Ω C)

/-- The `SmallCategoryOfSet` structure induced by a
`CoreSmallCategoryOfSet` structure. -/
@[simps]
/--
Definition of `smallCategoryOfSet` / `smallCategoryOfSet` 的定义

English:
definition smallCategoryOfSet
  signature: : SmallCategoryOfSet Ω where
  body: h.obj
  hom := h.hom
  id X := h.homEquiv.symm (𝟙 _)
  comp f g := h.homEquiv.symm (h.homEquiv f ≫ h.homEquiv g)

中文:
定义 smallCategoryOfSet
  签名: : SmallCategoryOfSet Ω where
  定义体: h.obj
  hom := h.hom
  id X := h.homEquiv.symm (𝟙 _)
  comp f g := h.homEquiv.symm (h.homEquiv f ≫ h.homEquiv g)

Depends on / 依赖: h.obj
-/
def smallCategoryOfSet : SmallCategoryOfSet Ω where
  obj := h.obj
  hom := h.hom
  id X := h.homEquiv.symm (𝟙 _)
  comp f g := h.homEquiv.symm (h.homEquiv f ≫ h.homEquiv g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `h : CoreSmallCategoryOfSet Ω C`, this is the
obvious functor `h.smallCategoryOfSet.obj ⥤ C`. -/
@[simps!]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : h.smallCategoryOfSet.obj ⥤ C where
  body: h.objEquiv
  map := h.homEquiv
  map_id _ := by rw [SmallCategoryOfSet.id_def]; simp
  map_comp _ _ := by rw [SmallCategoryOfSet.comp_def]; simp

中文:
定义 functor
  签名: : h.smallCategoryOfSet.obj ⥤ C where
  定义体: h.objEquiv
  map := h.homEquiv
  map_id _ := by rw [SmallCategoryOfSet.id_def]; simp
  map_comp _ _ := by rw [SmallCategoryOfSet.comp_def]; simp

Depends on / 依赖: h.objEquiv, objEquiv
-/
def functor : h.smallCategoryOfSet.obj ⥤ C where
  obj := h.objEquiv
  map := h.homEquiv
  map_id _ := by rw [SmallCategoryOfSet.id_def]; simp
  map_comp _ _ := by rw [SmallCategoryOfSet.comp_def]; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fullyFaithfulFunctor` / `fullyFaithfulFunctor` 的定义

English:
definition fullyFaithfulFunctor
  signature: : h.functor.FullyFaithful where
  body: h.homEquiv.symm

中文:
定义 fullyFaithfulFunctor
  签名: : h.functor.满忠实 where
  定义体: h.homEquiv.symm

Depends on / 依赖: h.homEquiv.symm, homEquiv
-/
def fullyFaithfulFunctor : h.functor.FullyFaithful where
  preimage := h.homEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: h.functor.IsEquivalence
  body: h.fullyFaithfulFunctor.faithful
  full := h.fullyFaithfulFunctor.full
  essSurj.mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

中文:
实例 :
  签名: h.functor.是等价
  定义体: h.fullyFaithfulFunctor.faithful
  full := h.fullyFaithfulFunctor.full
  essSurj.mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

Depends on / 依赖: faithful, fullyFaithfulFunctor, h.fullyFaithfulFunctor.faithful
-/
instance : h.functor.IsEquivalence where
  faithful := h.fullyFaithfulFunctor.faithful
  full := h.fullyFaithfulFunctor.full
  essSurj.mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : h.smallCategoryOfSet.obj ≌ C
  body: h.functor.asEquivalence

中文:
定义 equivalence
  签名: : h.smallCategoryOfSet.obj ≌ C
  定义体: h.functor.asEquivalence

Depends on / 依赖: asEquivalence, functor, h.functor.asEquivalence
-/
noncomputable def equivalence : h.smallCategoryOfSet.obj ≌ C :=
  h.functor.asEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `arrowEquiv` / `arrowEquiv` 的定义

English:
definition arrowEquiv
  signature: : Arrow h.smallCategoryOfSet.obj ≃ Arrow C
  body: Equiv.ofBijective h.functor.mapArrow.obj (by
    constructor
    · rintro ⟨x, y, f⟩ ⟨x', y', g⟩ hfg
      obtain rfl : x = x' := by simpa using! congr_arg Arrow.leftFunc.obj hfg
      obtain rfl : y = y' := by simpa using! congr_arg Arrow.rightFunc.obj hfg
      obtain rfl : f = g := by simpa [Arrow

中文:
定义 arrowEquiv
  签名: : 箭头 h.smallCategoryOfSet.obj ≃ 箭头 C
  定义体: Equiv.ofBijective h.functor.mapArrow.obj (by
    constructor
    · rintro ⟨x, y, f⟩ ⟨x', y', g⟩ hfg
      obtain rfl : x = x' := by simpa using! congr_arg Arrow.leftFunc.obj hfg
      obtain rfl : y = y' := by simpa using! congr_arg Arrow.rightFunc.obj hfg
      obtain rfl : f = g := by simpa [Arrow

Depends on / 依赖: Arrow.leftFunc.obj, Arrow.mk, Arrow.mk_eq_mk_iff, Arrow.rightFunc.obj, Equiv.ofBijective, congr_arg, functor, h.functor.mapArrow.obj, h.homEquiv.surjective, h.objEquiv.surjective, homEquiv, leftFunc, mapArrow, mk_eq_mk_iff, objEquiv, ofBijective, rightFunc, surjective
-/
noncomputable def arrowEquiv : Arrow h.smallCategoryOfSet.obj ≃ Arrow C :=
  Equiv.ofBijective h.functor.mapArrow.obj (by
    constructor
    · rintro ⟨x, y, f⟩ ⟨x', y', g⟩ hfg
      obtain rfl : x = x' := by simpa using! congr_arg Arrow.leftFunc.obj hfg
      obtain rfl : y = y' := by simpa using! congr_arg Arrow.rightFunc.obj hfg
      obtain rfl : f = g := by simpa [Arrow.mk_eq_mk_iff] using! hfg
      rfl
    · rintro ⟨X, Y, f⟩
      obtain ⟨x, rfl⟩ := h.objEquiv.surjective X
      obtain ⟨y, rfl⟩ := h.objEquiv.surjective Y
      obtain ⟨f, rfl⟩ := h.homEquiv.surjective f
      exact ⟨Arrow.mk f, rfl⟩)

end CoreSmallCategoryOfSet

namespace SmallCategoryOfSet

/--
lemma `exists_equivalence` / 引理 `exists_equivalence`

English:
lemma exists_equivalence
  statement: (C : Type u) [Category.{v} C]
  proof: by
  let f₁ := (Cardinal.lift_mk_le'.1 h₁).some
  let f₂ (X Y) := (Cardinal.lift_mk_le'.1 (h₂ X Y)).some
  let e := Equiv.ofInjective _ f₁.injective
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      

中文:
引理 存在_equivalence
  结论: (C : 类型u) [范畴.{v} C]
  证明: by
  let f₁ := (Cardinal.lift_mk_le'.1 h₁).some
  let f₂ (X Y) := (Cardinal.lift_mk_le'.1 (h₂ X Y)).some
  let e := Equiv.ofInjective _ f₁.injective
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      

Depends on / 依赖: Cardinal, Cardinal.lift_mk_le, CoreSmallCategoryOfSet, Equiv.ofInjective, Set.range, e.symm, equivalence, h.equivalence, h.smallCategoryOfSet, homEquiv, injective, lift_mk_le, objEquiv, ofInjective, smallCategoryOfSet
-/
lemma exists_equivalence (C : Type u) [Category.{v} C]
    (h₁ : Cardinal.lift.{w} (Cardinal.mk C) <= Cardinal.lift.{u} (Cardinal.mk Ω))
    (h₂ : forall (X Y : C), Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) <=
      Cardinal.lift.{v} (Cardinal.mk Ω)) :
    exists (h : SmallCategoryOfSet Ω), Nonempty (categoryFamily Ω h ≌ C) := by
  let f₁ := (Cardinal.lift_mk_le'.1 h₁).some
  let f₂ (X Y) := (Cardinal.lift_mk_le'.1 (h₂ X Y)).some
  let e := Equiv.ofInjective _ f₁.injective
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      homEquiv {_ _} := by simpa using (Equiv.ofInjective _ ((f₂ _ _).injective)).symm }
  exact ⟨h.smallCategoryOfSet, ⟨h.equivalence⟩⟩

end SmallCategoryOfSet

/--
Definition of `SmallCategoryCardinalLT` / `SmallCategoryCardinalLT` 的定义

English:
definition SmallCategoryCardinalLT
  signature: (κ : Cardinal.{w})
  body: { S : SmallCategoryOfSet κ.ord.ToType // HasCardinalLT (Arrow S.obj) κ}

中文:
定义 SmallCategoryCardinalLT
  签名: (κ : 基数.{w})
  定义体: { S : SmallCategoryOfSet κ.ord.ToType // HasCardinalLT (Arrow S.obj) κ}

Depends on / 依赖: HasCardinalLT, S.obj, SmallCategoryOfSet, ToType, ord.ToType
-/
def SmallCategoryCardinalLT (κ : Cardinal.{w}) : Type w :=
  { S : SmallCategoryOfSet κ.ord.ToType // HasCardinalLT (Arrow S.obj) κ}

namespace SmallCategoryCardinalLT

variable (κ : Cardinal.{w})

/--
Definition of `categoryFamily` / `categoryFamily` 的定义

English:
abbreviation categoryFamily
  signature: (S : SmallCategoryCardinalLT κ)
  body: S.1.obj

中文:
缩写 categoryFamily
  签名: (S : SmallCategoryCardinalLT κ)
  定义体: S.1.obj
-/
abbrev categoryFamily (S : SmallCategoryCardinalLT κ) : Type w := S.1.obj

/--
lemma `hasCardinalLT` / 引理 `hasCardinalLT`

English:
lemma hasCardinalLT
  given: (S : SmallCategoryCardinalLT κ)
  proof: S.2

中文:
引理 hasCardinalLT
  条件: (S : SmallCategoryCardinalLT κ)
  证明: S.2
-/
lemma hasCardinalLT (S : SmallCategoryCardinalLT κ) :
    HasCardinalLT (Arrow (categoryFamily κ S)) κ := S.2

/--
lemma `exists_equivalence` / 引理 `exists_equivalence`

English:
lemma exists_equivalence
  given: (C : Type u) [Category.{v} C] (hC : HasCardinalLT (Arrow C) κ)
  proof: by
  let Ω := κ.ord.ToType
  have ι : Arrow C ↪ Ω := Nonempty.some (by
    rw [← Cardinal.lift_mk_le']
    simpa [Ω] using hC.le)
  have h₁ : Cardinal.lift.{w} (Cardinal.mk C) <=
      Cardinal.lift.{u} (Cardinal.mk Ω) := by
    rw [Cardinal.lift_mk_le']
    refine ⟨Function.Embedding.trans { toFun 

中文:
引理 存在_equivalence
  条件: (C : 类型u) [范畴.{v} C] (hC : HasCardinalLT (箭头 C) κ)
  证明: by
  let Ω := κ.ord.ToType
  have ι : Arrow C ↪ Ω := Nonempty.some (by
    rw [← Cardinal.lift_mk_le']
    simpa [Ω] using hC.le)
  have h₁ : Cardinal.lift.{w} (Cardinal.mk C) <=
      Cardinal.lift.{u} (Cardinal.mk Ω) := by
    rw [Cardinal.lift_mk_le']
    refine ⟨Function.Embedding.trans { toFun 

Depends on / 依赖: Arrow.leftFunc.obj, Arrow.mk, Cardinal, Cardinal.lift, Cardinal.lift_mk_le, Cardinal.mk, Embedding, Function, Function.Embedding.trans, Nonempty, Nonempty.some, ToType, congr_arg, hC.le, leftFunc, lift_mk_le, ord.ToType
-/
lemma exists_equivalence (C : Type u) [Category.{v} C] (hC : HasCardinalLT (Arrow C) κ) :
    exists (S : SmallCategoryCardinalLT κ),
      Nonempty (categoryFamily κ S ≌ C) := by
  let Ω := κ.ord.ToType
  have ι : Arrow C ↪ Ω := Nonempty.some (by
    rw [← Cardinal.lift_mk_le']
    simpa [Ω] using hC.le)
  have h₁ : Cardinal.lift.{w} (Cardinal.mk C) <=
      Cardinal.lift.{u} (Cardinal.mk Ω) := by
    rw [Cardinal.lift_mk_le']
    refine ⟨Function.Embedding.trans { toFun X := Arrow.mk (𝟙 X), inj' := ?_ } ι⟩
    intro X Y h
    exact congr_arg Arrow.leftFunc.obj h
  have h₂ (X Y : C) : Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) <=
      Cardinal.lift.{v} (Cardinal.mk Ω) := by
    rw [Cardinal.lift_mk_le']
    refine ⟨Function.Embedding.trans { toFun f := Arrow.mk f, inj' := ?_ } ι⟩
    intro f g h
    simpa [Arrow.mk_eq_mk_iff] using h
  let f₁ := (Cardinal.lift_mk_le'.1 h₁).some
  let f₂ (X Y) := (Cardinal.lift_mk_le'.1 (h₂ X Y)).some
  let e := Equiv.ofInjective _ f₁.injective
  let h : CoreSmallCategoryOfSet Ω C :=
    { obj := Set.range f₁
      hom X Y := Set.range (f₂ (e.symm X) (e.symm Y))
      objEquiv := e.symm
      homEquiv {_ _} := by simpa using (Equiv.ofInjective _ ((f₂ _ _).injective)).symm }
  refine ⟨⟨h.smallCategoryOfSet, ?_⟩, ⟨h.equivalence⟩⟩
  rwa [hasCardinalLT_iff_of_equiv h.arrowEquiv]

end SmallCategoryCardinalLT

end CategoryTheory
