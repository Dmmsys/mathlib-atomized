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

/-- Structure which allows to construct a category whose types
of objects and morphisms are subtypes of a fixed type `Ω`. -/
/-
**CategoryTheory.SmallCategoryOfSet** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：SmallCategoryOfSet where /-- objects -/ obj : Set Ω /-- morphisms -/ hom (
X Y : obj) : Set Ω /-- identity morphisms -/ id (X : obj) : hom X X /-- the comp
osition of morphisms -/ comp {X Y Z : obj} (f : hom X Y) (g : hom Y Z) : hom X Z
 id_comp {X Y : obj} (f : hom X Y) : comp (id _) f = f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure which allows to construct a category whose types
of objects and morphisms are subtypes of a fixed type `Ω`.
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
/-
**CategoryTheory.SmallCategoryOfSet.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.S
mallCategoryOfSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : SmallCategoryOfSet Ω) : SmallCategory S.obj where
  Hom X Y := S.hom X Y
  id := S.id
  comp := S.comp

/-- The family of all categories such that the types of objects and
morphisms are subtypes of a given type `Ω`. -/
/-
**CategoryTheory.SmallCategoryOfSet.categoryFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.SmallCategoryOfSet`。
形式化陈述：categoryFamily : SmallCategoryOfSet Ω -> Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of all categories such that the types of objects and
morphisms are subtypes of a given type `Ω`.
-/
abbrev categoryFamily : SmallCategoryOfSet Ω → Type w := fun S ↦ S.obj

end SmallCategoryOfSet

variable (C : Type u) [Category.{v} C]

/-- Helper structure for the construction of a term in `SmallCategoryOfSet`.
This involves the choice of bijections between types of objects and morphisms
in a category `C` and subtypes of a type `Ω`. -/
/-
**CategoryTheory.CoreSmallCategoryOfSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory`。
形式化陈述：Type w → (C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max (ma
x u v) w)
参数：C : Type u；max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper structure for the construction of a term in `SmallCategoryOfSet`.
This involves the choice of bijections between types of objects and morphisms
in a category `C` and subtypes of a type `Ω`.
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
/-
**CategoryTheory.CoreSmallCategoryOfSet.smallCategoryOfSet** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.CoreSmallCategoryOfSet`。
形式化陈述：smallCategoryOfSet : SmallCategoryOfSet Ω where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `SmallCategoryOfSet` structure induced by a
`CoreSmallCategoryOfSet` structure.
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
/-
**CategoryTheory.CoreSmallCategoryOfSet.functor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.CoreSmallCategoryOfSet`。
形式化陈述：functor : h.smallCategoryOfSet.obj ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `h : CoreSmallCategoryOfSet Ω C`, this is the
obvious functor `h.smallCategoryOfSet.obj ⥤ C`.
-/
def functor : h.smallCategoryOfSet.obj ⥤ C where
  obj := h.objEquiv
  map := h.homEquiv
  map_id _ := by rw [SmallCategoryOfSet.id_def]; simp
  map_comp _ _ := by rw [SmallCategoryOfSet.comp_def]; simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is fully faithful. -/
/-
**CategoryTheory.CoreSmallCategoryOfSet.fullyFaithfulFunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CoreSmallCategoryOfSet`。
形式化陈述：fullyFaithfulFunctor : h.functor.FullyFaithful where preimage
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is fully faithful.
-/
def fullyFaithfulFunctor : h.functor.FullyFaithful where
  preimage := h.homEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CoreSmallCategoryOfSet.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.CoreSmallCategoryOfSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : h.functor.IsEquivalence where
  faithful := h.fullyFaithfulFunctor.faithful
  full := h.fullyFaithfulFunctor.full
  essSurj.mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h.objEquiv.surjective Y
    exact ⟨_, ⟨Iso.refl _⟩⟩

/-- Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is an equivalence. -/
/-
**CategoryTheory.CoreSmallCategoryOfSet.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CoreSmallCategoryOfSet`。
形式化陈述：equivalence : h.smallCategoryOfSet.obj ≌ C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CoreSmallCategoryOfSet.instIsEquivalenceElemObjSmallCateg
oryOfSetFunctor`：∀ {Ω : Type w} {C : Type u} [inst : CategoryTheory.Category.{v,
 u} C] (h : CategoryTheory.CoreSmallCategoryOfSet Ω C),   h.functor.IsEquival…

--- 原说明 ---
Given `h : CoreSmallCategoryOfSet Ω C`,
the obvious functor `h.smallCategoryOfSet.obj ⥤ C` is an equivalence.
-/
noncomputable def equivalence : h.smallCategoryOfSet.obj ≌ C :=
  h.functor.asEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `h : CoreSmallCategoryOfSet Ω C`, the equivalence of categories
`h.smallCategoryOfSet.obj ≌ C` is actually an isomorphism: it induces
a bijection on the type of arrows. -/
/-
**CategoryTheory.CoreSmallCategoryOfSet.arrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.CoreSmallCategoryOfSet`。
形式化陈述：arrowEquiv : Arrow h.smallCategoryOfSet.obj ≃ Arrow C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `h : CoreSmallCategoryOfSet Ω C`, the equivalence of categories
`h.smallCategoryOfSet.obj ≌ C` is actually an isomorphism: it induces
a bijection on the type of arrows.
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

/-
**CategoryTheory.SmallCategoryOfSet.exists_equivalence** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.SmallCategoryOfSet`。
形式化陈述：exists_equivalence (C : Type u) [Category.{v} C] (h₁ : Cardinal.lift.{w} (
Cardinal.mk C) <= Cardinal.lift.{u} (Cardinal.mk Ω)) (h₂ : forall (X Y : C), Car
dinal.lift.{w} (Cardinal.mk (X ⟶ Y)) <= Cardinal.lift.{v} (Cardinal.mk Ω)) : exi
sts (h : SmallCategoryOfSet Ω), Nonempty (categoryFamily Ω h ≌ C)
参数：C : Type u；h₁ : Cardinal.lift.{w} (Cardinal.mk C) <= Cardinal.lift.{u} (Cardi
nal.mk Ω)；h₂ : forall (X Y : C), Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) <= Card
inal.lift.{v} (Cardinal.mk Ω)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma exists_equivalence (C : Type u) [Category.{v} C]
    (h₁ : Cardinal.lift.{w} (Cardinal.mk C) ≤ Cardinal.lift.{u} (Cardinal.mk Ω))
    (h₂ : ∀ (X Y : C), Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) ≤
      Cardinal.lift.{v} (Cardinal.mk Ω)) :
    ∃ (h : SmallCategoryOfSet Ω), Nonempty (categoryFamily Ω h ≌ C) := by
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

/-- Index set of a representative set of all categories `C` which satisfy
`HasCardinalLT C κ`, see `SmallCategoryCardinalLT.categoryFamily`. -/
/-
**CategoryTheory.SmallCategoryCardinalLT** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：SmallCategoryCardinalLT (κ : Cardinal.{w}) : Type w
参数：κ : Cardinal.{w}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Index set of a representative set of all categories `C` which satisfy
`HasCardinalLT C κ`, see `SmallCategoryCardinalLT.categoryFamily`.
-/
def SmallCategoryCardinalLT (κ : Cardinal.{w}) : Type w :=
  { S : SmallCategoryOfSet κ.ord.ToType // HasCardinalLT (Arrow S.obj) κ}

namespace SmallCategoryCardinalLT

variable (κ : Cardinal.{w})

/-- Given a cardinal `κ`, this is a representative family of all categories `C`
such that `HasCardinalLT C κ`. -/
/-
**CategoryTheory.SmallCategoryCardinalLT.categoryFamily** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.SmallCategoryCardinalLT`。
形式化陈述：categoryFamily (S : SmallCategoryCardinalLT κ) : Type w
参数：S : SmallCategoryCardinalLT κ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cardinal `κ`, this is a representative family of all categories `C`
such that `HasCardinalLT C κ`.
-/
abbrev categoryFamily (S : SmallCategoryCardinalLT κ) : Type w := S.1.obj
/-
**CategoryTheory.SmallCategoryCardinalLT.hasCardinalLT** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.SmallCategoryCardinalLT`。
形式化陈述：hasCardinalLT (S : SmallCategoryCardinalLT κ) : HasCardinalLT (Arrow (cate
goryFamily κ S)) κ
参数：S : SmallCategoryCardinalLT κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma hasCardinalLT (S : SmallCategoryCardinalLT κ) :
    HasCardinalLT (Arrow (categoryFamily κ S)) κ := S.2
/-
**CategoryTheory.SmallCategoryCardinalLT.exists_equivalence** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.SmallCategoryCardinalLT`。
形式化陈述：exists_equivalence (C : Type u) [Category.{v} C] (hC : HasCardinalLT (Arro
w C) κ) : exists (S : SmallCategoryCardinalLT κ), Nonempty (categoryFamily κ S ≌
 C)
参数：C : Type u；hC : HasCardinalLT (Arrow C) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
-/
lemma exists_equivalence (C : Type u) [Category.{v} C] (hC : HasCardinalLT (Arrow C) κ) :
    ∃ (S : SmallCategoryCardinalLT κ),
      Nonempty (categoryFamily κ S ≌ C) := by
  let Ω := κ.ord.ToType
  have ι : Arrow C ↪ Ω := Nonempty.some (by
    rw [← Cardinal.lift_mk_le']
    simpa [Ω] using hC.le)
  have h₁ : Cardinal.lift.{w} (Cardinal.mk C) ≤
      Cardinal.lift.{u} (Cardinal.mk Ω) := by
    rw [Cardinal.lift_mk_le']
    refine ⟨Function.Embedding.trans { toFun X := Arrow.mk (𝟙 X), inj' := ?_ } ι⟩
    intro X Y h
    exact congr_arg Arrow.leftFunc.obj h
  have h₂ (X Y : C) : Cardinal.lift.{w} (Cardinal.mk (X ⟶ Y)) ≤
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

