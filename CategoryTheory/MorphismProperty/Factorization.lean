/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The factorization axiom

In this file, we introduce a type-class `HasFactorization W₁ W₂`, which, given
two classes of morphisms `W₁` and `W₂` in a category `C`, asserts that any morphism
in `C` can be factored as a morphism in `W₁` followed by a morphism in `W₂`. The data
of such factorizations can be packaged in the type `FactorizationData W₁ W₂`.

This shall be used in the formalization of model categories for which the CM5 axiom
asserts that any morphism can be factored as a cofibration followed by a trivial
fibration (or a trivial cofibration followed by a fibration).

We also provide a structure `FunctorialFactorizationData W₁ W₂` which contains
the data of a functorial factorization as above. With this design, when we
formalize certain constructions (e.g. cylinder objects in model categories),
we may first construct them using the data `data : FactorizationData W₁ W₂`.
Without duplication of code, it shall be possible to show these cylinders
are functorial when a term `data : FunctorialFactorizationData W₁ W₂` is available,
the existence of which is asserted in the type-class `HasFunctorialFactorization W₁ W₂`.

We also introduce the class `W₁.comp W₂` of morphisms of the form `i ≫ p` with `W₁ i`
and `W₂ p` and show that `W₁.comp W₂ = ⊤` iff `HasFactorization W₁ W₂` holds (this
is `MorphismProperty.comp_eq_top_iff`).

-/

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C D : Type*} [Category* C] [Category* D] (W₁ W₂ : MorphismProperty C)

/-- Given two classes of morphisms `W₁` and `W₂` on a category `C`, this is
the data of the factorization of a morphism `f : X ⟶ Y` as `i ≫ p` with
`W₁ i` and `W₂ p`. -/
/-
**CategoryTheory.MorphismProperty.MapFactorizationData** 是 Mathlib 中的一个结构，位于命名空间
 `CategoryTheory.MorphismProperty`。
形式化陈述：MapFactorizationData {X Y : C} (f : X ⟶ Y) where /-- the intermediate obje
ct in the factorization -/ Z : C /-- the first morphism in the factorization -/ 
i : X ⟶ Z /-- the second morphism in the factorization -/ p : Z ⟶ Y fac : i ≫ p 
= f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two classes of morphisms `W₁` and `W₂` on a category `C`, this is
the data of the factorization of a morphism `f : X ⟶ Y` as `i ≫ p` with
`W₁ i` and `W₂ p`.
-/
structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  /-- the intermediate object in the factorization -/
  Z : C
  /-- the first morphism in the factorization -/
  i : X ⟶ Z
  /-- the second morphism in the factorization -/
  p : Z ⟶ Y
  fac : i ≫ p = f := by cat_disch
  hi : W₁ i
  hp : W₂ p

namespace MapFactorizationData

attribute [reassoc (attr := simp)] fac

variable {X Y : C} (f : X ⟶ Y)

/-- The opposite of a factorization. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.MapFactorizationData.op** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MorphismProperty.MapFactorizationData`。
形式化陈述：op {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f) : MapFactoriz
ationData W₂.op W₁.op f.op where Z
参数：hf : MapFactorizationData W₁ W₂ f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…

--- 原说明 ---
The opposite of a factorization.
-/
def op {X Y : C} {f : X ⟶ Y} (hf : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.op W₁.op f.op where
  Z := Opposite.op hf.Z
  i := hf.p.op
  p := hf.i.op
  fac := Quiver.Hom.unop_inj (by simp)
  hi := hf.hp
  hp := hf.hi

/-- The factorization obtained from a factorization in the opposite category. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.MapFactorizationData.unop** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.MorphismProperty.MapFactorizationData`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W₁
 W₂ : CategoryTheory.MorphismProperty Cᵒᵖ} →       {X Y : Cᵒᵖ} → {f : X ⟶ Y} → W
₁.MapFactorizationData W₂ f → W₂.unop.MapFactorizationData W₁.unop f.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The factorization obtained from a factorization in the opposite category.
-/
protected def unop {W₁ W₂ : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y}
    (φ : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.unop W₁.unop f.unop where
  Z := φ.Z.unop
  i := φ.p.unop
  p := φ.i.unop
  hi := φ.hp
  hp := φ.hi
  fac := by simp [← unop_comp]

/-- The bijection between factorizations in `C` and factorizations in `Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.MapFactorizationData.opEquiv** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.MorphismProperty.MapFactorizationData`。
形式化陈述：opEquiv {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y} : MapFactorizat
ionData W₁ W₂ f ≃ MapFactorizationData W₂.op W₁.op f.op where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between factorizations in `C` and factorizations in `Cᵒᵖ`.
-/
def opEquiv {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    MapFactorizationData W₁ W₂ f ≃ MapFactorizationData W₂.op W₁.op f.op where
  toFun φ := φ.op
  invFun φ := φ.unop

end MapFactorizationData

/-- The data of a term in `MapFactorizationData W₁ W₂ f` for any morphism `f`. -/
/-
**CategoryTheory.MorphismProperty.FactorizationData** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty`。
形式化陈述：FactorizationData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a term in `MapFactorizationData W₁ W₂ f` for any morphism `f`.
-/
abbrev FactorizationData := ∀ {X Y : C} (f : X ⟶ Y), MapFactorizationData W₁ W₂ f

/-- The factorization axiom for two classes of morphisms `W₁` and `W₂` in a category `C`. It
asserts that any morphism can be factored as a morphism in `W₁` followed by a morphism
in `W₂`. -/
/-
**CategoryTheory.MorphismProperty.HasFactorization** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The factorization axiom for two classes of morphisms `W₁` and `W₂` in a category
 `C`. It
asserts that any morphism can be factored as a morphism in `W₁` followed by a mo
rphism
in `W₂`.
-/
class HasFactorization : Prop where
  nonempty_mapFactorizationData {X Y : C} (f : X ⟶ Y) : Nonempty (MapFactorizationData W₁ W₂ f)

/-- A chosen term in `FactorizationData W₁ W₂` when `HasFactorization W₁ W₂` holds. -/
/-
**CategoryTheory.MorphismProperty.factorizationData** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasFactorization.nonempty_mapFactorizati
onData`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W₁ W₂ : 
CategoryTheory.MorphismProperty C}   [self : W₁.HasFactorization W₂]…

--- 原说明 ---
A chosen term in `FactorizationData W₁ W₂` when `HasFactorization W₁ W₂` holds.
-/
noncomputable def factorizationData [HasFactorization W₁ W₂] : FactorizationData W₁ W₂ :=
  fun _ => Nonempty.some (HasFactorization.nonempty_mapFactorizationData _)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFactorization W₁ W₂] : HasFactorization W₂.op W₁.op where
  nonempty_mapFactorizationData f := ⟨(factorizationData W₁ W₂ f.unop).op⟩

/-- The class of morphisms that are of the form `i ≫ p` with `W₁ i` and `W₂ p`. -/
/-
**CategoryTheory.MorphismProperty.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MorphismProperty`。
形式化陈述：comp : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms that are of the form `i ≫ p` with `W₁ i` and `W₂ p`.
-/
def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)
/-
**CategoryTheory.MorphismProperty.comp_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：comp_eq_top_iff : W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma comp_eq_top_iff : W₁.comp W₂ = ⊤ ↔ HasFactorization W₁ W₂ := by
  constructor
  · intro h
    refine ⟨fun f => ?_⟩
    have : W₁.comp W₂ f := by simp only [h, top_apply]
    exact ⟨this.some⟩
  · intro
    ext X Y f
    simp only [top_apply, iff_true]
    exact ⟨factorizationData W₁ W₂ f⟩

/-- The data of a functorial factorization of any morphism in `C` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData** 是 Mathlib 中的一个结构
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：FunctorialFactorizationData where /-- the intermediate objects in the fact
orizations -/ Z : Arrow C ⥤ C /-- the first morphism in the factorizations -/ i 
: Arrow.leftFunc ⟶ Z /-- the second morphism in the factorizations -/ p : Z ⟶ Ar
row.rightFunc fac : i ≫ p = Arrow.leftToRight
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a functorial factorization of any morphism in `C` as a morphism in `
W₁`
followed by a morphism in `W₂`.
-/
structure FunctorialFactorizationData where
  /-- the intermediate objects in the factorizations -/
  Z : Arrow C ⥤ C
  /-- the first morphism in the factorizations -/
  i : Arrow.leftFunc ⟶ Z
  /-- the second morphism in the factorizations -/
  p : Z ⟶ Arrow.rightFunc
  fac : i ≫ p = Arrow.leftToRight := by cat_disch
  hi (f : Arrow C) : W₁ (i.app f)
  hp (f : Arrow C) : W₂ (p.app f)

namespace FunctorialFactorizationData

variable {W₁ W₂}
variable (data : FunctorialFactorizationData W₁ W₂)

attribute [reassoc (attr := simp)] fac

@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.fac_app** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.MorphismProperty.FunctorialFactorizationData.fac`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.
MorphismProperty C}   (self : W₁.FunctorialFactorizat…
· 使用定理 `CategoryTheory.Arrow.leftToRight_app`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] (f : CategoryTheory.Arrow C),   CategoryTheory.Arrow.left
ToRight.app f = f.hom
-/
lemma fac_app {f : Arrow C} : data.i.app f ≫ data.p.app f = f.hom := by
  rw [← NatTrans.comp_app, fac, Arrow.leftToRight_app]

/-- If `W₁ ≤ W₁'` and `W₂ ≤ W₂'`, then a functorial factorization for `W₁` and `W₂` induces
a functorial factorization for `W₁'` and `W₂'`. -/
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.ofLE** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：ofLE {W₁' W₂' : MorphismProperty C} (le₁ : W₁ <= W₁') (le₂ : W₂ <= W₂') : 
FunctorialFactorizationData W₁' W₂' where Z
参数：le₁ : W₁ <= W₁'；le₂ : W₂ <= W₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W₁ ≤ W₁'` and `W₂ ≤ W₂'`, then a functorial factorization for `W₁` and `W₂` 
induces
a functorial factorization for `W₁'` and `W₂'`.
-/
def ofLE {W₁' W₂' : MorphismProperty C} (le₁ : W₁ ≤ W₁') (le₂ : W₂ ≤ W₂') :
    FunctorialFactorizationData W₁' W₂' where
  Z := data.Z
  i := data.i
  p := data.p
  hi f := le₁ _ (data.hi f)
  hp f := le₂ _ (data.hp f)

set_option backward.isDefEq.respectTransparency false in
/-- The term in `FactorizationData W₁ W₂` that is deduced from a functorial factorization. -/
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.factorizationData*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizati
onData`。
形式化陈述：factorizationData : FactorizationData W₁ W₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The term in `FactorizationData W₁ W₂` that is deduced from a functorial factoriz
ation.
-/
def factorizationData : FactorizationData W₁ W₂ := fun f =>
  { Z := data.Z.obj (Arrow.mk f)
    i := data.i.app (Arrow.mk f)
    p := data.p.app (Arrow.mk f)
    hi := data.hi _
    hp := data.hp _ }

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)

/-- When `data : FunctorialFactorizationData W₁ W₂`, this is the
morphism `(data.factorizationData f).Z ⟶ (data.factorizationData g).Z` expressing the
functoriality of the intermediate objects of the factorizations
for `φ : Arrow.mk f ⟶ Arrow.mk g`. -/
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.mapZ** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `data : FunctorialFactorizationData W₁ W₂`, this is the
morphism `(data.factorizationData f).Z ⟶ (data.factorizationData g).Z` expressin
g the
functoriality of the intermediate objects of the factorizations
for `φ : Arrow.mk f ⟶ Arrow.mk g`.
-/
def mapZ : (data.factorizationData f).Z ⟶ (data.factorizationData g).Z := data.Z.map φ

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.i_mapZ** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：i_mapZ : (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.facto
rizationData g).i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.mapZ_p** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：mapZ_p : data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationD
ata f).p ≫ φ.right
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma mapZ_p :
    data.mapZ φ ≫ (data.factorizationData g).p = (data.factorizationData f).p ≫ φ.right :=
  data.p.naturality φ

variable (f) in
@[simp]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.mapZ_id** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma mapZ_id : data.mapZ (𝟙 (Arrow.mk f)) = 𝟙 _ :=
  data.Z.map_id _

@[reassoc, simp]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.mapZ_comp** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizationData`。
形式化陈述：mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) : da
ta.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ
参数：ψ : Arrow.mk g ⟶ Arrow.mk h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma mapZ_comp {X'' Y'' : C} {h : X'' ⟶ Y''} (ψ : Arrow.mk g ⟶ Arrow.mk h) :
    data.mapZ (φ ≫ ψ) = data.mapZ φ ≫ data.mapZ ψ :=
  data.Z.map_comp _ _

end

section

variable (J : Type*) [Category* J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `FunctorialFactorizationData.functorCategory`. -/
@[simps]
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.functorCategory.Z*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorizati
onData.functorCategory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W₁
 W₂ : CategoryTheory.MorphismProperty C} →       W₁.FunctorialFactorizationData 
W₂ →         (J : Type u_3) →           [inst_1 : CategoryTheory.Category.{v_3, 
u_3} J] →             CategoryTheory.Functor (CategoryTheory.Arrow (CategoryTheo
ry.Functor J C)) (CategoryTheory.Functor J C)
参数：J : Type u_3；CategoryTheory.Arrow (CategoryTheory.Functor J C)；CategoryTheory
.Functor J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `FunctorialFactorizationData.functorCategory`.
-/
def functorCategory.Z : Arrow (J ⥤ C) ⥤ J ⥤ C where
  obj f :=
    { obj j := (data.factorizationData (f.hom.app j)).Z
      map φ := data.mapZ (Arrow.homMk (f.left.map φ) (f.right.map φ))
      map_id j := by
        rw [← data.mapZ_id (f.hom.app j)]
        congr <;> simp
      map_comp _ _ := by
        rw [← data.mapZ_comp]
        congr <;> simp }
  map τ :=
    { app j := data.mapZ (Arrow.homMk (τ.left.app j) (τ.right.app j) (congr_app τ.w j))
      naturality _ _ _ := by
        dsimp
        rw [← data.mapZ_comp, ← data.mapZ_comp]
        congr 1
        ext <;> simp }
  map_id f := by
    ext j
    dsimp
    rw [← data.mapZ_id]
    congr 1
  map_comp f g := by
    ext j
    dsimp
    rw [← data.mapZ_comp]
    congr 1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functorial factorization in the category `C` extends to the functor category `J ⥤ C`. -/
/-
**CategoryTheory.MorphismProperty.FunctorialFactorizationData.functorCategory** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.FunctorialFactorization
Data`。
形式化陈述：functorCategory : FunctorialFactorizationData (W₁.functorCategory J) (W₂.f
unctorCategory J) where Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functorial factorization in the category `C` extends to the functor category `
J ⥤ C`.
-/
def functorCategory :
    FunctorialFactorizationData (W₁.functorCategory J) (W₂.functorCategory J) where
  Z := functorCategory.Z data J
  i := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).i } }
  p := { app := fun f => { app := fun j => (data.factorizationData (f.hom.app j)).p } }
  hi _ _ := data.hi _
  hp _ _ := data.hp _

end

end FunctorialFactorizationData

/-- The functorial factorization axiom for two classes of morphisms `W₁` and `W₂` in a
category `C`. It asserts that any morphism can be factored in a functorial manner
as a morphism in `W₁` followed by a morphism in `W₂`. -/
/-
**CategoryTheory.MorphismProperty.HasFunctorialFactorization** 是 Mathlib 中的一个归纳类
型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial factorization axiom for two classes of morphisms `W₁` and `W₂` in
 a
category `C`. It asserts that any morphism can be factored in a functorial manne
r
as a morphism in `W₁` followed by a morphism in `W₂`.
-/
class HasFunctorialFactorization : Prop where
  nonempty_functorialFactorizationData : Nonempty (FunctorialFactorizationData W₁ W₂)

/-- A chosen term in `FunctorialFactorizationData W₁ W₂` when the functorial factorization
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个公理，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
axiom `HasFunctorialFactorization W₁ W₂` holds. -/
/-
**CategoryTheory.MorphismProperty.functorialFactorizationData** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：functorialFactorizationData [HasFunctorialFactorization W₁ W₂] : Functoria
lFactorizationData W₁ W₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.HasFunctorialFactorization.nonempty_func
torialFactorizationData`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, 
u_1} C} {W₁ W₂ : CategoryTheory.MorphismProperty C}   [self : W₁.HasFunctorialFa
ctori…

--- 原说明 ---
A chosen term in `FunctorialFactorizationData W₁ W₂` when the functorial factori
zation
axiom `HasFunctorialFactorization W₁ W₂` holds.
-/
noncomputable def functorialFactorizationData [HasFunctorialFactorization W₁ W₂] :
    FunctorialFactorizationData W₁ W₂ :=
  Nonempty.some (HasFunctorialFactorization.nonempty_functorialFactorizationData)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFunctorialFactorization W₁ W₂] : HasFactorization W₁ W₂ where
  nonempty_mapFactorizationData f := ⟨(functorialFactorizationData W₁ W₂).factorizationData f⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFunctorialFactorization W₁ W₂] (J : Type*) [Category* J] :
    HasFunctorialFactorization (W₁.functorCategory J) (W₂.functorCategory J) :=
  ⟨⟨(functorialFactorizationData W₁ W₂).functorCategory J⟩⟩

set_option backward.defeqAttrib.useBackward true in
variable {W₁ W₂} in
/-- The term in `MapFactorizationData (W₁.inverseImage F) (W₂.inverseImage F) f`
deduced from `h : MapFactorizationData W₁ W₂ (F.map f)` when `F` is an equivalence
of categories and both `W₁` and `W₂` respect isomorphisms. -/
/-
**CategoryTheory.MorphismProperty.MapFactorizationData.ofIsEquivalence** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.MapFactorizationData`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {W
₁ W₂ : CategoryTheory.MorphismProperty C} →           {F : CategoryTheory.Functo
r D C} →             [F.IsEquivalence] →               [W₁.RespectsIso] →       
          [W₂.RespectsIso] →                   {X Y : D} →                     {
f : X ⟶ Y} →                       W₁.MapFactorizationData W₂ (F.map f) →       
                  (W₁.inverseImage F).MapFactorizationData (W₂.inverseImage F) f
参数：F.map f；W₁.inverseImage F；W₂.inverseImage F。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
The term in `MapFactorizationData (W₁.inverseImage F) (W₂.inverseImage F) f`
deduced from `h : MapFactorizationData W₁ W₂ (F.map f)` when `F` is an equivalen
ce
of categories and both `W₁` and `W₂` respect isomorphisms.
-/
noncomputable def MapFactorizationData.ofIsEquivalence {F : D ⥤ C}
    [F.IsEquivalence] [W₁.RespectsIso] [W₂.RespectsIso]
    {X Y : D} {f : X ⟶ Y} (h : MapFactorizationData W₁ W₂ (F.map f)) :
    MapFactorizationData (W₁.inverseImage F) (W₂.inverseImage F) f where
  Z := F.objPreimage h.Z
  i := F.preimage (h.i ≫ (F.objObjPreimageIso h.Z).inv)
  p := F.preimage ((F.objObjPreimageIso h.Z).hom ≫ h.p)
  hi := by
    refine (W₁.arrow_mk_iso_iff ?_).1 h.hi
    refine Arrow.isoMk (Iso.refl _) (F.objObjPreimageIso h.Z).symm ?_
    simp [F.map_preimage]
  hp := by
    refine (W₂.arrow_mk_iso_iff ?_).1 h.hp
    refine Arrow.isoMk (F.objObjPreimageIso h.Z).symm (Iso.refl _) ?_
    simp [F.map_preimage]
  fac := F.map_injective (by simp)
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : D ⥤ C) [F.IsEquivalence]
    [W₁.RespectsIso] [W₂.RespectsIso] [HasFactorization W₁ W₂] :
    HasFactorization (W₁.inverseImage F) (W₂.inverseImage F) where
  nonempty_mapFactorizationData f :=
    ⟨(factorizationData W₁ W₂ (F.map f)).ofIsEquivalence⟩

end MorphismProperty

end CategoryTheory

