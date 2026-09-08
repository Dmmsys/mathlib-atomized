/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Construction for the small object argument

Given a family of morphisms `f i : A i ⟶ B i` in a category `C`,
we define a functor
`SmallObject.functor f : Arrow S ⥤ Arrow S` which sends
an object given by arrow `πX : X ⟶ S` to the pushout `functorObj f πX`:
```
∐ functorObjSrcFamily f πX ⟶       X

            |                      |
            |                      |
            v                      v

∐ functorObjTgtFamily f πX ⟶ functorObj f πX
```
where the morphism on the left is a coproduct (of copies of maps `f i`)
indexed by a type `FunctorObjIndex f πX` which parametrizes the
diagrams of the form
```
A i ⟶ X
 |    |
 |    |
 v    v
B i ⟶ S
```

The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is part of
a natural transformation `SmallObject.ε f : 𝟭 (Arrow C) ⟶ functor f S`.
The main idea in this construction is that for any commutative square
as above, there may not exist a lifting `B i ⟶ X`, but the construction
provides a tautological morphism `B i ⟶ functorObj f πX`
(see `SmallObject.ιFunctorObj_extension`).

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section
universe t w v u

namespace CategoryTheory

open Category Limits HomotopicalAlgebra

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

section

variable {S X : C} (πX : X ⟶ S)

/-- Given a family of morphisms `f i : A i ⟶ B i` and a morphism `πX : X ⟶ S`,
this type parametrizes the commutative squares with a morphism `f i` on the left
and `πX` on the right. -/
/-
**CategoryTheory.SmallObject.FunctorObjIndex** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.SmallObject`。
形式化陈述：FunctorObjIndex where /-- an element in the index type -/ i : I /-- the to
p morphism in the square -/ t : A i ⟶ X /-- the bottom morphism in the square -/
 b : B i ⟶ S w : t ≫ πX = f i ≫ b  attribute [reassoc (attr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of morphisms `f i : A i ⟶ B i` and a morphism `πX : X ⟶ S`,
this type parametrizes the commutative squares with a morphism `f i` on the left
and `πX` on the right.
-/
structure FunctorObjIndex where
  /-- an element in the index type -/
  i : I
  /-- the top morphism in the square -/
  t : A i ⟶ X
  /-- the bottom morphism in the square -/
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

/-- The family of objects `A x.i` parametrized by `x : FunctorObjIndex f πX`. -/
/-
**CategoryTheory.SmallObject.functorObjSrcFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.SmallObject`。
形式化陈述：functorObjSrcFamily (x : FunctorObjIndex f πX) : C
参数：x : FunctorObjIndex f πX。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of objects `A x.i` parametrized by `x : FunctorObjIndex f πX`.
-/
abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

/-- The family of objects `B x.i` parametrized by `x : FunctorObjIndex f πX`. -/
/-
**CategoryTheory.SmallObject.functorObjTgtFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.SmallObject`。
形式化陈述：functorObjTgtFamily (x : FunctorObjIndex f πX) : C
参数：x : FunctorObjIndex f πX。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of objects `B x.i` parametrized by `x : FunctorObjIndex f πX`.
-/
abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

/-- The family of the morphisms `f x.i : A x.i ⟶ B x.i`
parametrized by `x : FunctorObjIndex f πX`. -/
/-
**CategoryTheory.SmallObject.functorObjLeftFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.SmallObject`。
形式化陈述：functorObjLeftFamily (x : FunctorObjIndex f πX) : functorObjSrcFamily f πX
 x ⟶ functorObjTgtFamily f πX x
参数：x : FunctorObjIndex f πX。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of the morphisms `f x.i : A x.i ⟶ B x.i`
parametrized by `x : FunctorObjIndex f πX`.
-/
abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

/-- The top morphism in the pushout square in the definition of `pushoutObj f πX`. -/
/-
**CategoryTheory.SmallObject.functorObjTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.SmallObject`。
形式化陈述：functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top morphism in the pushout square in the definition of `pushoutObj f πX`.
-/
noncomputable abbrev functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

/-- The left morphism in the pushout square in the definition of `pushoutObj f πX`. -/
/-
**CategoryTheory.SmallObject.functorObjLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.SmallObject`。
形式化陈述：functorObjLeft : ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left morphism in the pushout square in the definition of `pushoutObj f πX`.
-/
noncomputable abbrev functorObjLeft :
    ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]

/-- The functor `SmallObject.functor f : Arrow C ⥤ Arrow C` that is part of
the small object argument for a family of morphisms `f`, on an object given
as a morphism `πX : X ⟶ S`. -/
/-
**CategoryTheory.SmallObject.functorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.SmallObject`。
形式化陈述：functorObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SmallObject.functor f : Arrow C ⥤ Arrow C` that is part of
the small object argument for a family of morphisms `f`, on an object given
as a morphism `πX : X ⟶ S`.
-/
noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

/-- The canonical morphism `X ⟶ functorObj f πX`. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.SmallO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `X ⟶ functorObj f πX`.
-/
noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl _ _

/-- The canonical morphism `∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX`. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.SmallO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX`.
-/
noncomputable abbrev ρFunctorObj : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX := pushout.inr _ _

@[reassoc]
/-
**CategoryTheory.SmallObject.functorObj_comm** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.SmallObject`。
形式化陈述：functorObj_comm : functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f
 πX ≫ ρFunctorObj f πX
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX :=
  pushout.condition
/-
**CategoryTheory.SmallObject.functorObj_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.SmallObject`。
形式化陈述：functorObj_isPushout : IsPushout (functorObjTop f πX) (functorObjLeft f πX
) (ιFunctorObj f πX) (ρFunctorObj f πX)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma functorObj_isPushout :
    IsPushout (functorObjTop f πX) (functorObjLeft f πX) (ιFunctorObj f πX) (ρFunctorObj f πX) :=
  IsPushout.of_hasPushout _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.SmallObject.FunctorObjIndex.comm** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.SmallObject.FunctorObjIndex`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {I : Type w} {A B
 : I → C} (f : (i : I) → A i ⟶ B i) {S X : C}   (πX : X ⟶ S)   [inst_1 :     Cat
egoryTheory.Limits.HasColimitsOfShape (CategoryTheory.Discrete (CategoryTheory.S
mallObject.FunctorObjIndex f πX))       C]   [inst_2 :     CategoryTheory.Limits
.HasPushout (CategoryTheory.SmallObject.functorObjTop f πX)       (CategoryTheor
y.SmallObject.functorObjLeft f πX)]   (x : CategoryTheory.SmallObject.FunctorObj
Index f πX),   CategoryTheory.CategoryStruct.comp (f x.i)       (CategoryTheory.
CategoryStruct.comp         (CategoryTheory.Limits.Sigma.ι (CategoryTheory.Small
Object.functorObjTgtFamily f πX) x)         (CategoryTheory.SmallObject.ρFunctor
Obj f πX)) =     CategoryTheory.CategoryStruct.comp x.t (CategoryTheory.SmallObj
ect.ιFunctorObj f πX)
参数：f : (i : I) → A i ⟶ B i；πX : X ⟶ S；CategoryTheory.Discrete (CategoryTheory.Sm
allObject.FunctorObjIndex f πX)；CategoryTheory.SmallObject.functorObjTop f πX；Ca
tegoryTheory.SmallObject.functorObjLeft f πX；x : CategoryTheory.SmallObject.Func
torObjIndex f πX；f x.i；CategoryTheory.CategoryStruct.comp         (CategoryTheor
y.Limits.Sigma.ι (CategoryTheory.SmallObject.functorObjTgtFamily f πX) x)       
  (CategoryTheory.SmallObject.ρFunctorObj f πX)；CategoryTheory.SmallObject.ιFunc
torObj f πX。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用引理 `CategoryTheory.SmallObject.functorObj_comm`：functorObj_comm : functorObj
Top f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX
-/
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

/-- The canonical projection on the base object. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.SmallO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection on the base object.
-/
noncomputable abbrev π'FunctorObj : ∐ functorObjTgtFamily f πX ⟶ S := Sigma.desc (fun x => x.b)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical projection on the base object. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection on the base object.
-/
noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is obtained by
attaching `f`-cells. -/
@[simps]
/-
**CategoryTheory.SmallObject.attachCells** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is obtained by
attaching `f`-cells.
-/
noncomputable def attachCellsιFunctorObj :
    AttachCells.{max v w} f (ιFunctorObj f πX) where
  ι := FunctorObjIndex f πX
  π x := x.i
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := functorObjLeft f πX
  g₁ := functorObjTop f πX
  g₂ := ρFunctorObj f πX
  isPushout := IsPushout.of_hasPushout (functorObjTop f πX) (functorObjLeft f πX)
  cofan₁ := _
  cofan₂ := _

section Small

variable [LocallySmall.{t} C] [Small.{t} I]

/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{t} (FunctorObjIndex f πX) := by
  let φ (x : FunctorObjIndex f πX) :
    Σ (i : Shrink.{t} I),
      Shrink.{t} ((A ((equivShrink _).symm i) ⟶ X) ×
        (B ((equivShrink _).symm i) ⟶ S)) :=
        ⟨equivShrink _ x.i, equivShrink _
          ⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa [φ] using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{t} (attachCellsιFunctorObj f πX).ι := by
  dsimp
  infer_instance

/-- The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is obtained by
attaching `f`-cells, and the index type can be chosen to be in `Type t`
if the category is `t`-locally small and the index type for `f`
is `t`-small. -/
/-
**CategoryTheory.SmallObject.attachCells** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is obtained by
attaching `f`-cells, and the index type can be chosen to be in `Type t`
if the category is `t`-locally small and the index type for `f`
is `t`-small.
-/
noncomputable def attachCellsιFunctorObjOfSmall :
    AttachCells.{t} f (ιFunctorObj f πX) :=
  (attachCellsιFunctorObj f πX).reindex (equivShrink.{t} _).symm

end Small

section

variable {S T X Y : C} {πX : X ⟶ S} {πY : Y ⟶ T} (τ : Arrow.mk πX ⟶ Arrow.mk πY)
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism `∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f πY)`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`. -/
/-
**CategoryTheory.SmallObject.functorMapSrc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：functorMapSrc : ∐ (functorObjSrcFamily f πX) ⟶ ∐ functorObjSrcFamily f πY
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f 
πY)`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`.
-/
noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ functorObjSrcFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f τ =
      Sigma.ι (functorObjSrcFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb', ← reassoc_of% w, ← ht', assoc, this])) := by
  subst hb' ht'
  simp [functorMapSrc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.functorMapSrc_functorObjTop** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.SmallObject`。
形式化陈述：functorMapSrc_functorObjTop : functorMapSrc f τ ≫ functorObjTop f πY = fun
ctorObjTop f πX ≫ τ.left
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SmallObject.ι_functorMapSrc_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {I : Type w} {A B : I → C} (f : (i : I) → A i
 ⟶ B i)   {S T X Y : C} {πX : X ⟶ S} {…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorMapSrc_functorObjTop :
    functorMapSrc f τ ≫ functorObjTop f πY = functorObjTop f πX ≫ τ.left := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f τ i t b w _ rfl]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism `∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`. -/
/-
**CategoryTheory.SmallObject.functorMapTgt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：functorMapTgt : ∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`.
-/
noncomputable def functorMapTgt :
    ∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f τ =
      Sigma.ι (functorObjTgtFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb', ← reassoc_of% w, ← ht', assoc, this])) := by
  subst hb' ht'
  simp [functorMapTgt]
/-
**CategoryTheory.SmallObject.functorMap_comm** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.SmallObject`。
形式化陈述：functorMap_comm : functorObjLeft f πX ≫ functorMapTgt f τ = functorMapSrc 
f τ ≫ functorObjLeft f πY
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用引理 `CategoryTheory.SmallObject.ι_functorMapTgt`：ι_functorMapTgt (i : I) (t :
 A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b) (b' : B i ⟶ T) (hb' : b ≫ τ.right
 = b') (t' : A i ⟶ Y) (ht' : t ≫…
· 使用定理 `CategoryTheory.SmallObject.ι_functorMapSrc_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {I : Type w} {A B : I → C} (f : (i : I) → A i
 ⟶ B i)   {S T X Y : C} {πX : X ⟶ S} {…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f τ =
      functorMapSrc f τ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapTgt f τ i t b w _ rfl, ι_functorMapSrc_assoc f τ i t b w _ rfl]

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]

set_option backward.defeqAttrib.useBackward true in
/-- The functor `SmallObject.functor f S : Arrow S ⥤ Arrow S` that is part of
the small object argument for a family of morphisms `f`, on morphisms. -/
/-
**CategoryTheory.SmallObject.functorMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SmallObject`。
形式化陈述：functorMap : functorObj f πX ⟶ functorObj f πY
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.functorMap_comm`：functorMap_comm : functorObj
Left f πX ≫ functorMapTgt f τ = functorMapSrc f τ ≫ functorObjLeft f πY

--- 原说明 ---
The functor `SmallObject.functor f S : Arrow S ⥤ Arrow S` that is part of
the small object argument for a family of morphisms `f`, on morphisms.
-/
noncomputable def functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ τ.left (functorMapTgt f τ) (functorMapSrc f τ) (by simp)
    (functorMap_comm f τ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.functorMap_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.SmallObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorMap_π : functorMap f τ ≫ πFunctorObj f πY = πFunctorObj f πX ≫ τ.right := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f τ i t b w _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (X) in
@[simp]
/-
**CategoryTheory.SmallObject.functorMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.SmallObject`。
形式化陈述：functorMap_id : functorMap f (𝟙 (Arrow.mk πX)) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SmallObject.functorMap_comm`：functorMap_comm : functorObj
Left f πX ≫ functorMapTgt f τ = functorMapSrc f τ ≫ functorObjLeft f πY
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SmallObject.ι_functorMapTgt_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {I : Type w} {A B : I → C} (f : (i : I) → A i
 ⟶ B i)   {S T X Y : C} {πX : X ⟶ S} {…
-/
lemma functorMap_id : functorMap f (𝟙 (Arrow.mk πX)) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap,
      ι_functorMapTgt_assoc f (𝟙 (Arrow.mk πX)) i t b w b (by simp) t (by simp)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f τ = τ.left ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFunctorObj_extension {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
    (sq : CommSq t (f i) πX b) :
    ∃ (l : B i ⟶ functorObj f πX), f i ≫ l = t ≫ ιFunctorObj f πX ∧
      l ≫ πFunctorObj f πX = b :=
  ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

/-- Variant of `ιFunctorObj_extension` where the diagram involving `functorObj f πX`
is replaced by an isomorphic diagram. -/
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `ιFunctorObj_extension` where the diagram involving `functorObj f πX`
is replaced by an isomorphic diagram.
-/
lemma ιFunctorObj_extension' {X' S' Z' : C} (πX' : X' ⟶ S') (ι' : X' ⟶ Z') (πZ' : Z' ⟶ S')
    (fac' : ι' ≫ πZ' = πX') (eX : X' ≅ X) (eS : S' ≅ S) (eZ : Z' ≅ functorObj f πX)
    (commι : ι' ≫ eZ.hom = eX.hom ≫ ιFunctorObj f πX)
    (commπ : πZ' ≫ eS.hom = eZ.hom ≫ πFunctorObj f πX)
    {i : I} (t : A i ⟶ X') (b : B i ⟶ S') (fac : t ≫ πX' = f i ≫ b) :
    ∃ (l : B i ⟶ Z'), f i ≫ l = t ≫ ι' ∧ l ≫ πZ' = b := by
  obtain ⟨l, hl₁, hl₂⟩ :=
    ιFunctorObj_extension f (πX := πX) (i := i) (t ≫ eX.hom) (b ≫ eS.hom) ⟨by
      rw [assoc, ← ιFunctorObj_πFunctorObj f πX, ← reassoc_of% commι, ← commπ,
        reassoc_of% fac', reassoc_of% fac]⟩
  refine ⟨l ≫ eZ.inv, ?_, ?_⟩
  · rw [reassoc_of% hl₁, ← reassoc_of% commι, eZ.hom_inv_id, comp_id]
  · rw [← cancel_mono eS.hom, assoc, assoc, commπ, eZ.inv_hom_id_assoc, hl₂]

end

variable [HasPushouts C]
  [∀ {X S : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `Arrow C ⥤ Arrow C` that is constructed in order to apply the small
object argument to a family of morphisms `f i : A i ⟶ B i`, see the introduction
of the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` -/
@[simps! obj map]
/-
**CategoryTheory.SmallObject.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
mallObject`。
形式化陈述：functor : Arrow C ⥤ Arrow C where obj π
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Arrow C ⥤ Arrow C` that is constructed in order to apply the small
object argument to a family of morphisms `f i : A i ⟶ B i`, see the introduction
of the file `Mathlib/CategoryTheory/SmallObject/Construction.lean`
-/
noncomputable def functor : Arrow C ⥤ Arrow C where
  obj π := Arrow.mk (πFunctorObj f π.hom)
  map {π₁ π₂} τ := Arrow.homMk (functorMap f τ) τ.right
  map_id g := by
    ext
    · apply functorMap_id
    · dsimp
  map_comp {π₁ π₂ π₃} τ τ' := by
    ext
    · dsimp
      simp only [functorMap, Arrow.comp_left, Arrow.mk_left]
      ext ⟨i, t, b, w⟩
      · simp
      · simp [ι_functorMapTgt_assoc f τ i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f (τ ≫ τ') i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f τ' i (t ≫ τ.left) (b ≫ τ.right)
            (by simp [reassoc_of% w]) (b ≫ τ.right ≫ τ'.right) (by simp)
            (t ≫ (τ ≫ τ').left) (by simp)]
    · dsimp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical natural transformation `𝟭 (Arrow C) ⟶ functor f`. -/
@[simps app]
/-
**CategoryTheory.SmallObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SmallObj
ect`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical natural transformation `𝟭 (Arrow C) ⟶ functor f`.
-/
noncomputable def ε : 𝟭 (Arrow C) ⟶ functor f where
  app π := Arrow.homMk (ιFunctorObj f π.hom) (𝟙 _)

end

end SmallObject

end CategoryTheory

