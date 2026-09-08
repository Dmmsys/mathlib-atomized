/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Localization.BousfieldTransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `W.isLocal.isLocal` and
is an isomorphism iff `Z` belongs to `W.isLocal` (see the lemma `isIso_toSucc_iff`).
The morphism `toSucc W Z : Z ⟶ succ W Z` is defined as a composition
of two morphisms that are roughly described as follows:
* `toStep W Z : Z ⟶ step W Z`: for any morphism `f : X ⟶ Y` satisfying `W`
  and any morphism `X ⟶ Z`, we "attach" a morphism `Y ⟶ step W Z` (using
  coproducts and a pushout in essentially the same way as it is done in
  the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` for the small object
  argument);
* `fromStep W Z : step W Z ⟶ succ W Z`: this morphism coequalizes all pairs
  of morphisms `g₁ g₂ : Y ⟶ step W Z` such that there is a `f : X ⟶ Y`
  satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.

The morphism `toSucc W Z : Z ⟶ succ W Z` is a variant of the (wrong) definition
p. 32 in the book by Adámek and Rosický. In this book, a slightly different object
than `succ W Z` is defined directly as a colimit of an intricate diagram, but
contrary to what is stated on p. 33, it does not satisfy `isIso_toSucc_iff`.
The author of this file was unable to understand the attempt of the authors
to fix this mistake in the errata to this book. This led to the definition
in two steps outlined above.

## Main results

The morphisms described above `toSucc W Z : Z ⟶ succ W Z` for all `Z : C` allow to
define `succStruct W Z₀ : SuccStruct C` for any `Z₀ : C`. By applying
a transfinite iteration to this `SuccStruct`, we obtain the following results
under the assumption that `W : MorphismProperty C` is a `w`-small property
of morphisms in a locally `κ`-presentable category `C` (with `κ : Cardinal.{w}`
a regular cardinal) such that the domains and codomains of the morphisms
satisfying `W` are `κ`-presentable:
* `MorphismProperty.isRightAdjoint_ι_isLocal`: existence of the left adjoint
  of the inclusion `W.isLocal ⥤ C`;
* `MorphismProperty.isLocallyPresentable_isLocal`: the full subcategory
  `W.isLocal` is locally presentable.

This is essentially the implication (i) → (ii) in Theorem 1.39 (and the corollary 1.40)
in the book by Adámek and Rosický (note that according to the
errata to this book, the implication (ii) → (i) is wrong when `κ = ℵ₀`).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Limits Localization Opposite

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.isClosedUnderColimitsOfShape_isLocal** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheo
ry.MorphismProperty C) (J : Type u')   [inst_1 : CategoryTheory.Category.{v', u'
} J] [CategoryTheory.EssentiallySmall.{w, v', u'} J] (κ : Cardinal.{w})   [inst_
3 : Fact κ.IsRegular] [CategoryTheory.IsCardinalFiltered J κ],   (∀ ⦃X Y : C⦄ (f
 : X ⟶ Y), W f → CategoryTheory.IsCardinalPresentable X κ ∧ CategoryTheory.IsCar
dinalPresentable Y κ) →     W.isLocal.IsClosedUnderColimitsOfShape J
参数：W : CategoryTheory.MorphismProperty C；J : Type u'；κ : Cardinal.{w}；∀ ⦃X Y : C
⦄ (f : X ⟶ Y), W f → CategoryTheory.IsCardinalPresentable X κ ∧ CategoryTheory.I
sCardinalPresentable Y κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [ins
t_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Limits.ColimitPresentation.w`：w (pres : ColimitPresentati
on J X) {i j : J} (f : i ⟶ j) : pres.diag.map f ≫ pres.ι.app j = pres.ι.app i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MorphismProperty.isClosedUnderColimitsOfShape_isLocal
    (J : Type u') [Category.{v'} J] [EssentiallySmall.{w} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun Z ⟨p⟩ X Y f hf ↦ by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u, ← p.w v, reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩
/-
**CategoryTheory.MorphismProperty.isCardinalAccessible_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MorphismProperty.isCardinalAccessible_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits C κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.ι.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    infer_instance

namespace OrthogonalReflection

variable (Z : C)

/-- Given `W : MorphismProperty C` and `Z : C`, this is the index type
parametrising the data of a morphism `f : X ⟶ Y` satisfying `W`
and a morphism `X ⟶ Z`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C` and `Z : C`, this is the index type
parametrising the data of a morphism `f : X ⟶ Y` satisfying `W`
and a morphism `X ⟶ Z`.
-/
def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z
/-
**CategoryTheory.OrthogonalReflection.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C] :
    Small.{w} (D₁ (W := W) (Z := Z)) := by
  dsimp [D₁]
  infer_instance
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₁.hasCoproductsOfShape [MorphismProperty.IsSmall.{w} W]
    [LocallySmall.{w} C] [HasCoproducts.{w} C] :
    HasCoproductsOfShape (D₁ (W := W) (Z := Z)) C :=
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `X`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `X`.
-/
def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `Y`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `Y`.
-/
def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

section

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

/-- Considering all diagrams consisting of a morphism `f : X ⟶ Y` satisfying `W`
and of a morphism `d : X ⟶ Z`, this is the morphism from the coproduct of
all these `X` objects to `Z` given by these morphisms `d`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Considering all diagrams consisting of a morphism `f : X ⟶ Y` satisfying `W`
and of a morphism `d : X ⟶ Z`, this is the morphism from the coproduct of
all these `X` objects to `Z` given by these morphisms `d`.
-/
noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d ↦ d.2)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₁`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand in `∐ obj₁`.
-/
noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ obj₁ (W := W) (Z := Z) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g :=
  Sigma.ι_desc _ _

variable [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]

/-- The coproduct of all the morphisms `f` indexed by all diagrams
consisting of a morphism `f : X ⟶ Y` satisfying `W` and of a morphism `d : X ⟶ Z`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct of all the morphisms `f` indexed by all diagrams
consisting of a morphism `f : X ⟶ Y` satisfying `W` and of a morphism `d : X ⟶ Z
`.
-/
noncomputable abbrev D₁.t : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Limits.Sigma.map (fun d ↦ d.1.1.hom)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₂`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand in `∐ obj₂`.
-/
noncomputable abbrev D₁.ιRight {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    Y ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

set_option backward.isDefEq.respectTransparency false in -- Needed below
variable {W Z} in
@[reassoc]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₁.ι_comp_t (d : D₁ W Z) :
    Sigma.ι _ d ≫ D₁.t W Z = d.1.1.hom ≫ Sigma.ι obj₂ d := by
  apply ι_colimMap

variable {W Z} in
@[reassoc]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

/-- The intermediate object in the definition of the morphism `toSucc W Z : Z ⟶ succ W Z`.
It is the pushout of the following square:
```lean
∐ D₁.obj₁ ⟶ ∐ D₁.obj₂
   |           |
   v           v
   Z      ⟶   step W Z
```
where the coproduct is taken over all the diagram consisting of a morphism `f : X ⟶ Y`
satisfying `W` and a morphism `X ⟶ Z`. The top map is the coproduct of all of these `f`.
-/
/-
**CategoryTheory.OrthogonalReflection.step** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.OrthogonalReflection`。
形式化陈述：step
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate object in the definition of the morphism `toSucc W Z : Z ⟶ succ
 W Z`.
It is the pushout of the following square:
```lean
∐ D₁.obj₁ ⟶ ∐ D₁.obj₂
   |           |
   v           v
   Z      ⟶   step W Z
```
where the coproduct is taken over all the diagram consisting of a morphism `f : 
X ⟶ Y`
satisfying `W` and a morphism `X ⟶ Z`. The top map is the coproduct of all of th
ese `f`.
-/
noncomputable abbrev step := pushout (D₁.t W Z) (D₁.l W Z)

/-- The canonical map from `Z` to the pushout of `D₁.t W Z` and `D₁.l W Z`. -/
/-
**CategoryTheory.OrthogonalReflection.toStep** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.OrthogonalReflection`。
形式化陈述：toStep : Z ⟶ step W Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `Z` to the pushout of `D₁.t W Z` and `D₁.l W Z`.
-/
noncomputable abbrev toStep : Z ⟶ step W Z := pushout.inr _ _

/-- The index type parametrising the data of two morphisms `g₁ g₂ : Y ⟶ step W Z`, and
a map `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index type parametrising the data of two morphisms `g₁ g₂ : Y ⟶ step W Z`, a
nd
a map `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.
-/
def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

/-- The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W 
Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.
-/
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

section

variable [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]

/-
**CategoryTheory.OrthogonalReflection.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{w} (D₂ (W := W) (Z := Z)) := by
  dsimp [D₂]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.OrthogonalReflection.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{w} (D₂.multispanShape W Z).L := by dsimp; infer_instance

attribute [local instance] essentiallySmall_of_small_of_locallySmall in
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₂.hasColimitsOfShape [HasColimitsOfSize.{w, w} C] :
    HasColimitsOfShape (WalkingMultispan (multispanShape W Z)) C :=
  hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).symm

end

/-- The diagram of the multicoequalizer of all pair of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram of the multicoequalizer of all pair of morphisms `g₁ g₂ : Y ⟶ step W
 Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.
-/
noncomputable def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The object `succ W Z` is the multicoequalizer of all pairs of morphisms
`g₁ g₂ : Y ⟶ step W Z` with a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
/-
**CategoryTheory.OrthogonalReflection.succ** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.OrthogonalReflection`。
形式化陈述：succ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object `succ W Z` is the multicoequalizer of all pairs of morphisms
`g₁ g₂ : Y ⟶ step W Z` with a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫
 g₂`.
-/
noncomputable abbrev succ := multicoequalizer (D₂.multispanIndex W Z)

/-- The projection from `Z` to the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
/-
**CategoryTheory.OrthogonalReflection.fromStep** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.OrthogonalReflection`。
形式化陈述：fromStep : step W Z ⟶ succ W Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from `Z` to the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ st
ep W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.
-/
noncomputable abbrev fromStep : step W Z ⟶ succ W Z :=
  Multicoequalizer.π (D₂.multispanIndex W Z) .unit

variable {W Z} in
@[reassoc]
/-
**CategoryTheory.OrthogonalReflection.D** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma D₂.condition {X Y : C} (f : X ⟶ Y) (hf : W f)
    {g₁ g₂ : Y ⟶ step W Z} (h : f ≫ g₁ = f ≫ g₂) :
      g₁ ≫ fromStep W Z = g₂ ≫ fromStep W Z :=
  Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

/-- The morphism `Z ⟶ succ W Z`. -/
/-
**CategoryTheory.OrthogonalReflection.toSucc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.OrthogonalReflection`。
形式化陈述：toSucc : Z ⟶ succ W Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `Z ⟶ succ W Z`.
-/
noncomputable abbrev toSucc : Z ⟶ succ W Z := toStep W Z ≫ fromStep W Z

variable {W Z} in
/-
**CategoryTheory.OrthogonalReflection.toSucc_injectivity** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g₁ g₂ : Y ⟶ Z) (hg : 
f ≫ g₁ = f ≫ g₂) : g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z
参数：f : X ⟶ Y；hf : W f；g₁ g₂ : Y ⟶ Z；hg : f ≫ g₁ = f ≫ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.OrthogonalReflection.D₂.condition`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {Z : 
C}   [inst_1 : CategoryTheory.Limits.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f)
    (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z := by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

set_option backward.isDefEq.respectTransparency false in
variable {W Z} in
/-
**CategoryTheory.OrthogonalReflection.toSucc_surjectivity** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) : exists 
(g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z
参数：f : X ⟶ Y；hf : W f；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    ∃ (g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z :=
  ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OrthogonalReflection.isLocal_isLocal_toSucc** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：isLocal_isLocal_toSucc : W.isLocal.isLocal (toSucc W Z)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isLocal_isLocal_toSucc :
    W.isLocal.isLocal (toSucc W Z) := by
  refine fun T hT ↦ ⟨fun φ₁ φ₂ h ↦ ?_, fun g ↦ ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) ↦ (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ ↦ pushout.desc (Sigma.desc f) g)
      (fun d ↦ (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OrthogonalReflection.isIso_toSucc_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.OrthogonalReflection`。
形式化陈述：isIso_toSucc_iff : IsIso (toSucc W Z) ↔ W.isLocal Z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.OrthogonalReflection.D₂.condition`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {Z : 
C}   [inst_1 : CategoryTheory.Limits.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.OrthogonalReflection.isLocal_isLocal_toSucc`：isLocal_isLo
cal_toSucc : W.isLocal.isLocal (toSucc W Z)
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.OrthogonalReflection.D₁.ι_comp_t_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} 
{Z : C}   [inst_1 : CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
lemma isIso_toSucc_iff :
    IsIso (toSucc W Z) ↔ W.isLocal Z := by
  refine ⟨fun _ X Y f hf ↦ ?_, fun hZ ↦ ?_⟩
  · refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (isLocal_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc, Category.assoc, Category.assoc,
        ← D₁.ι_comp_t_assoc, pushout.condition_assoc, reassoc_of% hf,
        ← D₁.ι_comp_t_assoc, pushout.condition]
    · simp [reassoc_of% hf]

end

open SmallObject

variable [HasPushouts C]
  [∀ Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [∀ Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [∀ Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The successor structure of the orthogonal-reflection construction. -/
/-
**CategoryTheory.OrthogonalReflection.succStruct** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.OrthogonalReflection`。
形式化陈述：succStruct (Z₀ : C) : SuccStruct C where X₀
参数：Z₀ : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The successor structure of the orthogonal-reflection construction.
-/
noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

variable (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
  [HasIterationOfShape κ.ord.ToType C]

/-- The transfinite iteration of `succStruct W Z` to the power `κ.ord.ToType`. -/
/-
**CategoryTheory.OrthogonalReflection.reflectionObj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.OrthogonalReflection`。
形式化陈述：reflectionObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfinite iteration of `succStruct W Z` to the power `κ.ord.ToType`.
-/
noncomputable def reflectionObj : C := (succStruct W Z).iteration κ.ord.ToType

/-- The map which shall exhibit `reflectionObj W Z κ` as the image of `Z` by
the left adjoint of the inclusion of `W.isLocal`, see `corepresentableBy`. -/
/-
**CategoryTheory.OrthogonalReflection.reflection** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.OrthogonalReflection`。
形式化陈述：reflection : Z ⟶ reflectionObj W Z κ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map which shall exhibit `reflectionObj W Z κ` as the image of `Z` by
the left adjoint of the inclusion of `W.isLocal`, see `corepresentableBy`.
-/
noncomputable def reflection : Z ⟶ reflectionObj W Z κ :=
  (succStruct W Z).ιIteration κ.ord.ToType

/-- The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` is a transfinite
compositions of morphisms in `LeftBousfield.W W.isLocal`. -/
/-
**CategoryTheory.OrthogonalReflection.transfiniteCompositionOfShapeReflection** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：transfiniteCompositionOfShapeReflection : W.isLocal.isLocal.TransfiniteCom
positionOfShape κ.ord.ToType (reflection W Z κ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` is a transfinite
compositions of morphisms in `LeftBousfield.W W.isLocal`.
-/
noncomputable def transfiniteCompositionOfShapeReflection :
    W.isLocal.isLocal.TransfiniteCompositionOfShape κ.ord.ToType
      (reflection W Z κ) :=
  ((succStruct W Z).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE (by
    rintro Z₀ _ _ ⟨_⟩
    exact isLocal_isLocal_toSucc W Z₀)

/-- The functor `κ.ord.ToType ⥤ C` that is the diagram of the
transfinite composition `transfiniteCompositionOfShapeReflection`. -/
/-
**CategoryTheory.OrthogonalReflection.iteration** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.OrthogonalReflection`。
形式化陈述：iteration : κ.ord.ToType ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `κ.ord.ToType ⥤ C` that is the diagram of the
transfinite composition `transfiniteCompositionOfShapeReflection`.
-/
noncomputable abbrev iteration : κ.ord.ToType ⥤ C :=
  (transfiniteCompositionOfShapeReflection W Z κ).F

section

variable [Fact κ.IsRegular]

/-- `(iteration W Z κ).obj (Order.succ j)` identifies to the image of
`(iteration W Z κ).obj j` by `succ`. -/
/-
**CategoryTheory.OrthogonalReflection.iterationObjSuccIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：iterationObjSuccIso (j : κ.ord.ToType) : (iteration W Z κ).obj (Order.succ
 j) ≅ succ W ((iteration W Z κ).obj j)
参数：j : κ.ord.ToType。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(iteration W Z κ).obj (Order.succ j)` identifies to the image of
`(iteration W Z κ).obj j` by `succ`.
-/
noncomputable def iterationObjSuccIso (j : κ.ord.ToType) :
  (iteration W Z κ).obj (Order.succ j) ≅ succ W ((iteration W Z κ).obj j) :=
    (succStruct W Z).iterationFunctorObjSuccIso j (by
      have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
      exact not_isMax j)

@[reassoc]
/-
**CategoryTheory.OrthogonalReflection.iteration_map_succ** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：iteration_map_succ (j : κ.ord.ToType) : (iteration W Z κ).map (homOfLE (Or
der.le_succ j)) = toSucc W _ ≫ (iterationObjSuccIso W Z κ j).inv
参数：j : κ.ord.ToType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallObject.SuccStruct.iterationFunctor_map_succ`：iterati
onFunctor_map_succ (j : J) (hj : ¬ IsMax j) : (Φ.iterationFunctor J).map (homOfL
E (Order.le_succ j)) = Φ.toSucc _ ≫ (Φ.iterationFunct…
-/
lemma iteration_map_succ (j : κ.ord.ToType) :
    (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      toSucc W _ ≫ (iterationObjSuccIso W Z κ j).inv :=
  (succStruct W Z).iterationFunctor_map_succ _ _

variable {κ W Z} in
/-
**CategoryTheory.OrthogonalReflection.iteration_map_succ_injectivity** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：iteration_map_succ_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord
.ToType} (g₁ g₂ : Y ⟶ (iteration W Z κ).obj j) (hg : f ≫ g₁ = f ≫ g₂) : g₁ ≫ (it
eration W Z κ).map (homOfLE (Order.le_succ j)) = g₂ ≫ (iteration W Z κ).map (hom
OfLE (Order.le_succ j))
参数：f : X ⟶ Y；hf : W f；g₁ g₂ : Y ⟶ (iteration W Z κ).obj j；hg : f ≫ g₁ = f ≫ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.OrthogonalReflection.iteration_map_succ`：iteration_map_su
cc (j : κ.ord.ToType) : (iteration W Z κ).map (homOfLE (Order.le_succ j)) = toSu
cc W _ ≫ (iterationObjSuccIso W Z κ j).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.OrthogonalReflection.toSucc_injectivity`：toSucc_injectivi
ty {X Y : C} (f : X ⟶ Y) (hf : W f) (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) : g₁ 
≫ toSucc W Z = g₂ ≫ toSucc W Z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteration_map_succ_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g₁ g₂ : Y ⟶ (iteration W Z κ).obj j) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      g₂ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp [iteration_map_succ, reassoc_of% (toSucc_injectivity f hf _ _ hg)]

variable {κ W Z} in
/-
**CategoryTheory.OrthogonalReflection.iteration_map_succ_surjectivity** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：iteration_map_succ_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.or
d.ToType} (g : X ⟶ (iteration W Z κ).obj j) : exists (g' : Y ⟶ (iteration W Z κ)
.obj (Order.succ j)), f ≫ g' = g ≫ (iteration W Z κ).map (homOfLE (Order.le_succ
 j))
参数：f : X ⟶ Y；hf : W f；g : X ⟶ (iteration W Z κ).obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.OrthogonalReflection.iteration_map_succ`：iteration_map_su
cc (j : κ.ord.ToType) : (iteration W Z κ).map (homOfLE (Order.le_succ j)) = toSu
cc W _ ≫ (iterationObjSuccIso W Z κ j).inv
· 使用引理 `CategoryTheory.OrthogonalReflection.toSucc_surjectivity`：toSucc_surjecti
vity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) : exists (g' : Y ⟶ succ W Z), 
f ≫ g' = g ≫ toSucc W Z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteration_map_succ_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g : X ⟶ (iteration W Z κ).obj j) :
    ∃ (g' : Y ⟶ (iteration W Z κ).obj (Order.succ j)),
      f ≫ g' = g ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp only [iteration_map_succ]
  obtain ⟨g', hg'⟩ := toSucc_surjectivity f hf g
  exact ⟨g' ≫ (iterationObjSuccIso W Z κ j).inv, by simp [reassoc_of% hg']⟩

end

/-
**CategoryTheory.OrthogonalReflection.isLocal_isLocal_reflection** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：isLocal_isLocal_reflection : W.isLocal.isLocal (reflection W Z κ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderTransfiniteCompositionOfS
hapeIsLocal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : Categ
oryTheory.ObjectProperty C) (J : Type w)   [inst_1 : LinearOrder J] [inst…
-/
lemma isLocal_isLocal_reflection :
     W.isLocal.isLocal (reflection W Z κ) :=
  W.isLocal.isLocal.transfiniteCompositionsOfShape_le κ.ord.ToType _
    ⟨transfiniteCompositionOfShapeReflection W Z κ⟩

variable {W} {κ} [Fact κ.IsRegular]
  (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)

include hW

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OrthogonalReflection.isLocal_reflectionObj** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：isLocal_reflectionObj : W.isLocal (reflectionObj W Z κ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_thin`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [Quiver.IsThin C], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.instIsCardinalFilteredToTypeOrd`：∀ (κ : Cardinal.{w}) [hκ
 : Fact κ.IsRegular], CategoryTheory.IsCardinalFiltered κ.ord.ToType κ
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CategoryTheory.IsCardinalPresentable.exists_eq_of_isColimit'`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (κ : Cardinal.{w}) [in
st_1 : Fact κ.IsRegular]   {J : Type u_1} [inst_2 …
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `CategoryTheory.OrthogonalReflection.iteration_map_succ_injectivity`：iter
ation_map_succ_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType} (
g₁ g₂ : Y ⟶ (iteration W Z κ).obj j) (hg : f ≫ g₁ = f ≫ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.OrthogonalReflection.iteration_map_succ_surjectivity`：ite
ration_map_succ_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
 (g : X ⟶ (iteration W Z κ).obj j) : exists (g' : Y ⟶ (it…
-/
lemma isLocal_reflectionObj :
    W.isLocal (reflectionObj W Z κ) := by
  let H := transfiniteCompositionOfShapeReflection W Z κ
  intro X Y f hf
  obtain ⟨_, _⟩ := hW f hf
  refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨j, g₁, g₂, rfl, rfl⟩ :
      ∃ (j : κ.ord.ToType) (g₁' g₂' : Y ⟶ H.F.obj j), g₁' ≫ H.incl.app j = g₁ ∧
        g₂' ≫ H.incl.app j = g₂ := by
      obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₂
      exact ⟨max j₁ j₂, g₁ ≫ H.F.map (homOfLE (le_max_left _ _)),
        g₂ ≫ H.F.map (homOfLE (le_max_right _ _)), by simp⟩
    dsimp at h
    obtain ⟨k, u, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ H.isColimit
      (f ≫ g₁) (f ≫ g₂) (by simpa)
    have hg := iteration_map_succ_injectivity f hf
      (g₁ ≫ H.F.map u) (g₂ ≫ H.F.map u) (by simpa using hk)
    simp only [homOfLE_leOfHom, Category.assoc] at hg
    have := H.incl.naturality (u ≫ homOfLE (Order.le_succ k))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    simp only [← this, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hg]
  · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g
    obtain ⟨g', hg'⟩ := iteration_map_succ_surjectivity f hf g
    exact ⟨g' ≫ H.incl.app (Order.succ j), by simp [reassoc_of% hg']⟩

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` exhibits `reflectionObj W Z κ`
as the image of `Z` by the left adjoint of the inclusion `W.isLocal.ι`. -/
/-
**CategoryTheory.OrthogonalReflection.corepresentableBy** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.OrthogonalReflection`。
形式化陈述：corepresentableBy : (W.isLocal.ι ⋙ coyoneda.obj (op Z)).CorepresentableBy 
⟨_, isLocal_reflectionObj Z hW⟩ where homEquiv {A}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OrthogonalReflection.isLocal_reflectionObj`：isLocal_refle
ctionObj : W.isLocal (reflectionObj W Z κ)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` exhibits `reflectionOb
j W Z κ`
as the image of `Z` by the left adjoint of the inclusion `W.isLocal.ι`.
-/
noncomputable def corepresentableBy :
  (W.isLocal.ι ⋙ coyoneda.obj (op Z)).CorepresentableBy
    ⟨_, isLocal_reflectionObj Z hW⟩ where
  homEquiv {A} :=
    (ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Equiv.ofBijective _ (isLocal_isLocal_reflection W Z κ _ A.2))

variable (W κ)
/-
**CategoryTheory.OrthogonalReflection.isRightAdjoint_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OrthogonalReflection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRightAdjoint_ι :
    W.isLocal.ι.IsRightAdjoint := by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  ext Z
  simpa using! (corepresentableBy Z hW).isCorepresentable

end OrthogonalReflection

namespace MorphismProperty

open OrthogonalReflection in
/-
**CategoryTheory.MorphismProperty.isRightAdjoint_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRightAdjoint_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)
    [HasColimitsOfSize.{w, w} C] :
    W.isLocal.ι.IsRightAdjoint := by
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero Fact.out
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have := D₁.hasCoproductsOfShape.{w} W
  have := D₂.hasColimitsOfShape.{w} W
  exact isRightAdjoint_ι W κ hW
/-
**CategoryTheory.MorphismProperty.isLocallyPresentable_isLocal** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isLocallyPresentable_isLocal (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCard
inalLocallyPresentable C κ] [MorphismProperty.IsSmall.{w} W] (hW : forall ⦃X Y :
 C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
 IsCardinalLocallyPresentable W.isLocal.FullSubcategory κ
参数：κ : Cardinal.{w}；hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresenta
ble X κ ∧ IsCardinalPresentable Y κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.isRightAdjoint_ι_isLocal`：isRightAdjoint
_ι_isLocal (κ : Cardinal.{w}) [Fact κ.IsRegular] [MorphismProperty.IsSmall.{w} W
] [LocallySmall.{w} C] (hW : forall ⦃X Y : C⦄ …
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall`：∀ {C : Type 
u} {hC : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {hκ : Fact κ.IsReg
ular}   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredGenerat
or`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} 
{inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用定理 `CategoryTheory.instIsCardinalAccessibleCategoryOfIsCardinalLocallyPresen
table`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w
}) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.IsCardinalLocallyP…
· 使用定理 `CategoryTheory.IsCardinalLocallyPresentable.toHasColimitsOfSize`：∀ {C : 
Type u} {inst : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {inst_1 : F
act κ.IsRegular}   [self : CategoryTheory.IsCardinalL…
· 使用定理 `CategoryTheory.MorphismProperty.isCardinalAccessible_ι_isLocal`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismPro
perty C) (κ : Cardinal.{w})   [inst_1 : Fact κ.IsReg…
· 使用定理 `CategoryTheory.IsCardinalAccessibleCategory.toHasCardinalFilteredColimit
s`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {κ : Cardinal.{w}} {
inst_1 : Fact κ.IsRegular}   [self : CategoryTheory.IsCardinalA…
· 使用引理 `CategoryTheory.Adjunction.isCardinalLocallyPresentable`：isCardinalLocall
yPresentable [IsCardinalLocallyPresentable C κ] [G.IsCardinalAccessible κ] [G.Fu
ll] [G.Faithful] : IsCardinalLocallyPresenta…
-/
lemma isLocallyPresentable_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ]
    [MorphismProperty.IsSmall.{w} W]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
  IsCardinalLocallyPresentable W.isLocal.FullSubcategory κ := by
    have := isRightAdjoint_ι_isLocal W κ hW
    have := MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW
    exact (Adjunction.ofIsRightAdjoint W.isLocal.ι).isCardinalLocallyPresentable κ

end MorphismProperty

end CategoryTheory

