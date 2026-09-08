/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Cartesian morphisms

This file defines Cartesian resp. strongly Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted to `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCartesian p f φ` expresses that `φ` is a Cartesian morphism lying over `f` with respect to `p` in
the sense of SGA 1 VI 5.1. This means that for any morphism `φ' : a' ⟶ b` lying over `f` there is
a unique morphism `τ : a' ⟶ a` lying over `𝟙 R`, such that `φ' = τ ≫ φ`.

`IsStronglyCartesian p f φ` expresses that `φ` is a strongly Cartesian morphism lying over `f` with
respect to `p`, see <https://stacks.math.columbia.edu/tag/02XK>.

## Implementation

The constructor of `IsStronglyCartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
* [Stacks: Fibred Categories](https://stacks.math.columbia.edu/tag/02XJ)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is Cartesian if for all
morphisms `φ' : a' ⟶ b`, also lying over `f`, there exists a unique morphism `χ : a' ⟶ a` lifting
`𝟙 R` such that `φ' = χ ≫ φ`.

See SGA 1 VI 5.1. -/
/-
**CategoryTheory.Functor.IsCartesian** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         Category
Theory.Functor 𝒳 𝒮 → {R S : 𝒮} → {a b : 𝒳} → (R ⟶ S) → (a ⟶ b) → Prop
参数：R ⟶ S；a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is Cartesian if for 
all
morphisms `φ' : a' ⟶ b`, also lying over `f`, there exists a unique morphism `χ 
: a' ⟶ a` lifting
`𝟙 R` such that `φ' = χ ≫ φ`.

See SGA 1 VI 5.1.
-/
class IsCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'
attribute [instance] IsCartesian.toIsHomLift

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly Cartesian if for
all morphisms `φ' : a' ⟶ b` and all diagrams of the form
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ'` lifts `g ≫ f`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
/-
**CategoryTheory.Functor.IsStronglyCartesian** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         Category
Theory.Functor 𝒳 𝒮 → {R S : 𝒮} → {a b : 𝒳} → (R ⟶ S) → (a ⟶ b) → Prop
参数：R ⟶ S；a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly Cartesia
n if for
all morphisms `φ' : a' ⟶ b` and all diagrams of the form
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ'` lifts `g ≫ f`, there exists a lift `χ` of `g` such that `φ' = χ ≫
 φ`.
-/
class IsStronglyCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'
attribute [instance] IsStronglyCartesian.toIsHomLift

end

namespace IsCartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]

section

variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a' ⟶ b` which also lifts `f`, then `IsCartesian.map f φ φ'` is the morphism `a' ⟶ a` lifting
`𝟙 R` obtained from the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsCartesian.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor.IsCartesian`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         (p : Cat
egoryTheory.Functor 𝒳 𝒮) →           {R S : 𝒮} →             {a b : 𝒳} →        
       (f : R ⟶ S) → (φ : a ⟶ b) → [p.IsCartesian f φ] → {a' : 𝒳} → (φ' : a' ⟶ b
) → [p.IsHomLift f φ'] → a' ⟶ a
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；φ' : a' ⟶ b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.universal_property`：∀ {𝒮 : Type u₁} {
𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and anothe
r morphism
`φ' : a' ⟶ b` which also lifts `f`, then `IsCartesian.map f φ φ'` is the morphis
m `a' ⟶ a` lifting
`𝟙 R` obtained from the universal property of `φ`.
-/
protected noncomputable def map : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'
/-
**CategoryTheory.Functor.IsCartesian.map_isHomLift** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Functor.IsCartesian`。
形式化陈述：map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ')
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Functor.IsCartesian.universal_property`：∀ {𝒮 : Type u₁} {
𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsCartesian.fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor.IsCartesian`。
形式化陈述：fac : IsCartesian.map p f φ φ' ≫ φ = φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.IsCartesian.universal_property`：∀ {𝒮 : Type u₁} {
𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma fac : IsCartesian.map p f φ φ' ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a' ⟶ b` which also lifts `f`. Then any morphism `ψ : a' ⟶ a` lifting `𝟙 R` such that
`g ≫ ψ = φ'` must equal the map induced from the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsCartesian.map_uniq** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor.IsCartesian`。
形式化陈述：map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCart
esian.map p f φ φ'
参数：ψ : a' ⟶ a；𝟙 R；hψ : ψ ≫ φ = φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.IsCartesian.universal_property`：∀ {𝒮 : Type u₁} {
𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and anothe
r morphism
`φ' : a' ⟶ b` which also lifts `f`. Then any morphism `ψ : a' ⟶ a` lifting `𝟙 R`
 such that
`g ≫ ψ = φ'` must equal the map induced from the universal property of `φ`.
-/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = IsCartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two morphisms
`ψ ψ' : a' ⟶ a` such that `ψ ≫ φ = ψ' ≫ φ`. Then we must have `ψ = ψ'`. -/
/-
**CategoryTheory.Functor.IsCartesian.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.IsCartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsCartesian f φ] {a' : 𝒳}   (ψ ψ
' : a' ⟶ a) [p.IsHomLift (CategoryTheory.CategoryStruct.id R) ψ]   [p.IsHomLift 
(CategoryTheory.CategoryStruct.id R) ψ'],   CategoryTheory.CategoryStruct.comp ψ
 φ = CategoryTheory.CategoryStruct.comp ψ' φ → ψ = ψ'
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；ψ ψ' : a' ⟶ a；CategoryTheo
ry.CategoryStruct.id R；CategoryTheory.CategoryStruct.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsCartesian.map_uniq`：map_uniq (ψ : a' ⟶ a) [IsHo
mLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCartesian.map p f φ φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two mo
rphisms
`ψ ψ' : a' ⟶ a` such that `ψ ≫ φ = ψ' ≫ φ`. Then we must have `ψ = ψ'`.
-/
protected lemma ext (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl, map_uniq p f φ (ψ ≫ φ) ψ' h.symm]

@[simp]
/-
**CategoryTheory.Functor.IsCartesian.map_self** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor.IsCartesian`。
形式化陈述：map_self : IsCartesian.map p f φ φ = 𝟙 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCartesian.map_uniq`：map_uniq (ψ : a' ⟶ a) [IsHo
mLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCartesian.map p f φ φ'
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma map_self : IsCartesian.map p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]
/-
**CategoryTheory.Functor.IsCartesian.of_comp_iso** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Functor.IsCartesian`。
形式化陈述：of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] : IsCartesia
n p f (φ ≫ φ'.hom) where universal_property
参数：φ' : b ≅ b'；𝟙 S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsCartesian.fac_assoc`：∀ {𝒮 : Type u₁} {𝒳 : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsCartesian.map_uniq`：map_uniq (ψ : a' ⟶ a) [IsHo
mLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCartesian.map p f φ φ'
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
-/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp only [fac_assoc, assoc, Iso.inv_hom_id, comp_id]⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    rw [Iso.eq_comp_inv]
    simp only [assoc, hτ₂]

/-- The canonical isomorphism between the domains of two Cartesian arrows
lying over the same object. -/
@[simps]
/-
**CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.IsCartesian`。
形式化陈述：domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a w
here hom
参数：φ' : a' ⟶ b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
The canonical isomorphism between the domains of two Cartesian arrows
lying over the same object.
-/
noncomputable def domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a where
  hom := IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp]
/-
**CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsCartesian`。
形式化陈述：domainUniqueUpToIso_inv_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f 
φ'] : IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').hom
参数：φ' : a' ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_hom`：∀ {𝒮 : Type 
u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Category
Theory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
-/
instance domainUniqueUpToIso_inv_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').hom :=
  domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'
/-
**CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsCartesian`。
形式化陈述：domainUniqueUpToIso_hom_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f 
φ'] : IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').inv
参数：φ' : a' ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_inv`：∀ {𝒮 : Type 
u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Category
Theory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
-/
instance domainUniqueUpToIso_hom_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').inv :=
  domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ

/-- Precomposing a Cartesian morphism with an isomorphism lifting the identity is Cartesian. -/
/-
**CategoryTheory.Functor.IsCartesian.of_iso_comp** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Functor.IsCartesian`。
形式化陈述：of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] : IsCartesia
n p f (φ'.hom ≫ φ) where universal_property
参数：φ' : a' ≅ a；𝟙 R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.Functor.IsCartesian.fac`：fac : IsCartesian.map p f φ φ' ≫
 φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用引理 `CategoryTheory.Functor.IsCartesian.map_uniq`：map_uniq (ψ : a' ⟶ a) [IsHo
mLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCartesian.map p f φ φ'

--- 原说明 ---
Precomposing a Cartesian morphism with an isomorphism lifting the identity is Ca
rtesian.
-/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

end IsCartesian

namespace IsStronglyCartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCartesian p f φ]

/-- The universal property of a strongly Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the field
`universal_property'` of `IsStronglyCartesian`. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.universal_property** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' 
= g ≫ f) (φ' : a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, IsHomLift p g χ
 ∧ χ ≫ φ = φ'
参数：g : R' ⟶ R；f' : R' ⟶ S；hf' : f' = g ≫ f；φ' : a' ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property'`：∀ {𝒮 : T
ype u₁} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : Cate
goryTheory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The universal property of a strongly Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the
 field
`universal_property'` of `IsStronglyCartesian`.
-/
lemma universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f
/-
**CategoryTheory.Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian*
* 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：isCartesian_of_isStronglyCartesian : p.IsCartesian f φ where universal_pro
perty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property`：universal
_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f) (φ' : 
a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isCartesian_of_isStronglyCartesian : p.IsCartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

section

variable {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f) (φ' : a' ⟶ b)
  [IsHomLift p f' φ']

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and a morphism `φ' : a' ⟶ b`. Then `map` is the map `a' ⟶ a`
lying over `g` obtained from the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.map** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.IsStronglyCartesian`。
形式化陈述：map : a' ⟶ a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property`：universal
_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f) (φ' : 
a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, I…

--- 原说明 ---
Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and a morphism `φ' : a' ⟶ b`. Then `map` is
 the map `a' ⟶ a`
lying over `g` obtained from the universal property of `φ`.
-/
noncomputable def map : a' ⟶ a :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'
/-
**CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：map_isHomLift : IsHomLift p g (map p f φ hf' φ')
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property`：universal
_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f) (φ' : 
a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, I…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsStronglyCartesian.fac** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor.IsStronglyCartesian`。
形式化陈述：fac : (map p f φ hf' φ') ≫ φ = φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property`：universal
_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f) (φ' : 
a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma fac : (map p f φ hf' φ') ≫ φ = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `φ' : a' ⟶ b`, `ψ : a' ⟶ a` such that
`ψ ≫ φ = φ'`. Then `ψ` is the map induced by the universal property. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.map_uniq** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：map_uniq (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ 
hf' φ'
参数：ψ : a' ⟶ a；hψ : ψ ≫ φ = φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.universal_property`：universal
_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f) (φ' : 
a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, I…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `φ' : a' ⟶ b`, `ψ : a' ⟶ a` s
uch that
`ψ ≫ φ = φ'`. Then `ψ` is the map induced by the universal property.
-/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `ψ ψ' : a' ⟶ a` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.IsStronglyCartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsStronglyCartesian f φ] {R' : 𝒮
}   {a' : 𝒳} (g : R' ⟶ R) {ψ ψ' : a' ⟶ a} [p.IsHomLift g ψ] [p.IsHomLift g ψ'], 
  CategoryTheory.CategoryStruct.comp ψ φ = CategoryTheory.CategoryStruct.comp ψ'
 φ → ψ = ψ'
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；g : R' ⟶ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `ψ ψ' : a' ⟶ a` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`.
-/
protected lemma ext (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
    {ψ ψ' : a' ⟶ a} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl, map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]

@[simp]
/-
**CategoryTheory.Functor.IsStronglyCartesian.map_self** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：map_self : map p f φ (id_comp f).symm φ = 𝟙 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma map_self : map p f φ (id_comp f).symm φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

/-- When its possible to compare the two, the composition of two `IsStronglyCartesian.map` will also
be given by a `IsStronglyCartesian.map`. In other words, given diagrams
```
a''         a'        a --φ--> b
|           |         |        |
v           v         v        v
R'' --g'--> R' --g--> R --f--> S
```
and
```
a' --φ'--> b
|          |
v          v
R' --f'--> S
```
and
```
a'' --φ''--> b
|            |
v            v
R'' --f''--> S
```
such that `φ` and `φ'` are strongly Cartesian morphisms, and such that `f' = g ≫ f` and
`f'' = g' ≫ f'`. Then composing the induced map from `a'' ⟶ a'` with the induced map from
`a' ⟶ a` gives the induced map from `a'' ⟶ a`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsStronglyCartesian.map_comp_map** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：map_comp_map {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : 
R' ⟶ R} {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ''
 : a'' ⟶ b) [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] : map p f' φ' H'
 φ'' ≫ map p f φ H φ' = map p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) 
φ''
参数：H : f' = g ≫ f；H' : f'' = g' ≫ f'；φ' : a' ⟶ b；φ'' : a'' ⟶ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.fac`：fac : (map p f φ hf' φ')
 ≫ φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When its possible to compare the two, the composition of two `IsStronglyCartesia
n.map` will also
be given by a `IsStronglyCartesian.map`. In other words, given diagrams
```
a''         a'        a --φ--> b
|           |         |        |
v           v         v        v
R'' --g'--> R' --g--> R --f--> S
```
and
```
a' --φ'--> b
|          |
v          v
R' --f'--> S
```
and
```
a'' --φ''--> b
|            |
v            v
R'' --f''--> S
```
such that `φ` and `φ'` are strongly Cartesian morphisms, and such that `f' = g ≫
 f` and
`f'' = g' ≫ f'`. Then composing the induced map from `a'' ⟶ a'` with the induced
 map from
`a' ⟶ a` gives the induced map from `a'' ⟶ a`.
-/
lemma map_comp_map {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
    {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ'' : a'' ⟶ b)
    [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f' φ' H' φ'' ≫ map p f φ H φ' =
      map p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/-- Given two strongly Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly Cartesian. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.comp** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] : IsStronglyC
artesian p (f ≫ g) (φ ≫ ψ) where universal_property'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.fac`：fac : (map p f φ hf' φ')
 ≫ φ = φ'
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given two strongly Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly Cartesian.
-/
instance comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
    IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `ψ` are strongly Cartesian, then so is `φ`. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}   [p.Is
StronglyCartesian g ψ]   [p.IsStronglyCartesian (CategoryTheory.CategoryStruct.c
omp f g) (CategoryTheory.CategoryStruct.comp φ ψ)]   [p.IsHomLift f φ], p.IsStro
nglyCartesian f φ
参数：p : CategoryTheory.Functor 𝒳 𝒮；CategoryTheory.CategoryStruct.comp f g；Categor
yTheory.CategoryStruct.comp φ ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.ext`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.fac`：fac : (map p f φ hf' φ')
 ≫ φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `ψ` are strongly Cartesian, then so is `φ`.
-/
protected lemma of_comp [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p f φ] : IsStronglyCartesian p f φ where
  universal_property' := by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    /- We get a morphism `π : a' ⟶ a` such that `π ≫ φ ≫ ψ = τ ≫ ψ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := h ≫ f ≫ g) rfl (τ ≫ ψ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `π ≫ φ = τ` follows from `π ≫ φ ≫ ψ = τ ≫ ψ` and the universal property of
    `ψ`. -/
    · apply IsStronglyCartesian.ext p g ψ (h ≫ f) (by simp)
    -- Finally, the uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

/-
**CategoryTheory.Functor.IsStronglyCartesian.of_iso** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom w
here universal_property'
参数：φ : a ≅ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `CategoryTheory.IsHomLift.isoOfIsoLift_hom_inv_id`：isoOfIsoLift_hom_inv_i
d (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : f ≫ (isoOfIsoLift p f φ).inv =
 𝟙 R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom where
  universal_property' := by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by cat_disch⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)
/-
**CategoryTheory.Functor.IsStronglyCartesian.of_isIso** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f
 φ
参数：φ : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f φ :=
  @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/-- A strongly Cartesian morphism lying over an isomorphism is an isomorphism. -/
/-
**CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f] : Is
Iso φ
参数：φ : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.fac`：fac : (map p f φ hf' φ')
 ≫ φ = φ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.ext`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A strongly Cartesian morphism lying over an isomorphism is an isomorphism.
-/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ` be the morphism induced by applying universal property to `𝟙 b` lying over `f⁻¹ ≫ f`.
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property.
  have inv_hom : φ' ≫ φ = 𝟙 b := fac p (p.map φ) φ _ (𝟙 b)
  refine ⟨?_, inv_hom⟩
  -- We will now show that `φ ≫ φ' = 𝟙 a` by showing that `(φ ≫ φ') ≫ φ = 𝟙 a ≫ φ`.
  have h₁ : IsHomLift p (𝟙 (p.obj a)) (φ ≫ φ') := by
    rw [← IsIso.hom_inv_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCartesian.ext p (p.map φ) φ (𝟙 (p.obj a))
  simp only [assoc, inv_hom, comp_id, id_comp]

end

section

variable {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}

/-- The canonical isomorphism between the domains of two strongly Cartesian morphisms lying over
isomorphic objects. -/
@[simps]
/-
**CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：domainIsoOfBaseIso (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b) [IsStron
glyCartesian p f φ] [IsStronglyCartesian p f' φ'] : a' ≅ a where hom
参数：h : f' = g.hom ≫ f；φ : a ⟶ b；φ' : a' ⟶ b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
The canonical isomorphism between the domains of two strongly Cartesian morphism
s lying over
isomorphic objects.
-/
noncomputable def domainIsoOfBaseIso (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : a' ≅ a where
  hom := map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ
/-
**CategoryTheory.Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：domainUniqueUpToIso_inv_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a
' ⟶ b) [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : IsHomLift p g
.hom (domainIsoOfBaseIso p h φ φ').hom
参数：h : f' = g.hom ≫ f；φ : a ⟶ b；φ' : a' ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom`：∀ {𝒮 
: Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : C
ategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
-/
instance domainUniqueUpToIso_inv_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.hom (domainIsoOfBaseIso p h φ φ').hom :=
  domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'
/-
**CategoryTheory.Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift**
 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsStronglyCartesian`。
形式化陈述：domainUniqueUpToIso_hom_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a
' ⟶ b) [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : IsHomLift p g
.inv (domainIsoOfBaseIso p h φ φ').inv
参数：h : f' = g.hom ≫ f；φ : a ⟶ b；φ' : a' ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso_inv`：∀ {𝒮 
: Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : C
ategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsStronglyCartesian.map.congr_simp`：∀ {𝒮 : Type u
₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryT
heory.Category.{v₂, u₂} 𝒳]   (p p_1 : CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance domainUniqueUpToIso_hom_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.inv (domainIsoOfBaseIso p h φ φ').inv := by
  have : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

end

end IsStronglyCartesian

end CategoryTheory.Functor

