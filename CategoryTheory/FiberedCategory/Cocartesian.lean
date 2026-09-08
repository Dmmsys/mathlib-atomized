/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Co-Cartesian morphisms

This file defines co-Cartesian resp. strongly co-Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted from `Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCocartesian p f φ` expresses that `φ` is a co-Cartesian morphism lying over `f : R ⟶ S` with
respect to `p`. This means that for any morphism `φ' : a ⟶ b'` lying over `f` there
is a unique morphism `τ : b ⟶ b'` lying over `𝟙 S`, such that `φ' = φ ≫ τ`.

`IsStronglyCocartesian p f φ` expresses that `φ` is a strongly co-Cartesian morphism lying over `f`
with respect to `p`.

## Implementation

The constructor of `IsStronglyCocartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCocartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is co-Cartesian if for all
morphisms `φ' : a ⟶ b'`, also lying over `f`, there exists a unique morphism `χ : b ⟶ b'` lifting
`𝟙 S` such that `φ' = φ ≫ χ`. -/
/-
**CategoryTheory.Functor.IsCocartesian** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         Category
Theory.Functor 𝒳 𝒮 → {R S : 𝒮} → {a b : 𝒳} → (R ⟶ S) → (a ⟶ b) → Prop
参数：R ⟶ S；a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is co-Cartesian if f
or all
morphisms `φ' : a ⟶ b'`, also lying over `f`, there exists a unique morphism `χ 
: b ⟶ b'` lifting
`𝟙 S` such that `φ' = φ ≫ χ`.
-/
class IsCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ'] :
      ∃! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'

attribute [instance] IsCocartesian.toIsHomLift
/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly co-Cartesian if for
all morphisms `φ' : a ⟶ b'` and all diagrams of the form
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ'` lifts `f ≫ g`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
/-
**CategoryTheory.Functor.IsStronglyCocartesian** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         Category
Theory.Functor 𝒳 𝒮 → {R S : 𝒮} → {a b : 𝒳} → (R ⟶ S) → (a ⟶ b) → Prop
参数：R ⟶ S；a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly co-Carte
sian if for
all morphisms `φ' : a ⟶ b'` and all diagrams of the form
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ'` lifts `f ≫ g`, there exists a lift `χ` of `g` such that `φ' = χ ≫
 φ`.
-/
class IsStronglyCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ'] :
      ∃! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'
attribute [instance] IsStronglyCocartesian.toIsHomLift

end

namespace IsCocartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCocartesian p f φ]

section

variable {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ']

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a ⟶ b'` which also lifts `f`, then `IsCocartesian.map f φ φ'` is the morphism `b ⟶ b'` lying
over `𝟙 S` obtained from the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsCocartesian.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.IsCocartesian`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] →         (p : Cat
egoryTheory.Functor 𝒳 𝒮) →           {R S : 𝒮} →             {a b : 𝒳} →        
       (f : R ⟶ S) → (φ : a ⟶ b) → [p.IsCocartesian f φ] → {b' : 𝒳} → (φ' : a ⟶ 
b') → [p.IsHomLift f φ'] → b ⟶ b'
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；φ' : a ⟶ b'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.universal_property`：∀ {𝒮 : Type u₁}
 {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryThe
ory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and ano
ther morphism
`φ' : a ⟶ b'` which also lifts `f`, then `IsCocartesian.map f φ φ'` is the morph
ism `b ⟶ b'` lying
over `𝟙 S` obtained from the universal property of `φ`.
-/
protected noncomputable def map : b ⟶ b' :=
  Classical.choose <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ'
/-
**CategoryTheory.Functor.IsCocartesian.map_isHomLift** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Functor.IsCocartesian`。
形式化陈述：map_isHomLift : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ')
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Functor.IsCocartesian.universal_property`：∀ {𝒮 : Type u₁}
 {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryThe
ory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance map_isHomLift : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsCocartesian.fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor.IsCocartesian`。
形式化陈述：fac : φ ≫ IsCocartesian.map p f φ φ' = φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.IsCocartesian.universal_property`：∀ {𝒮 : Type u₁}
 {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryThe
ory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma fac : φ ≫ IsCocartesian.map p f φ φ' = φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a ⟶ b'` which also lifts `f`. Then any morphism `ψ : b ⟶ b'` lifting `𝟙 S` such that
`g ≫ ψ = φ'` must equal the map induced by the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsCocartesian.map_uniq** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.IsCocartesian`。
形式化陈述：map_uniq (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') : ψ = IsCoca
rtesian.map p f φ φ'
参数：ψ : b ⟶ b'；𝟙 S；hψ : φ ≫ ψ = φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Functor.IsCocartesian.universal_property`：∀ {𝒮 : Type u₁}
 {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryThe
ory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and ano
ther morphism
`φ' : a ⟶ b'` which also lifts `f`. Then any morphism `ψ : b ⟶ b'` lifting `𝟙 S`
 such that
`g ≫ ψ = φ'` must equal the map induced by the universal property of `φ`.
-/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') :
    ψ = IsCocartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two morphisms
`ψ ψ' : b ⟶ b'` lifting `𝟙 S` such that `φ ≫ ψ = φ ≫ ψ'`. Then we must have `ψ = ψ'`. -/
/-
**CategoryTheory.Functor.IsCocartesian.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsCocartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsCocartesian f φ] {b' : 𝒳}   (ψ
 ψ' : b ⟶ b') [p.IsHomLift (CategoryTheory.CategoryStruct.id S) ψ]   [p.IsHomLif
t (CategoryTheory.CategoryStruct.id S) ψ'],   CategoryTheory.CategoryStruct.comp
 φ ψ = CategoryTheory.CategoryStruct.comp φ ψ' → ψ = ψ'
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；ψ ψ' : b ⟶ b'；CategoryTheo
ry.CategoryStruct.id S；CategoryTheory.CategoryStruct.id S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsCocartesian.map_uniq`：map_uniq (ψ : b ⟶ b') [Is
HomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') : ψ = IsCocartesian.map p f φ φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two
 morphisms
`ψ ψ' : b ⟶ b'` lifting `𝟙 S` such that `φ ≫ ψ = φ ≫ ψ'`. Then we must have `ψ =
 ψ'`.
-/
protected lemma ext (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
    [IsHomLift p (𝟙 S) ψ] [IsHomLift p (𝟙 S) ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (φ ≫ ψ) ψ rfl, map_uniq p f φ (φ ≫ ψ) ψ' h.symm]

@[simp]
/-
**CategoryTheory.Functor.IsCocartesian.map_self** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.IsCocartesian`。
形式化陈述：map_self : IsCocartesian.map p f φ φ = 𝟙 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCocartesian.map_uniq`：map_uniq (ψ : b ⟶ b') [Is
HomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') : ψ = IsCocartesian.map p f φ φ'
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma map_self : IsCocartesian.map p f φ φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/-- The canonical isomorphism between the codomains of two co-Cartesian morphisms
lying over the same object. -/
/-
**CategoryTheory.Functor.IsCocartesian.codomainUniqueUpToIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.IsCocartesian`。
形式化陈述：codomainUniqueUpToIso {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ'] : b ≅ 
b' where hom
参数：φ' : a ⟶ b'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
The canonical isomorphism between the codomains of two co-Cartesian morphisms
lying over the same object.
-/
noncomputable def codomainUniqueUpToIso {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ'] :
    b ≅ b' where
  hom := IsCocartesian.map p f φ φ'
  inv := IsCocartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ
    apply IsCocartesian.ext p (p.map φ) φ
    simp only [fac_assoc, fac, comp_id]
  inv_hom_id := by
    subst_hom_lift p f φ'
    apply IsCocartesian.ext p (p.map φ') φ'
    simp only [fac_assoc, fac, comp_id]

/-- Postcomposing a co-Cartesian morphism with an isomorphism lifting the identity is
co-Cartesian. -/
/-
**CategoryTheory.Functor.IsCocartesian.of_comp_iso** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Functor.IsCocartesian`。
形式化陈述：of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] : IsCocartes
ian p f (φ ≫ φ'.hom) where universal_property
参数：φ' : b ≅ b'；𝟙 S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.Functor.IsCocartesian.fac`：fac : φ ≫ IsCocartesian.map p 
f φ φ' = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用引理 `CategoryTheory.Functor.IsCocartesian.map_uniq`：map_uniq (ψ : b ⟶ b') [Is
HomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') : ψ = IsCocartesian.map p f φ φ'

--- 原说明 ---
Postcomposing a co-Cartesian morphism with an isomorphism lifting the identity i
s
co-Cartesian.
-/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCocartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use φ'.inv ≫ IsCocartesian.map p f φ ψ
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_inv_comp]
    apply map_uniq
    exact ((assoc φ _ _) ▸ hτ₂)

/-- Precomposing a co-Cartesian morphism with an isomorphism lifting the identity is
co-Cartesian. -/
/-
**CategoryTheory.Functor.IsCocartesian.of_iso_comp** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Functor.IsCocartesian`。
形式化陈述：of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] : IsCocartes
ian p f (φ'.hom ≫ φ) where universal_property
参数：φ' : a' ≅ a；𝟙 R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.IsCocartesian.fac`：fac : φ ≫ IsCocartesian.map p 
f φ φ' = φ'
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsCocartesian.map_uniq`：map_uniq (ψ : b ⟶ b') [Is
HomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') : ψ = IsCocartesian.map p f φ φ'

--- 原说明 ---
Precomposing a co-Cartesian morphism with an isomorphism lifting the identity is
co-Cartesian.
-/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCocartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCocartesian.map p f φ (φ'.inv ≫ ψ)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_inv_comp, ← assoc, hτ₂]

end IsCocartesian

namespace IsStronglyCocartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCocartesian p f φ]

/-- The universal property of a strongly co-Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the field
`universal_property'` of `IsStronglyCocartesian`. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.universal_property** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：universal_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' 
= f ≫ g) (φ' : a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', IsHomLift p g χ
 ∧ φ ≫ χ = φ'
参数：g : S ⟶ S'；f' : R ⟶ S'；hf' : f' = f ≫ g；φ' : a ⟶ b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property'`：∀ {𝒮 :
 Type u₁} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The universal property of a strongly co-Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the
 field
`universal_property'` of `IsStronglyCocartesian`.
-/
lemma universal_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g)
    (φ' : a ⟶ b') [IsHomLift p f' φ'] : ∃! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (f ≫ g) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCocartesian.universal_property' f
/-
**CategoryTheory.Functor.IsStronglyCocartesian.isCocartesian_of_isStronglyCocart
esian** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：isCocartesian_of_isStronglyCocartesian : p.IsCocartesian f φ where univers
al_property
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property`：univers
al_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' 
: a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance isCocartesian_of_isStronglyCocartesian : p.IsCocartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 S) f (comp_id f).symm φ'

section

variable {S' : 𝒮} {b' : 𝒳} {g : S ⟶ S'} {f' : R ⟶ S'} (hf' : f' = f ≫ g) (φ' : a ⟶ b')
  [IsHomLift p f' φ']

/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and a morphism `φ' : a ⟶ b'`. Then `map` is the map
`b ⟶ b'` lying over `g` obtained from the universal property of `φ`. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.map** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：map : b ⟶ b'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property`：univers
al_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' 
: a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', I…

--- 原说明 ---
Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and a morphism `φ' : a ⟶ b'`. Then `map`
 is the map
`b ⟶ b'` lying over `g` obtained from the universal property of `φ`.
-/
noncomputable def map : b ⟶ b' :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'
/-
**CategoryTheory.Functor.IsStronglyCocartesian.map_isHomLift** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：map_isHomLift : IsHomLift p g (map p f φ hf' φ')
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property`：univers
al_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' 
: a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', I…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsStronglyCocartesian.fac** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：fac : φ ≫ (map p f φ hf' φ') = φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property`：univers
al_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' 
: a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma fac : φ ≫ (map p f φ hf' φ') = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2


/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `φ' : a ⟶ b'`, `ψ : b ⟶ b'` such that
`g ≫ ψ = φ'`. Then `ψ` is the map induced by the universal property. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.map_uniq** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：map_uniq (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ 
hf' φ'
参数：ψ : b ⟶ b'；hψ : φ ≫ ψ = φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.universal_property`：univers
al_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' 
: a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', I…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `φ' : a ⟶ b'`, `ψ : b ⟶ b'
` such that
`g ≫ ψ = φ'`. Then `ψ` is the map induced by the universal property.
-/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `ψ ψ' : b ⟶ b'` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsStronglyCocartesian f φ] {S' :
 𝒮}   {b' : 𝒳} (g : S ⟶ S') {ψ ψ' : b ⟶ b'} [p.IsHomLift g ψ] [p.IsHomLift g ψ']
,   CategoryTheory.CategoryStruct.comp φ ψ = CategoryTheory.CategoryStruct.comp 
φ ψ' → ψ = ψ'
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S；φ : a ⟶ b；g : S ⟶ S'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.map_uniq`：map_uniq (ψ : b ⟶
 b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `ψ ψ' : b ⟶ b'` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`.
-/
protected lemma ext (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
    {ψ ψ' : b ⟶ b'} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ rfl, map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ' h.symm]

@[simp]
/-
**CategoryTheory.Functor.IsStronglyCocartesian.map_self** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：map_self : map p f φ (comp_id f).symm φ = 𝟙 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.map_uniq`：map_uniq (ψ : b ⟶
 b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ'
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
lemma map_self : map p f φ (comp_id f).symm φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/-- When its possible to compare the two, the composition of two `IsStronglyCocartesian.map` will
also be given by a `IsStronglyCocartesian.map`. In other words, given diagrams
```
a --φ--> b        b'         b''
|        |        |          |
v        v        v          v
R --f--> S --g--> S' --g'--> S'
```
and
```
a --φ'--> b'
|         |
v         v
R --f'--> S'

```
and
```
a --φ''--> b''
|          |
v          v
R --f''--> S''
```
such that `φ` and `φ'` are strongly co-Cartesian morphisms, and such that `f' = f ≫ g` and
`f'' = f' ≫ g'`. Then composing the induced map from `b ⟶ b'` with the induced map from
`b' ⟶ b''` gives the induced map from `b ⟶ b''`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsStronglyCocartesian.map_comp_map** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：map_comp_map {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : 
S ⟶ S'} {g' : S' ⟶ S''} (H : f' = f ≫ g) (H' : f'' = f' ≫ g') (φ' : a ⟶ b') (φ''
 : a ⟶ b'') [IsStronglyCocartesian p f' φ'] [IsHomLift p f'' φ''] : map p f φ H 
φ' ≫ map p f' φ' H' φ'' = map p f φ (show f'' = f ≫ (g ≫ g') by rwa [← assoc, ← 
H]) φ''
参数：H : f' = f ≫ g；H' : f'' = f' ≫ g'；φ' : a ⟶ b'；φ'' : a ⟶ b''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.map_uniq`：map_uniq (ψ : b ⟶
 b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.fac_assoc`：∀ {𝒮 : Type u₁} 
{𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.fac`：fac : φ ≫ (map p f φ h
f' φ') = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When its possible to compare the two, the composition of two `IsStronglyCocartes
ian.map` will
also be given by a `IsStronglyCocartesian.map`. In other words, given diagrams
```
a --φ--> b        b'         b''
|        |        |          |
v        v        v          v
R --f--> S --g--> S' --g'--> S'
```
and
```
a --φ'--> b'
|         |
v         v
R --f'--> S'

```
and
```
a --φ''--> b''
|          |
v          v
R --f''--> S''
```
such that `φ` and `φ'` are strongly co-Cartesian morphisms, and such that `f' = 
f ≫ g` and
`f'' = f' ≫ g'`. Then composing the induced map from `b ⟶ b'` with the induced m
ap from
`b' ⟶ b''` gives the induced map from `b ⟶ b''`.
-/
lemma map_comp_map {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : S ⟶ S'}
    {g' : S' ⟶ S''} (H : f' = f ≫ g) (H' : f'' = f' ≫ g') (φ' : a ⟶ b') (φ'' : a ⟶ b'')
    [IsStronglyCocartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f φ H φ' ≫ map p f' φ' H' φ'' =
      map p f φ (show f'' = f ≫ (g ≫ g') by rwa [← assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [fac_assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/-- Given two strongly co-Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly co-Cartesian. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.comp** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ] : IsStron
glyCocartesian p (f ≫ g) (φ ≫ ψ) where universal_property'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.map.congr_simp`：∀ {𝒮 : Type
 u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Categor
yTheory.Category.{v₂, u₂} 𝒳]   (p p_1 : CategoryT…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.fac`：fac : φ ≫ (map p f φ h
f' φ') = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.map_uniq`：map_uniq (ψ : b ⟶
 b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given two strongly co-Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly co-Cartesian.
-/
instance comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ] :
    IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro c' h τ hτ
    use map p g ψ (f' := g ≫ h) rfl <| map p f φ (assoc f g h) τ
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simp only [assoc, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [← hπ'₂, assoc]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `φ` are strongly co-Cartesian, then so is `ψ`. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.of_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}   [p.Is
StronglyCocartesian f φ]   [p.IsStronglyCocartesian (CategoryTheory.CategoryStru
ct.comp f g) (CategoryTheory.CategoryStruct.comp φ ψ)]   [p.IsHomLift g ψ], p.Is
StronglyCocartesian g ψ
参数：p : CategoryTheory.Functor 𝒳 𝒮；CategoryTheory.CategoryStruct.comp f g；Categor
yTheory.CategoryStruct.comp φ ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.ext`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.map.congr_simp`：∀ {𝒮 : Type
 u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Categor
yTheory.Category.{v₂, u₂} 𝒳]   (p p_1 : CategoryT…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.fac`：fac : φ ≫ (map p f φ h
f' φ') = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.map_uniq`：map_uniq (ψ : b ⟶
 b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `φ` are strongly co-Cartesian, then so is `ψ`.
-/
protected lemma of_comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p g ψ] : IsStronglyCocartesian p g ψ where
  universal_property' := by
    intro c' h τ hτ
    /- We get a morphism `π : c ⟶ c'` such that `(φ ≫ ψ) ≫ π = φ ≫ τ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := f ≫ g ≫ h) (assoc f g h).symm (φ ≫ τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `ψ ≫ π = τ` follows from `φ ≫ ψ ≫ π = φ ≫ τ` and the universal property of
    `φ`. -/
    · apply IsStronglyCocartesian.ext p f φ (g ≫ h) <| by simp only [← assoc, fac]
    -- Finally, uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

/-
**CategoryTheory.Functor.IsStronglyCocartesian.of_iso** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCocartesian p f φ.hom
 where universal_property'
参数：φ : a ≅ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `CategoryTheory.IsHomLift.isoOfIsoLift_inv_hom_id`：isoOfIsoLift_inv_hom_i
d (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] : (isoOfIsoLift p f φ).inv ≫ f =
 𝟙 S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCocartesian p f φ.hom where
  universal_property' := by
    intro b' g τ hτ
    use φ.inv ≫ τ
    refine ⟨?_, by cat_disch⟩
    simpa [← assoc] using (IsHomLift.comp p (isoOfIsoLift p f φ).inv (f ≫ g) φ.inv τ)
/-
**CategoryTheory.Functor.IsStronglyCocartesian.of_isIso** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCocartesian p
 f φ
参数：φ : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCocartesian p f φ :=
  @IsStronglyCocartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/-- A strongly co-Cartesian arrow lying over an isomorphism is an isomorphism. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f] : 
IsIso φ
参数：φ : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsHomLift.instIsHomLiftIdObj`：∀ {𝒮 : Type u₁} {𝒳 : Type u
₂} [inst : CategoryTheory.Category.{v₁, u₂} 𝒳] [inst_1 : CategoryTheory.Category
.{v₂, u₁} 𝒮]   (p : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsStronglyCocartesian.fac`：fac : φ ≫ (map p f φ h
f' φ') = φ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.ext`：∀ {𝒮 : Type u₁} {𝒳 : T
ype u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A strongly co-Cartesian arrow lying over an isomorphism is an isomorphism.
-/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ'` be the morphism induced by applying universal property to `𝟙 a` lying over `f ≫ f⁻¹`.
  let φ' := map p (p.map φ) φ (IsIso.hom_inv_id (p.map φ)).symm (𝟙 a)
  use φ'
  -- `φ ≫ φ' = 𝟙 a` follows immediately from the universal property.
  have inv_hom : φ ≫ φ' = 𝟙 a := fac p (p.map φ) φ _ (𝟙 a)
  refine ⟨inv_hom, ?_⟩
  -- We will now show that `φ' ≫ φ = 𝟙 b` by showing that `φ ≫ (φ' ≫ φ) = φ ≫ 𝟙 b`.
  have h₁ : IsHomLift p (𝟙 (p.obj b)) (φ' ≫ φ) := by
    rw [← IsIso.inv_hom_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCocartesian.ext p (p.map φ) φ (𝟙 (p.obj b))
  simp only [← assoc, inv_hom, comp_id, id_comp]

end

/-- The canonical isomorphism between the codomains of two strongly co-Cartesian arrows lying over
isomorphic objects. -/
/-
**CategoryTheory.Functor.IsStronglyCocartesian.codomainIsoOfBaseIso** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Functor.IsStronglyCocartesian`。
形式化陈述：codomainIsoOfBaseIso {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'} {
g : S ≅ S'} (h : f' = f ≫ g.hom) (φ : a ⟶ b) (φ' : a ⟶ b') [IsStronglyCocartesia
n p f φ] [IsStronglyCocartesian p f' φ'] : b ≅ b' where hom
参数：h : f' = f ≫ g.hom；φ : a ⟶ b；φ' : a ⟶ b'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsStronglyCocartesian.toIsHomLift`：∀ {𝒮 : Type u₁
} {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
The canonical isomorphism between the codomains of two strongly co-Cartesian arr
ows lying over
isomorphic objects.
-/
noncomputable def codomainIsoOfBaseIso {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'}
    {g : S ≅ S'} (h : f' = f ≫ g.hom) (φ : a ⟶ b) (φ' : a ⟶ b') [IsStronglyCocartesian p f φ]
    [IsStronglyCocartesian p f' φ'] : b ≅ b' where
  hom := map p f φ h φ'
  inv := @map _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (· ≫ g.inv) h.symm) φ
    (by simp only [assoc, Iso.hom_inv_id, comp_id]; infer_instance)

end IsStronglyCocartesian

end CategoryTheory.Functor

