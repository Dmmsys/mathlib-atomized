/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)fibered.

## Main definitions

- `IsPreFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that any morphism in the base `𝒮` can be lifted to a Cartesian morphism in `𝒳`.

- `IsFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that it is prefibered, and that the composition of any two Cartesian morphisms is
  Cartesian.

In the literature one often sees the notion of a fibered category defined as the existence of
strongly Cartesian morphisms lying over any given morphism in the base. This is equivalent to the
notion above, and we give an alternate constructor `IsFibered.of_exists_isCartesian'` for
constructing a fibered category this way.

## Implementation

The constructor of `IsPreFibered` is called `exists_isCartesian'`. The reason for the prime is that
when wanting to apply this condition, it is recommended to instead use the lemma
`exists_isCartesian` (without the prime), which is more applicable with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Definition of a prefibered category.

See SGA 1 VI.6.1. -/
/-
**CategoryTheory.Functor.IsPreFibered** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] → CategoryTheory.F
unctor 𝒳 𝒮 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of a prefibered category.

See SGA 1 VI.6.1.
-/
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCartesian' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ
/-
**CategoryTheory.IsPreFibered.exists_isCartesian** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsPreFibered`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheory.Functor 𝒳 𝒮)
 [p.IsPreFibered] {a : 𝒳} {R S : 𝒮},   p.obj a = S → ∀ (f : R ⟶ S), ∃ b φ, p.IsC
artesian f φ
参数：p : CategoryTheory.Functor 𝒳 𝒮；f : R ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsPreFibered.exists_isCartesian'`：∀ {𝒮 : Type u₁}
 {𝒳 : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryThe
ory.Category.{v₂, u₂} 𝒳}   {p : CategoryTheor…
-/
protected lemma IsPreFibered.exists_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.exists_isCartesian' f

/-- Definition of a fibered category.

See SGA 1 VI.6.1. -/
/-
**CategoryTheory.Functor.IsFibered** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{𝒮 : Type u₁} →   {𝒳 : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} 𝒮] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳] → CategoryTheory.F
unctor 𝒳 𝒮 → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of a fibered category.

See SGA 1 VI.6.1.
-/
class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) : Prop extends IsPreFibered p where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ) :=
  IsFibered.comp f g φ ψ

namespace Functor.IsPreFibered

variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

/-- Given a fibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` lying over `S`,
then `pullbackObj` is the domain of some choice of a Cartesian morphism lying over `f` with
codomain `a`. -/
/-
**CategoryTheory.Functor.IsPreFibered.pullbackObj** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.IsPreFibered`。
形式化陈述：pullbackObj : 𝒳
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreFibered.exists_isCartesian`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳]   (p : CategoryTheor…

--- 原说明 ---
Given a fibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` l
ying over `S`,
then `pullbackObj` is the domain of some choice of a Cartesian morphism lying ov
er `f` with
codomain `a`.
-/
noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreFibered.exists_isCartesian p ha f)

/-- Given a fibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` lying over `S`,
then `pullbackMap` is a choice of a Cartesian morphism lying over `f` with codomain `a`. -/
/-
**CategoryTheory.Functor.IsPreFibered.pullbackMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.IsPreFibered`。
形式化陈述：pullbackMap : pullbackObj ha f ⟶ a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPreFibered.exists_isCartesian`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳]   (p : CategoryTheor…

--- 原说明 ---
Given a fibered category `p : 𝒳 ⥤ 𝒫`, a morphism `f : R ⟶ S` and an object `a` l
ying over `S`,
then `pullbackMap` is a choice of a Cartesian morphism lying over `f` with codom
ain `a`.
-/
noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))
/-
**CategoryTheory.Functor.IsPreFibered.pullbackMap.IsCartesian** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.IsPreFibered.pullbackMap`。
形式化陈述：∀ {𝒮 : Type u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheory.Functor 𝒳 𝒮}
 [inst_2 : p.IsPreFibered] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S),   p
.IsCartesian f (CategoryTheory.Functor.IsPreFibered.pullbackMap ha f)
参数：ha : p.obj a = S；f : R ⟶ S；CategoryTheory.Functor.IsPreFibered.pullbackMap ha
 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.IsPreFibered.exists_isCartesian`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳]   (p : CategoryTheor…
-/
instance pullbackMap.IsCartesian : IsCartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))
/-
**CategoryTheory.Functor.IsPreFibered.pullbackObj_proj** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.IsPreFibered`。
形式化陈述：pullbackObj_proj : p.obj (pullbackObj ha f) = R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsPreFibered.pullbackMap.IsCartesian`：∀ {𝒮 : Type
 u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Categor
yTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheor…
-/
lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end Functor.IsPreFibered

namespace Functor.IsFibered

open IsCartesian Functor.IsPreFibered

/-- In a fibered category, any Cartesian morphism is strongly Cartesian. -/
/-
**CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_isCartesian** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsFibered`。
形式化陈述：isStronglyCartesian_of_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f 
: R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ w
here universal_property' g φ' hφ'
参数：p : 𝒳 ⥤ 𝒮；f : R ⟶ S；φ : a ⟶ b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsFibered.toIsPreFibered`：∀ {𝒮 : Type u₁} {𝒳 : Ty
pe u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用定理 `CategoryTheory.instIsCartesianCompOfIsFibered`：∀ {𝒮 : Type u₁} {𝒳 : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsPreFibered.pullbackMap.IsCartesian`：∀ {𝒮 : Type
 u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Categor
yTheory.Category.{v₂, u₂} 𝒳]   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.IsCartesian.fac`：fac : IsCartesian.map p f φ φ' ≫
 φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCartesian.map_uniq`：map_uniq (ψ : a' ⟶ a) [IsHo
mLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = IsCartesian.map p f φ φ'

--- 原说明 ---
In a fibered category, any Cartesian morphism is strongly Cartesian.
-/
instance isStronglyCartesian_of_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ where
  universal_property' g φ' hφ' := by
    -- Let `ψ` be a Cartesian arrow lying over `g`
    let ψ := pullbackMap (domain_eq p f φ) g
    -- Let `τ` be the map induced by the universal property of `ψ ≫ φ`.
    let τ := IsCartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    -- It is easily verified that `τ ≫ ψ` lifts `g` and `τ ≫ ψ ≫ φ = φ'`
    refine ⟨⟨inferInstance, by simp only [assoc, IsCartesian.fac, τ]⟩, ?_⟩
    -- It remains to check that `τ ≫ ψ` is unique.
    -- So fix another lift `π` of `g` satisfying `π ≫ φ = φ'`.
    intro π ⟨hπ, hπ_comp⟩
    -- Write `π` as `π = τ' ≫ ψ` for some `τ'` induced by the universal property of `ψ`.
    rw [← fac p g ψ π]
    -- It remains to show that `τ' = τ`. This follows again from the universal property of `ψ`.
    congr 1
    apply map_uniq
    rwa [← assoc, IsCartesian.fac]

/-- In a category which admits strongly Cartesian pullbacks, any Cartesian morphism is
strongly Cartesian. This is a helper-lemma for the fact that admitting strongly Cartesian pullbacks
implies being fibered. -/
/-
**CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_exists_isCartesian** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsFibered`。
形式化陈述：isStronglyCartesian_of_exists_isCartesian (p : 𝒳 ⥤ 𝒮) (h : forall (a : 𝒳) 
(R : 𝒮) (f : R ⟶ p.obj a), exists (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ
) {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStrongly
Cartesian f φ
参数：p : 𝒳 ⥤ 𝒮；h : forall (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a), exists (b : 𝒳) (φ : b
 ⟶ a), IsStronglyCartesian p f φ；f : R ⟶ S；φ : a ⟶ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCartesian.toIsHomLift`：∀ {𝒮 : Type u₁} {𝒳 : Typ
e u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} 𝒳}   {p : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_hom`：∀ {𝒮 : Type 
u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Category
Theory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.IsCartesian.fac`：fac : IsCartesian.map p f φ φ' ≫
 φ = φ'
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.fac`：fac : (map p f φ hf' φ')
 ≫ φ = φ'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CategoryTheory.Functor.IsStronglyCartesian.map_uniq`：map_uniq (ψ : a' ⟶ 
a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ'
· 使用定理 `CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso_inv`：∀ {𝒮 : Type 
u₁} {𝒳 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} 𝒮] [inst_1 : Category
Theory.Category.{v₂, u₂} 𝒳]   (p : CategoryTheor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
In a category which admits strongly Cartesian pullbacks, any Cartesian morphism 
is
strongly Cartesian. This is a helper-lemma for the fact that admitting strongly 
Cartesian pullbacks
implies being fibered.
-/
lemma isStronglyCartesian_of_exists_isCartesian (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (R : 𝒮)
    (f : R ⟶ p.obj a), ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) {R S : 𝒮} (f : R ⟶ S)
      {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a Cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCartesian.map p (p.map φ) ψ (f' := g ≫ p.map φ) rfl φ'
  -- Let `Φ : a' ≅ a` be natural isomorphism induced between `φ` and `ψ`.
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  -- The map induced by `φ` will be `τ' ≫ Φ.hom`
  use τ' ≫ Φ.hom
  -- It is easily verified that `τ' ≫ Φ.hom` lifts `g` and `τ' ≫ Φ.hom ≫ φ = φ'`
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ]
  -- It remains to check that it is unique. This follows from the universal property of `ψ`.
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]

/-- Alternate constructor for `IsFibered`, a functor `p : 𝒳 ⥤ 𝒴` is fibered if any diagram of the
form
```
          a
          -
          |
          v
R --f--> p(a)
```
admits a strongly Cartesian lift `b ⟶ a` of `f`. -/
/-
**CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor.IsFibered`。
形式化陈述：of_exists_isStronglyCartesian {p : 𝒳 ⥤ 𝒮} (h : forall (a : 𝒳) (R : 𝒮) (f :
 R ⟶ p.obj a), exists (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) : IsFibere
d p where exists_isCartesian'
参数：h : forall (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a), exists (b : 𝒳) (φ : b ⟶ a), IsS
tronglyCartesian p f φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_exists_isCartesi
an`：isStronglyCartesian_of_exists_isCartesian (p : 𝒳 ⥤ 𝒮) (h : forall (a : 𝒳) (R
 : 𝒮) (f : R ⟶ p.obj a), exists (b : 𝒳) (φ : b ⟶ a), IsStronglyC…

--- 原说明 ---
Alternate constructor for `IsFibered`, a functor `p : 𝒳 ⥤ 𝒴` is fibered if any d
iagram of the
form
```
          a
          -
          |
          v
R --f--> p(a)
```
admits a strongly Cartesian lift `b ⟶ a` of `f`.
-/
lemma of_exists_isStronglyCartesian {p : 𝒳 ⥤ 𝒮}
    (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
      ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) :
    IsFibered p where
  exists_isCartesian' := by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCartesian f φ := isStronglyCartesian_of_exists_isCartesian p h _ _
    have : p.IsStronglyCartesian g ψ := isStronglyCartesian_of_exists_isCartesian p h _ _
    inferInstance

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism `T ×_S a ≅ T ×_R (R ×_S a)` -/
/-
**CategoryTheory.Functor.IsFibered.pullbackPullbackIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.IsFibered`。
形式化陈述：pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p] {R S T : 𝒮} {a : 𝒳} (ha : p.
obj a = S) (f : R ⟶ S) (g : T ⟶ R) : pullbackObj ha (g ≫ f) ≅ pullbackObj (pullb
ackObj_proj ha f) g
参数：ha : p.obj a = S；f : R ⟶ S；g : T ⟶ R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsFibered.toIsPreFibered`：∀ {𝒮 : Type u₁} {𝒳 : Ty
pe u₂} {inst : CategoryTheory.Category.{v₁, u₁} 𝒮} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} 𝒳}   {p : CategoryTheor…

--- 原说明 ---
Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism `T ×_S a ≅ T ×_R (R ×_S a)`
-/
noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p]
    {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

end Functor.IsFibered

end CategoryTheory

