/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Morphisms of localizers

A morphism of localizers consists of a functor `F : C₁ ⥤ C₂` between
two categories equipped with morphism properties `W₁` and `W₂` such
that `F` sends morphisms in `W₁` to morphisms in `W₂`.

If `Φ : LocalizerMorphism W₁ W₂`, and that `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for `W₁` and `W₂`, the induced functor `D₁ ⥤ D₂`
is denoted `Φ.localizedFunctor L₁ L₂`; we introduce the condition
`Φ.IsLocalizedEquivalence` which expresses that this functor is an equivalence
of categories. This condition is independent of the choice of the
localized categories.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₄' v₅ v₅' v₆ u₁ u₂ u₃ u₄ u₄' u₅ u₅' u₆

namespace CategoryTheory

open Localization CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} D₁] [Category.{v₅} D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

/-- If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizerMorphism W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂` -/
/-
**CategoryTheory.LocalizerMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     [inst : CategoryTheory.Category.{v
₁, u₁} C₁] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] →         Cate
goryTheory.MorphismProperty C₁ → CategoryTheory.MorphismProperty C₂ → Type (max 
(max (max u₁ u₂) v₁) v₂)
参数：max (max (max u₁ u₂) v₁) v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`, a `LocalizerMorphi
sm W₁ W₂`
is the datum of a functor `C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms i
n `W₂`
-/
structure LocalizerMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ≤ W₂.inverseImage functor

namespace LocalizerMorphism

variable {W₁ W₂} in
/-- Constructor for localizer morphisms given by a functor `F : C₁ ⥤ C₂`
under the stronger assumption that the classes of morphisms `W₁` and `W₂`
satisfy `W₁ = W₂.inverseImage F`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.LocalizerMorphism`。
形式化陈述：ofEq {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F) : LocalizerMorphism W₁ W₂
 where functor
参数：hW : W₁ = W₂.inverseImage F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for localizer morphisms given by a functor `F : C₁ ⥤ C₂`
under the stronger assumption that the classes of morphisms `W₁` and `W₂`
satisfy `W₁ = W₂.inverseImage F`.
-/
def ofEq {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F) : LocalizerMorphism W₁ W₂ where
  functor := F
  map := by rw [hW]

/-- The identity functor as a morphism of localizers. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
LocalizerMorphism`。
形式化陈述：id : LocalizerMorphism W₁ W₁ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor as a morphism of localizers.
-/
def id : LocalizerMorphism W₁ W₁ where
  functor := 𝟭 C₁
  map _ _ _ hf := hf
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (id W₁).functor.IsEquivalence :=
  inferInstanceAs (𝟭 C₁).IsEquivalence

variable {W₁ W₂ W₃}

/-- The composition of two localizers morphisms. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.LocalizerMorphism`。
形式化陈述：comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) : Localiz
erMorphism W₁ W₃ where functor
参数：Φ : LocalizerMorphism W₁ W₂；Ψ : LocalizerMorphism W₂ W₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two localizers morphisms.
-/
def comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) :
    LocalizerMorphism W₁ W₃ where
  functor := Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

variable (Φ : LocalizerMorphism W₁ W₂)

/-- The opposite localizer morphism `LocalizerMorphism W₁.op W₂.op` deduced
from `Φ : LocalizerMorphism W₁ W₂`. -/
/-
**CategoryTheory.LocalizerMorphism.op** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.LocalizerMorphism`。
形式化陈述：op : LocalizerMorphism W₁.op W₂.op where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite localizer morphism `LocalizerMorphism W₁.op W₂.op` deduced
from `Φ : LocalizerMorphism W₁ W₂`.
-/
abbrev op : LocalizerMorphism W₁.op W₂.op where
  functor := Φ.functor.op
  map _ _ _ hf := Φ.map _ hf

variable (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
/-
**CategoryTheory.LocalizerMorphism.inverts** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.LocalizerMorphism`。
形式化陈述：inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.LocalizerMorphism.map`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{
v₂, u₂} C₂] {W₁ : Category…
-/
lemma inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂) :=
  fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

/-- When `Φ : LocalizerMorphism W₁ W₂` and that `L₁` and `L₂` are localization functors
for `W₁` and `W₂`, then `Φ.localizedFunctor L₁ L₂` is the induced functor on the
localized categories. -/
/-
**CategoryTheory.LocalizerMorphism.localizedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.LocalizerMorphism`。
形式化陈述：localizedFunctor : D₁ ⥤ D₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.inverts`：inverts : W₁.IsInvertedBy (Φ.f
unctor ⋙ L₂)

--- 原说明 ---
When `Φ : LocalizerMorphism W₁ W₂` and that `L₁` and `L₂` are localization funct
ors
for `W₁` and `W₂`, then `Φ.localizedFunctor L₁ L₂` is the induced functor on the
localized categories.
-/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁
/-
**CategoryTheory.LocalizerMorphism.liftingLocalizedFunctor** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：liftingLocalizedFunctor : Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunct
or L₁ L₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance liftingLocalizedFunctor :
    Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) :=
  inferInstanceAs <| Lifting L₁ W₁ _ (lift _ _ L₁)

/-- The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor` -/
/-
**CategoryTheory.LocalizerMorphism.catCommSq** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.LocalizerMorphism`。
形式化陈述：catCommSq : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-commutative square expressing that `Φ.localizedFunctor L₁ L₂` lifts the
functor `Φ.functor`
-/
noncomputable instance catCommSq : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂) :=
  CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

variable (G : D₁ ⥤ D₂)

section

variable [CatCommSq Φ.functor L₁ L₂ G]
  {D₁' : Type u₄'} {D₂' : Type u₅'}
  [Category.{v₄'} D₁'] [Category.{v₅'} D₂']
  (L₁' : C₁ ⥤ D₁') (L₂' : C₂ ⥤ D₂') [L₁'.IsLocalization W₁] [L₂'.IsLocalization W₂]
  (G' : D₁' ⥤ D₂') [CatCommSq Φ.functor L₁' L₂' G']
include W₁ W₂ Φ L₁ L₂ L₁' L₂'

/-- If a localizer morphism induces an equivalence on some choice of localized categories,
it will be so for any choice of localized categories. -/
/-
**CategoryTheory.LocalizerMorphism.isEquivalence_imp** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.LocalizerMorphism`。
形式化陈述：isEquivalence_imp [G.IsEquivalence] : G'.IsEquivalence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_iso`：isEquivalence_of_iso {F G :
 C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence
· 使用定理 `CategoryTheory.Functor.isEquivalence_trans`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_comp_left`：isEquivalence_of_comp
_left {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEqu
ivalence (F ⋙ G)] : IsEquivalence G

--- 原说明 ---
If a localizer morphism induces an equivalence on some choice of localized categ
ories,
it will be so for any choice of localized categories.
-/
lemma isEquivalence_imp [G.IsEquivalence] : G'.IsEquivalence :=
  let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G).symm E₂.functor ≪≫
            associator _ _ _
      _ ≅ Φ.functor ⋙ L₂' := isoWhiskerLeft Φ.functor (compUniqFunctor L₂ L₂' W₂)
      _ ≅ L₁' ⋙ G' := CatCommSq.iso Φ.functor L₁' L₂' G'
      _ ≅ L₁ ⋙ E₁.functor ⋙ G' :=
            isoWhiskerRight (compUniqFunctor L₁ L₁' W₁).symm G' ≪≫ associator _ _ _
  have := Functor.isEquivalence_of_iso
    (liftNatIso L₁ W₁ _ _ (G ⋙ E₂.functor) (E₁.functor ⋙ G') e)
  Functor.isEquivalence_of_comp_left E₁.functor G'
/-
**CategoryTheory.LocalizerMorphism.isEquivalence_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.LocalizerMorphism`。
形式化陈述：isEquivalence_iff : G.IsEquivalence ↔ G'.IsEquivalence
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isEquivalence_imp`：isEquivalence_imp [G
.IsEquivalence] : G'.IsEquivalence
-/
lemma isEquivalence_iff : G.IsEquivalence ↔ G'.IsEquivalence :=
  ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

/-- If a localizer morphism induces a fully faithful functor on some choice of
localized categories, it will be so for any choice of localized categories. -/
/-
**CategoryTheory.LocalizerMorphism.fullyFaithfulImp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.LocalizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a localizer morphism induces a fully faithful functor on some choice of
localized categories, it will be so for any choice of localized categories.
-/
private noncomputable def fullyFaithfulImp (hG : G.FullyFaithful) : G'.FullyFaithful :=
  let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G).symm E₂.functor ≪≫
            associator _ _ _
      _ ≅ Φ.functor ⋙ L₂' := isoWhiskerLeft Φ.functor (compUniqFunctor L₂ L₂' W₂)
      _ ≅ L₁' ⋙ G' := CatCommSq.iso Φ.functor L₁' L₂' G'
      _ ≅ L₁ ⋙ E₁.functor ⋙ G' :=
            isoWhiskerRight (compUniqFunctor L₁ L₁' W₁).symm G' ≪≫ associator _ _ _
  (E₁.fullyFaithfulInverse.comp (hG.comp E₂.fullyFaithfulFunctor)).ofIso
    ((isoWhiskerLeft (E₁.inverse) (liftNatIso L₁ W₁ _ _ (G ⋙ E₂.functor) (E₁.functor ⋙ G') e) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight E₁.counitIso G' ≪≫ G'.leftUnitor))
/-
**CategoryTheory.LocalizerMorphism.nonempty_fullyFaithful_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：nonempty_fullyFaithful_iff : Nonempty G.FullyFaithful ↔ Nonempty G'.FullyF
aithful
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nonempty_fullyFaithful_iff : Nonempty G.FullyFaithful ↔ Nonempty G'.FullyFaithful :=
  ⟨fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁ L₂ G L₁' L₂' G' h⟩,
    fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁' L₂' G' L₁ L₂ G h⟩⟩

end

/-- Condition that a `LocalizerMorphism` induces an equivalence on the localized categories -/
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence** 是 Mathlib 中的一个归纳类型，位
于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     [inst : CategoryTheory.Category.{v
₁, u₁} C₁] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] →         {W₁ 
: CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.MorphismP
roperty C₂} → CategoryTheory.LocalizerMorphism W₁ W₂ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condition that a `LocalizerMorphism` induces an equivalence on the localized cat
egories
-/
class IsLocalizedEquivalence : Prop where
  /-- the induced functor on the constructed localized categories is an equivalence -/
  isEquivalence : (Φ.localizedFunctor W₁.Q W₂.Q).IsEquivalence
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.mk'** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₄} {D₂ : Type u₅} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
] [inst_2 : CategoryTheory.Category.{v₄, u₄} D₁]   [inst_3 : CategoryTheory.Cate
gory.{v₅, u₅} D₂] {W₁ : CategoryTheory.MorphismProperty C₁}   {W₂ : CategoryTheo
ry.MorphismProperty C₂} (Φ : CategoryTheory.LocalizerMorphism W₁ W₂)   (L₁ : Cat
egoryTheory.Functor C₁ D₁) [L₁.IsLocalization W₁] (L₂ : CategoryTheory.Functor C
₂ D₂) [L₂.IsLocalization W₂]   (G : CategoryTheory.Functor D₁ D₂) [CategoryTheor
y.CatCommSq Φ.functor L₁ L₂ G] [G.IsEquivalence],   Φ.IsLocalizedEquivalence
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₁ : CategoryTheory.Functor C₁ D₁；
L₂ : CategoryTheory.Functor C₂ D₂；G : CategoryTheory.Functor D₁ D₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isEquivalence_iff`：isEquivalence_iff : 
G.IsEquivalence ↔ G'.IsEquivalence
-/
lemma IsLocalizedEquivalence.mk' [CatCommSq Φ.functor L₁ L₂ G] [G.IsEquivalence] :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    rw [Φ.isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact inferInstance

/-- If a `LocalizerMorphism` is a localized equivalence, then any compatible functor
between the localized categories is an equivalence. -/
/-
**CategoryTheory.LocalizerMorphism.isEquivalence** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.LocalizerMorphism`。
形式化陈述：isEquivalence [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G]
 : G.IsEquivalence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.isEquivalence_iff`：isEquivalence_iff : 
G.IsEquivalence ↔ G'.IsEquivalence
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isEquivalence`：∀
 {C₁ : Type u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {i
nst_1 : CategoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…

--- 原说明 ---
If a `LocalizerMorphism` is a localized equivalence, then any compatible functor
between the localized categories is an equivalence.
-/
lemma isEquivalence [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G] :
    G.IsEquivalence := (by
  rw [Φ.isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.isEquivalence)
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLocalizedEquivalence] : Φ.op.IsLocalizedEquivalence := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have := Φ.isEquivalence W₁.Q W₂.Q G
  exact IsLocalizedEquivalence.mk' Φ.op W₁.Q.op W₂.Q.op G.op

/-- If a `LocalizerMorphism` is a localized equivalence, then the induced functor on
the localized categories is an equivalence -/
/-
**CategoryTheory.LocalizerMorphism.localizedFunctor_isEquivalence** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] : (Φ.localizedFu
nctor L₁ L₂).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.isEquivalence`：isEquivalence [h : Φ.IsL
ocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G] : G.IsEquivalence

--- 原说明 ---
If a `LocalizerMorphism` is a localized equivalence, then the induced functor on
the localized categories is an equivalence
-/
instance localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] :
    (Φ.localizedFunctor L₁ L₂).IsEquivalence :=
  Φ.isEquivalence L₁ L₂ _

/-- When `Φ : LocalizerMorphism W₁ W₂`, if the composition `Φ.functor ⋙ L₂` is a
localization functor for `W₁`, then `Φ` is a localized equivalence. -/
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_i
sLocalization** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLoca
lizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] [inst_2 : Cat
egoryTheory.Category.{v₅, u₅} D₂]   {W₁ : CategoryTheory.MorphismProperty C₁} {W
₂ : CategoryTheory.MorphismProperty C₂}   (Φ : CategoryTheory.LocalizerMorphism 
W₁ W₂) (L₂ : CategoryTheory.Functor C₂ D₂) [L₂.IsLocalization W₂]   [(Φ.functor.
comp L₂).IsLocalization W₁], Φ.IsLocalizedEquivalence
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₂ : CategoryTheory.Functor C₂ D₂；
Φ.functor.comp L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.mk'`：∀ {C₁ : Typ
e u₁} {C₂ : Type u₂} {D₁ : Type u₄} {D₂ : Type u₅} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…

--- 原说明 ---
When `Φ : LocalizerMorphism W₁ W₂`, if the composition `Φ.functor ⋙ L₂` is a
localization functor for `W₁`, then `Φ` is a localized equivalence.
-/
lemma IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    [(Φ.functor ⋙ L₂).IsLocalization W₁] :
    IsLocalizedEquivalence Φ := by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

/-- When the underlying functor `Φ.functor` of `Φ : LocalizerMorphism W₁ W₂` is
an equivalence of categories and that `W₁` and `W₂` essentially correspond to each
other via this equivalence, then `Φ` is a localized equivalence. -/
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_equivalence** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C
₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : CategoryTheory.Morphis
mProperty C₁}   {W₂ : CategoryTheory.MorphismProperty C₂} (Φ : CategoryTheory.Lo
calizerMorphism W₁ W₂) [Φ.functor.IsEquivalence],   W₂ ≤ W₁.map Φ.functor → Φ.Is
LocalizedEquivalence
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsLocalization.of_equivalence_source`：of_equivale
nce_source (L₁ : C₁ ⥤ D) (W₁ : MorphismProperty C₁) (L₂ : C₂ ⥤ D) (W₂ : Morphism
Property C₂) (E : C₁ ≌ C₂) (hW₁ : W₁ <= W₂.isoClo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_equivalence_functor_eq_map_
inverse`：inverseImage_equivalence_functor_eq_map_inverse (Q : MorphismProperty C
) [RespectsIso Q] (E : C ≌ D) : Q.inverseImage E.inverse = Q.map E.fu…
· 使用引理 `CategoryTheory.MorphismProperty.map_isoClosure`：map_isoClosure (P : Morp
hismProperty C) (F : C ⥤ D) : P.isoClosure.map F = P.map F
· 使用引理 `CategoryTheory.LocalizerMorphism.inverts`：inverts : W₁.IsInvertedBy (Φ.f
unctor ⋙ L₂)
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_isLocalizatio
n_of_isLocalization`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
]…

--- 原说明 ---
When the underlying functor `Φ.functor` of `Φ : LocalizerMorphism W₁ W₂` is
an equivalence of categories and that `W₁` and `W₂` essentially correspond to ea
ch
other via this equivalence, then `Φ` is a localized equivalence.
-/
lemma IsLocalizedEquivalence.of_equivalence [Φ.functor.IsEquivalence]
    (h : W₂ ≤ W₁.map Φ.functor) : IsLocalizedEquivalence Φ := by
  have : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).symm) _ ≪≫
        leftUnitor _)
    erw [W₁.isoClosure.inverseImage_equivalence_functor_eq_map_inverse]
    rw [MorphismProperty.map_isoClosure]
    exact h
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] [inst_2 : Cat
egoryTheory.Category.{v₅, u₅} D₂]   {W₁ : CategoryTheory.MorphismProperty C₁} {W
₂ : CategoryTheory.MorphismProperty C₂}   (Φ : CategoryTheory.LocalizerMorphism 
W₁ W₂) (L₂ : CategoryTheory.Functor C₂ D₂) [L₂.IsLocalization W₂]   [Φ.IsLocaliz
edEquivalence], (Φ.functor.comp L₂).IsLocalization W₁
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₂ : CategoryTheory.Functor C₂ D₂；
Φ.functor.comp L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_iso`：of_iso {L₁ L₂ : C ⥤ D} (e 
: L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W
· 使用定理 `CategoryTheory.Functor.IsLocalization.instCompOfIsEquivalence`：∀ {C : Ty
pe u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
instance IsLocalizedEquivalence.isLocalization [Φ.IsLocalizedEquivalence] :
    (Φ.functor ⋙ L₂).IsLocalization W₁ :=
  Functor.IsLocalization.of_iso _ ((Φ.catCommSq W₁.Q L₂).iso).symm
/-
**CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLocalizedEquivalence_of_unit_of_unit (Ψ : LocalizerMorphism W₂ W₁) (ε₁ :
 𝟭 C₁ ⟶ Φ.functor ⋙ Ψ.functor) (ε₂ : 𝟭 C₂ ⟶ Ψ.functor ⋙ Φ.functor) (hε₁ : forall
 X₁, W₁ (ε₁.app X₁)) (hε₂ : forall X₂, W₂ (ε₂.app X₂)) : Φ.IsLocalizedEquivalenc
e where isEquivalence
参数：Ψ : LocalizerMorphism W₂ W₁；ε₁ : 𝟭 C₁ ⟶ Φ.functor ⋙ Ψ.functor；ε₂ : 𝟭 C₂ ⟶ Ψ.f
unctor ⋙ Φ.functor；hε₁ : forall X₁, W₁ (ε₁.app X₁)；hε₂ : forall X₂, W₂ (ε₂.app X
₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma isLocalizedEquivalence_of_unit_of_unit (Ψ : LocalizerMorphism W₂ W₁)
    (ε₁ : 𝟭 C₁ ⟶ Φ.functor ⋙ Ψ.functor) (ε₂ : 𝟭 C₂ ⟶ Ψ.functor ⋙ Φ.functor)
    (hε₁ : ∀ X₁, W₁ (ε₁.app X₁)) (hε₂ : ∀ X₂, W₂ (ε₂.app X₂)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ ↦ Localization.inverts W₂.Q W₂ _ (hε₂ _)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q)
      (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (asIso (whiskerRight ε₁ W₁.Q)).symm ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (asIso (whiskerRight ε₂ W₂.Q)).symm ≪≫ Functor.leftUnitor _
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.id** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C₁] {W₁ : Catego
ryTheory.MorphismProperty C₁},   (CategoryTheory.LocalizerMorphism.id W₁).IsLoca
lizedEquivalence
参数：CategoryTheory.LocalizerMorphism.id W₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_iso`：of_iso {L₁ L₂ : C ⥤ D} (e 
: L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_isLocalizatio
n_of_isLocalization`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
]…
-/
instance IsLocalizedEquivalence.id :
    (id W₁).IsLocalizedEquivalence :=
  have : ((LocalizerMorphism.id W₁).functor ⋙ W₁.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  of_isLocalization_of_isLocalization _ W₁.Q
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.comp** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] [inst_2 : Cat
egoryTheory.Category.{v₃, u₃} C₃]   {W₁ : CategoryTheory.MorphismProperty C₁} {W
₂ : CategoryTheory.MorphismProperty C₂}   {W₃ : CategoryTheory.MorphismProperty 
C₃} (Φ : CategoryTheory.LocalizerMorphism W₁ W₂) [Φ.IsLocalizedEquivalence]   (Ψ
 : CategoryTheory.LocalizerMorphism W₂ W₃) [Ψ.IsLocalizedEquivalence], (Φ.comp Ψ
).IsLocalizedEquivalence
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；Ψ : CategoryTheory.LocalizerMorphi
sm W₂ W₃；Φ.comp Ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_iso`：of_iso {L₁ L₂ : C ⥤ D} (e 
: L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : CategoryTheory.Category.{
v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_isLocalizatio
n_of_isLocalization`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₂ : Type u₅} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
]…
-/
instance IsLocalizedEquivalence.comp [Φ.IsLocalizedEquivalence]
    (Ψ : LocalizerMorphism W₂ W₃)
    [Ψ.IsLocalizedEquivalence] :
    (Φ.comp Ψ).IsLocalizedEquivalence :=
  have : ((Φ.comp Ψ).functor ⋙ W₃.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.associator _ _ _).symm
  of_isLocalization_of_isLocalization _ W₃.Q

/-- Condition that a `LocalizerMorphism` induces a fully faithful functor
on the localized categories. -/
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful** 是 Mathlib 中的一个归纳类型
，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     [inst : CategoryTheory.Category.{v
₁, u₁} C₁] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] →         {W₁ 
: CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.MorphismP
roperty C₂} → CategoryTheory.LocalizerMorphism W₁ W₂ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condition that a `LocalizerMorphism` induces a fully faithful functor
on the localized categories.
-/
class IsLocalizedFullyFaithful : Prop where
  /-- the induced functor on the constructed localized categories is fully faithful -/
  nonempty_fullyFaithful : Nonempty (Φ.localizedFunctor W₁.Q W₂.Q).FullyFaithful
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful.mk'** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₄} {D₂ : Type u₅} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
] [inst_2 : CategoryTheory.Category.{v₄, u₄} D₁]   [inst_3 : CategoryTheory.Cate
gory.{v₅, u₅} D₂] {W₁ : CategoryTheory.MorphismProperty C₁}   {W₂ : CategoryTheo
ry.MorphismProperty C₂} (Φ : CategoryTheory.LocalizerMorphism W₁ W₂)   (L₁ : Cat
egoryTheory.Functor C₁ D₁) [L₁.IsLocalization W₁] (L₂ : CategoryTheory.Functor C
₂ D₂) [L₂.IsLocalization W₂]   (G : CategoryTheory.Functor D₁ D₂) [CategoryTheor
y.CatCommSq Φ.functor L₁ L₂ G] (hG : G.FullyFaithful),   Φ.IsLocalizedFullyFaith
ful
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₁ : CategoryTheory.Functor C₁ D₁；
L₂ : CategoryTheory.Functor C₂ D₂；G : CategoryTheory.Functor D₁ D₂；hG : G.FullyF
aithful。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.LocalizerMorphism.nonempty_fullyFaithful_iff`：nonempty_fu
llyFaithful_iff : Nonempty G.FullyFaithful ↔ Nonempty G'.FullyFaithful
-/
lemma IsLocalizedFullyFaithful.mk' [CatCommSq Φ.functor L₁ L₂ G] (hG : G.FullyFaithful) :
    Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := by
    rw [Φ.nonempty_fullyFaithful_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨hG⟩
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLocalizedEquivalence] : Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- If a `LocalizerMorphism` becomes a fully faithful after localization, then any compatible
functor between the localized categories is fully faithful. -/
/-
**CategoryTheory.LocalizerMorphism.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {D₁ : Type u₄} →       {D₂ : Type 
u₅} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₄, u₄} D₁] →               [inst_3 : CategoryTheory.Category.{v₅, u₅} D₂
] →                 {W₁ : CategoryTheory.MorphismProperty C₁} →                 
  {W₂ : CategoryTheory.MorphismProperty C₂} →                     (Φ : CategoryT
heory.LocalizerMorphism W₁ W₂) →                       (L₁ : CategoryTheory.Func
tor C₁ D₁) →                         [L₁.IsLocalization W₁] →                   
        (L₂ : CategoryTheory.Functor C₂ D₂) →                             [L₂.Is
Localization W₂] →                               (G : CategoryTheory.Functor D₁ 
D₂) →                                 [h : Φ.IsLocalizedFullyFaithful] →        
                           [CategoryTheory.CatCommSq Φ.functor L₁ L₂ G] → G.Full
yFaithful
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₁ : CategoryTheory.Functor C₁ D₁；
L₂ : CategoryTheory.Functor C₂ D₂；G : CategoryTheory.Functor D₁ D₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `LocalizerMorphism` becomes a fully faithful after localization, then any c
ompatible
functor between the localized categories is fully faithful.
-/
@[no_expose] noncomputable def fullyFaithful
    [h : Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.FullyFaithful :=
  Nonempty.some (by
    rw [Φ.nonempty_fullyFaithful_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
    exact h.nonempty_fullyFaithful)
/-
**CategoryTheory.LocalizerMorphism.faithful** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.LocalizerMorphism`。
形式化陈述：faithful [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] : G.Fa
ithful
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
lemma faithful [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Faithful :=
  (Φ.fullyFaithful L₁ L₂ G).faithful
/-
**CategoryTheory.LocalizerMorphism.full** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.LocalizerMorphism`。
形式化陈述：full [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] : G.Full
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
lemma full [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Full :=
  (Φ.fullyFaithful L₁ L₂ G).full

/-- If a `LocalizerMorphism` becomes fully faithful after localization,
then the induced functor on the localized categories is fully faithful. -/
/-
**CategoryTheory.LocalizerMorphism.fullyFaithfulLocalizedFunctor** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {D₁ : Type u₄} →       {D₂ : Type 
u₅} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₄, u₄} D₁] →               [inst_3 : CategoryTheory.Category.{v₅, u₅} D₂
] →                 {W₁ : CategoryTheory.MorphismProperty C₁} →                 
  {W₂ : CategoryTheory.MorphismProperty C₂} →                     (Φ : CategoryT
heory.LocalizerMorphism W₁ W₂) →                       (L₁ : CategoryTheory.Func
tor C₁ D₁) →                         [inst_4 : L₁.IsLocalization W₁] →          
                 (L₂ : CategoryTheory.Functor C₂ D₂) →                          
   [inst_5 : L₂.IsLocalization W₂] →                               [Φ.IsLocalize
dFullyFaithful] → (Φ.localizedFunctor L₁ L₂).FullyFaithful
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；L₁ : CategoryTheory.Functor C₁ D₁；
L₂ : CategoryTheory.Functor C₂ D₂；Φ.localizedFunctor L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `LocalizerMorphism` becomes fully faithful after localization,
then the induced functor on the localized categories is fully faithful.
-/
@[no_expose] noncomputable def fullyFaithfulLocalizedFunctor [Φ.IsLocalizedFullyFaithful] :
    (Φ.localizedFunctor L₁ L₂).FullyFaithful :=
  Φ.fullyFaithful L₁ L₂ _
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Full :=
  Φ.full L₁ L₂ _
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Faithful :=
  Φ.faithful L₁ L₂ _
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsLocalizedFullyFaithful] : Φ.op.IsLocalizedFullyFaithful := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  exact IsLocalizedFullyFaithful.mk' Φ.op W₁.Q.op W₂.Q.op G.op
    (Φ.fullyFaithful W₁.Q W₂.Q G).op

/-- Assume that a localizer morphism `Φ : LocalizerMorphism W₁ W₂` induces
a fully faithful functor on the localized categories.
If `L₂ : C₂ ⥤ D₂` is a localization functor for `W₂` and we have a
factorization `iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F` as an essentially surjective
functor `L₁ : C₁ ⥤ D₁` followed by a fully faithful functor `F : D₁ ⥤ D₂`,
then `L₁` is a localization functor for `W₁`. -/
/-
**CategoryTheory.LocalizerMorphism.isLocalization_of_isLocalizedFullyFaithful** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLocalization_of_isLocalizedFullyFaithful [Φ.IsLocalizedFullyFaithful] {L
₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {L₁ : C₁ ⥤ D₁} {F : D₁ ⥤ D₂} (iso : Φ.functo
r ⋙ L₂ ≅ L₁ ⋙ F) [F.Full] [F.Faithful] [L₁.EssSurj] : L₁.IsLocalization W₁
参数：iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.LocalizerMorphism.map`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{
v₂, u₂} C₂] {W₁ : Category…
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…

--- 原说明 ---
Assume that a localizer morphism `Φ : LocalizerMorphism W₁ W₂` induces
a fully faithful functor on the localized categories.
If `L₂ : C₂ ⥤ D₂` is a localization functor for `W₂` and we have a
factorization `iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F` as an essentially surjective
functor `L₁ : C₁ ⥤ D₁` followed by a fully faithful functor `F : D₁ ⥤ D₂`,
then `L₁` is a localization functor for `W₁`.
-/
lemma isLocalization_of_isLocalizedFullyFaithful
    [Φ.IsLocalizedFullyFaithful] {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]
    {L₁ : C₁ ⥤ D₁} {F : D₁ ⥤ D₂}
    (iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
    [F.Full] [F.Faithful] [L₁.EssSurj] :
    L₁.IsLocalization W₁ := by
  have h : W₁.IsInvertedBy L₁ := fun _ _ f hf ↦ by
    rw [← isIso_iff_of_reflects_iso  _ F]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso iso f)).1 (Localization.inverts L₂ W₂ _ (Φ.map _ hf))
  let G := Localization.lift L₁ h W₁.Q
  let e : W₁.Q ⋙ G ≅ L₁ := Localization.fac L₁ h W₁.Q
  let : CatCommSq Φ.functor W₁.Q L₂ (G ⋙ F) :=
    ⟨iso ≪≫ isoWhiskerRight e.symm _ ≪≫ associator _ _ _⟩
  have hG : G.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (Φ.fullyFaithful W₁.Q L₂ (G ⋙ F))
  have := hG.full
  have := hG.faithful
  have : G.EssSurj :=
    ⟨fun X ↦ ⟨W₁.Q.obj (L₁.objPreimage X), ⟨e.app _ ≪≫ L₁.objObjPreimageIso X⟩⟩⟩
  have : G.IsEquivalence := { }
  exact IsLocalization.of_equivalence_target W₁.Q W₁ L₁ G.asEquivalence e
/-
**CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful.comp** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] [inst_2 : Cat
egoryTheory.Category.{v₃, u₃} C₃]   {W₁ : CategoryTheory.MorphismProperty C₁} {W
₂ : CategoryTheory.MorphismProperty C₂}   {W₃ : CategoryTheory.MorphismProperty 
C₃} (Φ : CategoryTheory.LocalizerMorphism W₁ W₂)   (Ψ : CategoryTheory.Localizer
Morphism W₂ W₃) [Φ.IsLocalizedFullyFaithful] [Ψ.IsLocalizedFullyFaithful],   (Φ.
comp Ψ).IsLocalizedFullyFaithful
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；Ψ : CategoryTheory.LocalizerMorphi
sm W₂ W₃；Φ.comp Ψ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedFullyFaithful.mk'`：∀ {C₁ : T
ype u₁} {C₂ : Type u₂} {D₁ : Type u₄} {D₂ : Type u₅} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
-/
instance IsLocalizedFullyFaithful.comp
    (Ψ : LocalizerMorphism W₂ W₃)
    [Φ.IsLocalizedFullyFaithful] [Ψ.IsLocalizedFullyFaithful] :
    (Φ.comp Ψ).IsLocalizedFullyFaithful :=
  letI : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q
      (Φ.localizedFunctor W₁.Q W₂.Q ⋙ Ψ.localizedFunctor W₂.Q W₃.Q) :=
    CatCommSq.hComp _ _ _ W₂.Q _ _ _
  IsLocalizedFullyFaithful.mk' _ W₁.Q W₃.Q _
    ((Φ.fullyFaithfulLocalizedFunctor W₁.Q W₂.Q).comp
      (Ψ.fullyFaithfulLocalizedFunctor W₂.Q W₃.Q))

/-- The localizer morphism from `W₁.arrow` to `W₂.arrow` that is induced by
`Φ : LocalizerMorphism W₁ W₂`. -/
/-
**CategoryTheory.LocalizerMorphism.arrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.LocalizerMorphism`。
形式化陈述：arrow : LocalizerMorphism W₁.arrow W₂.arrow where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The localizer morphism from `W₁.arrow` to `W₂.arrow` that is induced by
`Φ : LocalizerMorphism W₁ W₂`.
-/
abbrev arrow : LocalizerMorphism W₁.arrow W₂.arrow where
  functor := Φ.functor.mapArrow
  map _ _ _ hf := ⟨Φ.map _ hf.1, Φ.map _ hf.2⟩

/-- If `Φ : LocalizerMorphism W₁ W₂`, the typeclass `Φ.IsInduced`
says that `W₂.inverseImage Φ.functor = W₁`. -/
/-
**CategoryTheory.LocalizerMorphism.IsInduced** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     [inst : CategoryTheory.Category.{v
₁, u₁} C₁] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] →         {W₁ 
: CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.MorphismP
roperty C₂} → CategoryTheory.LocalizerMorphism W₁ W₂ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ : LocalizerMorphism W₁ W₂`, the typeclass `Φ.IsInduced`
says that `W₂.inverseImage Φ.functor = W₁`.
-/
class IsInduced (Φ : LocalizerMorphism W₁ W₂) : Prop where
  inverseImage_eq (Φ) : W₂.inverseImage Φ.functor = W₁

export IsInduced (inverseImage_eq)
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsInduced] : Φ.op.IsInduced where
  inverseImage_eq := by
    simp [← Φ.inverseImage_eq]
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (id W₁).IsInduced where
  inverseImage_eq := rfl
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Ψ : LocalizerMorphism W₂ W₃) [Φ.IsInduced] [Ψ.IsInduced] :
    (Φ.comp Ψ).IsInduced where
  inverseImage_eq := by
    simp [← Φ.inverseImage_eq, ← Ψ.inverseImage_eq]
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.IsInduced] : Φ.arrow.IsInduced where
  inverseImage_eq := by
    simp only [← Φ.inverseImage_eq]
    rfl

section

variable [Φ.functor.IsEquivalence] [Φ.IsInduced] [W₂.RespectsIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.asEquivalence_counitIso_hom_app
  Functor.asEquivalence_counitIso_inv_app in
/-- The inverse of a localizer morphism `Φ : LocalizerMorphism W₁ W₂`,
when `Φ.functor` is an equivalence, `W₁` is induced by `W₂`
and `W₂` respects isomorphisms. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.inv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.LocalizerMorphism`。
形式化陈述：inv : LocalizerMorphism W₂ W₁ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a localizer morphism `Φ : LocalizerMorphism W₁ W₂`,
when `Φ.functor` is an equivalence, `W₁` is induced by `W₂`
and `W₂` respects isomorphisms.
-/
noncomputable def inv : LocalizerMorphism W₂ W₁ where
  functor := Φ.functor.inv
  map := by
    simp only [← Φ.inverseImage_eq]
    intro X Y f hf
    exact (W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))).2 hf

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Φ.inv.functor.IsEquivalence := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.asEquivalence_inverse
  Functor.asEquivalence_counitIso_hom_app Functor.asEquivalence_counitIso_inv_app in
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Φ.inv.IsInduced where
  inverseImage_eq := by
    ext X Y f
    simp only [← Φ.inverseImage_eq]
    exact W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_isInduced** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isLocalizedEquivalence_of_isInduced : Φ.IsLocalizedEquivalence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.of_equivalence`：
∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [
inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LocalizerMorphism.IsInduced.inverseImage_eq`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma isLocalizedEquivalence_of_isInduced :
    Φ.IsLocalizedEquivalence := by
  refine IsLocalizedEquivalence.of_equivalence _ (fun X Y f hf ↦ ?_)
  let e :
      Arrow.mk (Φ.functor.map (Φ.functor.preimage
        ((Φ.functor.objObjPreimageIso X).hom ≫ f ≫ (Φ.functor.objObjPreimageIso Y).inv))) ≅
      Arrow.mk f :=
    Arrow.isoMk (Φ.functor.objObjPreimageIso X) (Φ.functor.objObjPreimageIso Y)
  simp only [← Φ.inverseImage_eq]
  exact ⟨_, _, _, (W₂.arrow_mk_iso_iff e).2 hf, ⟨e⟩⟩

end

end LocalizerMorphism

end CategoryTheory

