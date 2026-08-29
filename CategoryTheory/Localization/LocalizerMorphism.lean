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

/--
Definition of `LocalizerMorphism` / `LocalizerMorphism` 的定义

English:
structure LocalizerMorphism
  parameters: where
  axioms and operations (2):
    - functor : C₁ ⥤ C₂
    - map : W₁ <= W₂.inverseImage functor

中文:
结构 Localizer态射
  参数: where
  公理与运算 (2 个):
    - functor : C₁ ⥤ C₂
    - map : W₁ <= W₂.inverseImage functor
-/
structure LocalizerMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ <= W₂.inverseImage functor

namespace LocalizerMorphism

variable {W₁ W₂} in
/-- Constructor for localizer morphisms given by a functor `F : C₁ ⥤ C₂`
under the stronger assumption that the classes of morphisms `W₁` and `W₂`
satisfy `W₁ = W₂.inverseImage F`. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F)
  body: F
  map := by rw [hW]

中文:
定义 ofEq
  签名: {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F)
  定义体: F
  map := by rw [hW]
-/
def ofEq {F : C₁ ⥤ C₂} (hW : W₁ = W₂.inverseImage F) : LocalizerMorphism W₁ W₂ where
  functor := F
  map := by rw [hW]

/-- The identity functor as a morphism of localizers. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : LocalizerMorphism W₁ W₁ where
  body: 𝟭 C₁
  map _ _ _ hf := hf

中文:
定义 id
  签名: : Localizer态射 W₁ W₁ where
  定义体: 𝟭 C₁
  map _ _ _ hf := hf
-/
def id : LocalizerMorphism W₁ W₁ where
  functor := 𝟭 C₁
  map _ _ _ hf := hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (id W₁).functor.IsEquivalence
  body: inferInstanceAs (𝟭 C₁).IsEquivalence

中文:
实例 :
  签名: (id W₁).functor.是等价
  定义体: inferInstanceAs (𝟭 C₁).IsEquivalence

Depends on / 依赖: IsEquivalence
-/
instance : (id W₁).functor.IsEquivalence :=
  inferInstanceAs (𝟭 C₁).IsEquivalence

variable {W₁ W₂ W₃}

/-- The composition of two localizers morphisms. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
  body: Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

中文:
定义 comp
  签名: (Φ : Localizer态射 W₁ W₂) (Ψ : Localizer态射 W₂ W₃)
  定义体: Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

Depends on / 依赖: functor
-/
def comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) :
    LocalizerMorphism W₁ W₃ where
  functor := Φ.functor ⋙ Ψ.functor
  map _ _ _ hf := Ψ.map _ (Φ.map _ hf)

variable (Φ : LocalizerMorphism W₁ W₂)

/--
Definition of `op` / `op` 的定义

English:
abbreviation op
  signature: : LocalizerMorphism W₁.op W₂.op where
  body: Φ.functor.op
  map _ _ _ hf := Φ.map _ hf

中文:
缩写 op
  签名: : Localizer态射 W₁.op W₂.op where
  定义体: Φ.functor.op
  map _ _ _ hf := Φ.map _ hf

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Functor, Functor.map_comp, Functor.map_comp_assoc, Functor.map_id, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, _inv_app, cancel_mono, functor, functor.op, hom_inv_id_app, hom_inv_id_app_assoc, id_comp, inv.app, map_comp, map_comp_assoc, map_id
-/
abbrev op : LocalizerMorphism W₁.op W₂.op where
  functor := Φ.functor.op
  map _ _ _ hf := Φ.map _ hf

variable (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

/--
lemma `inverts` / 引理 `inverts`

English:
lemma inverts
  statement: W₁.IsInvertedBy (Φ.functor ⋙ L₂)
  proof: fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

中文:
引理 inverts
  结论: W₁.IsInvertedBy (Φ.functor ⋙ L₂)
  证明: fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

Depends on / 依赖: Localization, Localization.inverts, inverts
-/
lemma inverts : W₁.IsInvertedBy (Φ.functor ⋙ L₂) :=
  fun _ _ _ hf => Localization.inverts L₂ W₂ _ (Φ.map _ hf)

/--
Definition of `localizedFunctor` / `localizedFunctor` 的定义

English:
definition localizedFunctor
  signature: : D₁ ⥤ D₂
  body: lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

中文:
定义 localizedFunctor
  签名: : D₁ ⥤ D₂
  定义体: lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

Depends on / 依赖: functor, inverts
-/
noncomputable def localizedFunctor : D₁ ⥤ D₂ :=
  lift (Φ.functor ⋙ L₂) (Φ.inverts _) L₁

/--
Instance `liftingLocalizedFunctor` / 实例 `liftingLocalizedFunctor`

English:
instance liftingLocalizedFunctor
  signature: :
  body: inferInstanceAs Lifting L₁ W₁ _ (lift _ _ L₁)

中文:
实例 liftingLocalizedFunctor
  签名: :
  定义体: inferInstanceAs Lifting L₁ W₁ _ (lift _ _ L₁)

Depends on / 依赖: Lifting
-/
noncomputable instance liftingLocalizedFunctor :
    Lifting L₁ W₁ (Φ.functor ⋙ L₂) (Φ.localizedFunctor L₁ L₂) :=
inferInstanceAs Lifting L₁ W₁ _ (lift _ _ L₁)

/--
Instance `catCommSq` / 实例 `catCommSq`

English:
instance catCommSq
  signature: : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂)
  body: CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

中文:
实例 catCommSq
  签名: : CatCommSq Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂)
  定义体: CatCommSq.mk (Lifting.iso _ W₁ _ _).symm

Depends on / 依赖: CatCommSq, CatCommSq.mk, Lifting, Lifting.iso
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

/--
lemma `isEquivalence_imp` / 引理 `isEquivalence_imp`

English:
lemma isEquivalence_imp
  given: [G.IsEquivalence]
  statement: G'.IsEquivalence
  proof: let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G)

中文:
引理 isEquivalence_imp
  条件: [G.是等价]
  结论: G'.是等价
  证明: let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G)

Depends on / 依赖: CatCommSq, CatCommSq.iso, Localization, Localization.uniq, associator, compUniqFunctor, functor, isoWhiskerLeft, isoWhiskerRight
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

/--
lemma `isEquivalence_iff` / 引理 `isEquivalence_iff`

English:
lemma isEquivalence_iff
  statement: G.IsEquivalence ↔ G'.IsEquivalence
  proof: ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

中文:
引理 isEquivalence_iff
  结论: G.是等价 ↔ G'.是等价
  证明: ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

Depends on / 依赖: isEquivalence_imp
-/
lemma isEquivalence_iff : G.IsEquivalence ↔ G'.IsEquivalence :=
  ⟨fun _ => Φ.isEquivalence_imp L₁ L₂ G L₁' L₂' G',
    fun _ => Φ.isEquivalence_imp L₁' L₂' G' L₁ L₂ G⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def fullyFaithfulImp (hG : G.FullyFaithful)
  body: let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G)

中文:
定义 noncomputable
  签名: def fullyFaithfulImp (hG : G.满忠实)
  定义体: let E₁ := Localization.uniq L₁ L₁' W₁
  let E₂ := Localization.uniq L₂ L₂' W₂
  let e : L₁ ⋙ G ⋙ E₂.functor ≅ L₁ ⋙ E₁.functor ⋙ G' :=
    calc
      L₁ ⋙ G ⋙ E₂.functor ≅ Φ.functor ⋙ L₂ ⋙ E₂.functor :=
          (associator _ _ _).symm ≪≫
            isoWhiskerRight (CatCommSq.iso Φ.functor L₁ L₂ G)
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

/--
lemma `nonempty_fullyFaithful_iff` / 引理 `nonempty_fullyFaithful_iff`

English:
lemma nonempty_fullyFaithful_iff
  statement: Nonempty G.FullyFaithful ↔ Nonempty G'.FullyFaithful
  proof: ⟨fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁ L₂ G L₁' L₂' G' h⟩,
    fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁' L₂' G' L₁ L₂ G h⟩⟩

中文:
引理 nonempty_fullyFaithful_iff
  结论: 非空 G.满忠实 ↔ 非空 G'.满忠实
  证明: ⟨fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁ L₂ G L₁' L₂' G' h⟩,
    fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁' L₂' G' L₁ L₂ G h⟩⟩

Depends on / 依赖: fullyFaithfulImp
-/
lemma nonempty_fullyFaithful_iff : Nonempty G.FullyFaithful ↔ Nonempty G'.FullyFaithful :=
  ⟨fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁ L₂ G L₁' L₂' G' h⟩,
    fun ⟨h⟩ => ⟨Φ.fullyFaithfulImp L₁' L₂' G' L₁ L₂ G h⟩⟩

end

/--
Definition of `IsLocalizedEquivalence` / `IsLocalizedEquivalence` 的定义

English:
class IsLocalizedEquivalence
  parameters: : Prop where
  axioms and operations (1):
    - isEquivalence : (Φ.localizedFunctor W₁.Q W₂.Q).IsEquivalence

中文:
类 是LocalizedEquivalence
  参数: : 命题 where
  公理与运算 (1 个):
    - isEquivalence : (Φ.localizedFunctor W₁.Q W₂.Q).是等价
-/
class IsLocalizedEquivalence : Prop where
  /-- the induced functor on the constructed localized categories is an equivalence -/
  isEquivalence : (Φ.localizedFunctor W₁.Q W₂.Q).IsEquivalence

/--
lemma `IsLocalizedEquivalence.mk'` / 引理 `IsLocalizedEquivalence.mk'`

English:
lemma IsLocalizedEquivalence.mk'
  given: [CatCommSq Φ.functor L₁ L₂ G] [G.IsEquivalence]
  proof: by
    rw [Φ.isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact inferInstance

中文:
引理 是LocalizedEquivalence.mk'
  条件: [CatCommSq Φ.functor L₁ L₂ G] [G.是等价]
  证明: by
    rw [Φ.isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact inferInstance

Depends on / 依赖: isEquivalence_iff, localizedFunctor
-/
lemma IsLocalizedEquivalence.mk' [CatCommSq Φ.functor L₁ L₂ G] [G.IsEquivalence] :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    rw [Φ.isEquivalence_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact inferInstance

/--
lemma `isEquivalence` / 引理 `isEquivalence`

English:
lemma isEquivalence
  given: [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G]
  proof: (by
  rw [Φ.isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.isEquivalence)

中文:
引理 isEquivalence
  条件: [h : Φ.是LocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G]
  证明: (by
  rw [Φ.isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.isEquivalence)

Depends on / 依赖: h.isEquivalence, isEquivalence, isEquivalence_iff, localizedFunctor
-/
lemma isEquivalence [h : Φ.IsLocalizedEquivalence] [CatCommSq Φ.functor L₁ L₂ G] :
    G.IsEquivalence := (by
  rw [Φ.isEquivalence_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
  exact h.isEquivalence)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLocalizedEquivalence]
  signature: : Φ.op.IsLocalizedEquivalence
  body: by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have := Φ.isEquivalence W₁.Q W₂.Q G
  exact IsLocalizedEquivalence.mk' Φ.op W₁.Q.op W₂.Q.op G.op

中文:
实例 [Φ.是LocalizedEquivalence]
  签名: : Φ.op.是LocalizedEquivalence
  定义体: by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have := Φ.isEquivalence W₁.Q W₂.Q G
  exact IsLocalizedEquivalence.mk' Φ.op W₁.Q.op W₂.Q.op G.op

Depends on / 依赖: CatCommSq, CatCommSq.iso, G.op, IsLocalizedEquivalence, IsLocalizedEquivalence.mk, NatIso, NatIso.op, Q.op, functor, isEquivalence, localizedFunctor, op.functor
-/
instance [Φ.IsLocalizedEquivalence] : Φ.op.IsLocalizedEquivalence := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have := Φ.isEquivalence W₁.Q W₂.Q G
  exact IsLocalizedEquivalence.mk' Φ.op W₁.Q.op W₂.Q.op G.op

/--
Instance `localizedFunctor_isEquivalence` / 实例 `localizedFunctor_isEquivalence`

English:
instance localizedFunctor_isEquivalence
  signature: [Φ.IsLocalizedEquivalence]
  body: Φ.isEquivalence L₁ L₂ _

中文:
实例 localizedFunctor_isEquivalence
  签名: [Φ.是LocalizedEquivalence]
  定义体: Φ.isEquivalence L₁ L₂ _

Depends on / 依赖: isEquivalence
-/
instance localizedFunctor_isEquivalence [Φ.IsLocalizedEquivalence] :
    (Φ.localizedFunctor L₁ L₂).IsEquivalence :=
  Φ.isEquivalence L₁ L₂ _

/--
lemma `IsLocalizedEquivalence.of_isLocalization_of_isLocalization` / 引理 `IsLocalizedEquivalence.of_isLocalization_of_isLocalization`

English:
lemma IsLocalizedEquivalence.of_isLocalization_of_isLocalization
  proof: by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

中文:
引理 是LocalizedEquivalence.of_isLocalization_of_isLocalization
  证明: by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

Depends on / 依赖: CatCommSq, CatCommSq.mk, IsLocalizedEquivalence, IsLocalizedEquivalence.mk, functor, rightUnitor
-/
lemma IsLocalizedEquivalence.of_isLocalization_of_isLocalization
    [(Φ.functor ⋙ L₂).IsLocalization W₁] :
    IsLocalizedEquivalence Φ := by
  have : CatCommSq Φ.functor (Φ.functor ⋙ L₂) L₂ (𝟭 D₂) :=
    CatCommSq.mk (rightUnitor _).symm
  exact IsLocalizedEquivalence.mk' Φ (Φ.functor ⋙ L₂) L₂ (𝟭 D₂)

/--
lemma `IsLocalizedEquivalence.of_equivalence` / 引理 `IsLocalizedEquivalence.of_equivalence`

English:
lemma IsLocalizedEquivalence.of_equivalence
  statement: [Φ.functor.IsEquivalence]
  proof: by
  have : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).sy

中文:
引理 是LocalizedEquivalence.of_equivalence
  结论: [Φ.functor.是等价]
  证明: by
  have : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).sy

Depends on / 依赖: Equivalence, Equivalence.unitIso, Functor, Functor.IsLocalization, Functor.IsLocalization.of_equivalence_source, IsLocalization, IsLocalizedEquivalence, IsLocalizedEquivalence.of_isLocalization_of_isLocalization, MorphismProperty, MorphismProperty.Q, MorphismProperty.map_isoClosure, asEquivalence, associator, functor, inverseImage_equivalence_functor_eq_map_inverse, inverts, isoClosure, isoClosure.inverseImage_equivalence_functor_eq_map_inverse, isoWhiskerRight, leftUnitor
-/
lemma IsLocalizedEquivalence.of_equivalence [Φ.functor.IsEquivalence]
    (h : W₂ <= W₁.map Φ.functor) : IsLocalizedEquivalence Φ := by
  have : Functor.IsLocalization (Φ.functor ⋙ MorphismProperty.Q W₂) W₁ := by
    refine Functor.IsLocalization.of_equivalence_source W₂.Q W₂ (Φ.functor ⋙ W₂.Q) W₁
      (asEquivalence Φ.functor).symm ?_ (Φ.inverts W₂.Q)
      ((associator _ _ _).symm ≪≫ isoWhiskerRight ((Equivalence.unitIso _).symm) _ ≪≫
        leftUnitor _)
    erw [W₁.isoClosure.inverseImage_equivalence_functor_eq_map_inverse]
    rw [MorphismProperty.map_isoClosure]
    exact h
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

/--
Instance `IsLocalizedEquivalence.isLocalization` / 实例 `IsLocalizedEquivalence.isLocalization`

English:
instance IsLocalizedEquivalence.isLocalization
  signature: [Φ.IsLocalizedEquivalence]
  body: Functor.IsLocalization.of_iso _ ((Φ.catCommSq W₁.Q L₂).iso).symm

中文:
实例 是LocalizedEquivalence.isLocalization
  签名: [Φ.是LocalizedEquivalence]
  定义体: Functor.IsLocalization.of_iso _ ((Φ.catCommSq W₁.Q L₂).iso).symm

Depends on / 依赖: Functor, Functor.IsLocalization.of_iso, IsLocalization, catCommSq, of_iso
-/
instance IsLocalizedEquivalence.isLocalization [Φ.IsLocalizedEquivalence] :
    (Φ.functor ⋙ L₂).IsLocalization W₁ :=
  Functor.IsLocalization.of_iso _ ((Φ.catCommSq W₁.Q L₂).iso).symm

/--
lemma `isLocalizedEquivalence_of_unit_of_unit` / 引理 `isLocalizedEquivalence_of_unit_of_unit`

English:
lemma isLocalizedEquivalence_of_unit_of_unit
  statement: (Ψ : LocalizerMorphism W₂ W₁)
  proof: by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₂.Q W₂ _ (hε₂ _)
    r

中文:
引理 isLocalizedEquivalence_of_unit_of_unit
  结论: (Ψ : Localizer态射 W₂ W₁)
  证明: by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₂.Q W₂ _ (hε₂ _)
    r

Depends on / 依赖: Functor, Functor.associator, Localization, Localization.equivalence, Localization.inverts, NatTrans, NatTrans.isIso_iff_isIso_app, associator, equivalence, functor, inverts, isEquivalence_functor, isIso_iff_isIso_app, isoWhiskerLeft, localizedFunctor, whiskerRight
-/
lemma isLocalizedEquivalence_of_unit_of_unit (Ψ : LocalizerMorphism W₂ W₁)
    (ε₁ : 𝟭 C₁ ⟶ Φ.functor ⋙ Ψ.functor) (ε₂ : 𝟭 C₂ ⟶ Ψ.functor ⋙ Φ.functor)
    (hε₁ : forall X₁, W₁ (ε₁.app X₁)) (hε₂ : forall X₂, W₂ (ε₂.app X₂)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₂.Q W₂ _ (hε₂ _)
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

/--
Instance `IsLocalizedEquivalence.id` / 实例 `IsLocalizedEquivalence.id`

English:
instance IsLocalizedEquivalence.id
  signature: :
  body: have : ((LocalizerMorphism.id W₁).functor ⋙ W₁.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  of_isLocalization_of_isLocalization _ W₁.Q

中文:
实例 是LocalizedEquivalence.id
  签名: :
  定义体: have : ((LocalizerMorphism.id W₁).functor ⋙ W₁.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  of_isLocalization_of_isLocalization _ W₁.Q

Depends on / 依赖: Functor, Functor.IsLocalization.of_iso, Functor.leftUnitor, IsLocalization, LocalizerMorphism, LocalizerMorphism.id, functor, leftUnitor, of_isLocalization_of_isLocalization, of_iso
-/
instance IsLocalizedEquivalence.id :
    (id W₁).IsLocalizedEquivalence :=
  have : ((LocalizerMorphism.id W₁).functor ⋙ W₁.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.leftUnitor _).symm
  of_isLocalization_of_isLocalization _ W₁.Q

/--
Instance `IsLocalizedEquivalence.comp` / 实例 `IsLocalizedEquivalence.comp`

English:
instance IsLocalizedEquivalence.comp
  signature: [Φ.IsLocalizedEquivalence]
  body: have : ((Φ.comp Ψ).functor ⋙ W₃.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.associator _ _ _).symm
  of_isLocalization_of_isLocalization _ W₃.Q

中文:
实例 是LocalizedEquivalence.comp
  签名: [Φ.是LocalizedEquivalence]
  定义体: have : ((Φ.comp Ψ).functor ⋙ W₃.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.associator _ _ _).symm
  of_isLocalization_of_isLocalization _ W₃.Q

Depends on / 依赖: Functor, Functor.IsLocalization.of_iso, Functor.associator, IsLocalization, associator, functor, of_isLocalization_of_isLocalization, of_iso
-/
instance IsLocalizedEquivalence.comp [Φ.IsLocalizedEquivalence]
    (Ψ : LocalizerMorphism W₂ W₃)
    [Ψ.IsLocalizedEquivalence] :
    (Φ.comp Ψ).IsLocalizedEquivalence :=
  have : ((Φ.comp Ψ).functor ⋙ W₃.Q).IsLocalization W₁ :=
    Functor.IsLocalization.of_iso _ (Functor.associator _ _ _).symm
  of_isLocalization_of_isLocalization _ W₃.Q

/--
Definition of `IsLocalizedFullyFaithful` / `IsLocalizedFullyFaithful` 的定义

English:
class IsLocalizedFullyFaithful
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_fullyFaithful : Nonempty (Φ.localizedFunctor W₁.Q W₂.Q).FullyFaithful

中文:
类 是LocalizedFullyFaithful
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_fullyFaithful : 非空 (Φ.localizedFunctor W₁.Q W₂.Q).满忠实
-/
class IsLocalizedFullyFaithful : Prop where
  /-- the induced functor on the constructed localized categories is fully faithful -/
  nonempty_fullyFaithful : Nonempty (Φ.localizedFunctor W₁.Q W₂.Q).FullyFaithful

/--
lemma `IsLocalizedFullyFaithful.mk'` / 引理 `IsLocalizedFullyFaithful.mk'`

English:
lemma IsLocalizedFullyFaithful.mk'
  given: [CatCommSq Φ.functor L₁ L₂ G] (hG : G.FullyFaithful)
  proof: by
    rw [Φ.nonempty_fullyFaithful_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨hG⟩

中文:
引理 是LocalizedFullyFaithful.mk'
  条件: [CatCommSq Φ.functor L₁ L₂ G] (hG : G.满忠实)
  证明: by
    rw [Φ.nonempty_fullyFaithful_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨hG⟩

Depends on / 依赖: localizedFunctor, nonempty_fullyFaithful_iff
-/
lemma IsLocalizedFullyFaithful.mk' [CatCommSq Φ.functor L₁ L₂ G] (hG : G.FullyFaithful) :
    Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := by
    rw [Φ.nonempty_fullyFaithful_iff W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q) L₁ L₂ G]
    exact ⟨hG⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLocalizedEquivalence]
  signature: : Φ.IsLocalizedFullyFaithful where
  body: ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

中文:
实例 [Φ.是LocalizedEquivalence]
  签名: : Φ.是LocalizedFullyFaithful where
  定义体: ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, ofFullyFaithful
-/
instance [Φ.IsLocalizedEquivalence] : Φ.IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
definition fullyFaithful
  body: Nonempty.some (by
    rw [Φ.nonempty_fullyFaithful_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
    exact h.nonempty_fullyFaithful)

中文:
定义 fullyFaithful
  定义体: Nonempty.some (by
    rw [Φ.nonempty_fullyFaithful_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
    exact h.nonempty_fullyFaithful)
-/
@[no_expose] noncomputable def fullyFaithful
    [h : Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.FullyFaithful :=
  Nonempty.some (by
    rw [Φ.nonempty_fullyFaithful_iff L₁ L₂ G W₁.Q W₂.Q (Φ.localizedFunctor W₁.Q W₂.Q)]
    exact h.nonempty_fullyFaithful)

/--
lemma `faithful` / 引理 `faithful`

English:
lemma faithful
  given: [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G]
  proof: (Φ.fullyFaithful L₁ L₂ G).faithful

中文:
引理 faithful
  条件: [Φ.是LocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G]
  证明: (Φ.fullyFaithful L₁ L₂ G).faithful

Depends on / 依赖: faithful, fullyFaithful
-/
lemma faithful [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Faithful :=
  (Φ.fullyFaithful L₁ L₂ G).faithful

/--
lemma `full` / 引理 `full`

English:
lemma full
  given: [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G]
  proof: (Φ.fullyFaithful L₁ L₂ G).full

中文:
引理 full
  条件: [Φ.是LocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G]
  证明: (Φ.fullyFaithful L₁ L₂ G).full

Depends on / 依赖: fullyFaithful, isoZero, shiftFunctorZero
-/
lemma full [Φ.IsLocalizedFullyFaithful] [CatCommSq Φ.functor L₁ L₂ G] :
    G.Full :=
  (Φ.fullyFaithful L₁ L₂ G).full

/--
Definition of `fullyFaithfulLocalizedFunctor` / `fullyFaithfulLocalizedFunctor` 的定义

English:
definition fullyFaithfulLocalizedFunctor
  signature: [Φ.IsLocalizedFullyFaithful]
  body: Φ.fullyFaithful L₁ L₂ _

中文:
定义 fullyFaithfulLocalizedFunctor
  签名: [Φ.是LocalizedFullyFaithful]
  定义体: Φ.fullyFaithful L₁ L₂ _
-/
@[no_expose] noncomputable def fullyFaithfulLocalizedFunctor [Φ.IsLocalizedFullyFaithful] :
    (Φ.localizedFunctor L₁ L₂).FullyFaithful :=
  Φ.fullyFaithful L₁ L₂ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLocalizedFullyFaithful]
  signature: : (Φ.localizedFunctor L₁ L₂).Full
  body: Φ.full L₁ L₂ _

中文:
实例 [Φ.是LocalizedFullyFaithful]
  签名: : (Φ.localizedFunctor L₁ L₂).满
  定义体: Φ.full L₁ L₂ _
-/
instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Full :=
  Φ.full L₁ L₂ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLocalizedFullyFaithful]
  signature: : (Φ.localizedFunctor L₁ L₂).Faithful
  body: Φ.faithful L₁ L₂ _

中文:
实例 [Φ.是LocalizedFullyFaithful]
  签名: : (Φ.localizedFunctor L₁ L₂).忠实
  定义体: Φ.faithful L₁ L₂ _

Depends on / 依赖: faithful
-/
instance [Φ.IsLocalizedFullyFaithful] : (Φ.localizedFunctor L₁ L₂).Faithful :=
  Φ.faithful L₁ L₂ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLocalizedFullyFaithful]
  signature: : Φ.op.IsLocalizedFullyFaithful
  body: by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  exact IsLocalizedFullyFaithful.mk' Φ.op W₁.Q.op W₂.Q.op G.op
    (Φ.fullyFaithful W₁.Q W₂.Q G).op

中文:
实例 [Φ.是LocalizedFullyFaithful]
  签名: : Φ.op.是LocalizedFullyFaithful
  定义体: by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  exact IsLocalizedFullyFaithful.mk' Φ.op W₁.Q.op W₂.Q.op G.op
    (Φ.fullyFaithful W₁.Q W₂.Q G).op

Depends on / 依赖: CatCommSq, CatCommSq.iso, G.op, IsLocalizedFullyFaithful, IsLocalizedFullyFaithful.mk, NatIso, NatIso.op, Q.op, fullyFaithful, functor, localizedFunctor, op.functor
-/
instance [Φ.IsLocalizedFullyFaithful] : Φ.op.IsLocalizedFullyFaithful := by
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  exact IsLocalizedFullyFaithful.mk' Φ.op W₁.Q.op W₂.Q.op G.op
    (Φ.fullyFaithful W₁.Q W₂.Q G).op

/--
lemma `isLocalization_of_isLocalizedFullyFaithful` / 引理 `isLocalization_of_isLocalizedFullyFaithful`

English:
lemma isLocalization_of_isLocalizedFullyFaithful
  proof: by
  have h : W₁.IsInvertedBy L₁ := fun _ _ f hf => by
    rw [← isIso_iff_of_reflects_iso _ F]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso iso f)).1 (Localization.inverts L₂ W₂ _ (Φ.map _ hf))
  let G := Localization.lift L₁ h W₁.Q
  let e : W₁.Q ⋙ G ≅ L₁ 

中文:
引理 isLocalization_of_isLocalizedFullyFaithful
  证明: by
  have h : W₁.IsInvertedBy L₁ := fun _ _ f hf => by
    rw [← isIso_iff_of_reflects_iso _ F]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso iso f)).1 (Localization.inverts L₂ W₂ _ (Φ.map _ hf))
  let G := Localization.lift L₁ h W₁.Q
  let e : W₁.Q ⋙ G ≅ L₁ 

Depends on / 依赖: Arrow.isoOfNatIso, CatCommSq, FullyFaithful, Functor, Functor.FullyFaithful.ofCompFaithful, Functor.map_comp_assoc, G.FullyFaithful, IsInvertedBy, Localization, Localization.fac, Localization.inverts, Localization.lift, MorphismProperty, MorphismProperty.isomorphisms, _add_zero_hom_app, _add_zero_inv_app, arrow_mk_iso_iff, associator, e.symm, fullyFaithful
-/
lemma isLocalization_of_isLocalizedFullyFaithful
    [Φ.IsLocalizedFullyFaithful] {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂]
    {L₁ : C₁ ⥤ D₁} {F : D₁ ⥤ D₂}
    (iso : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
    [F.Full] [F.Faithful] [L₁.EssSurj] :
    L₁.IsLocalization W₁ := by
  have h : W₁.IsInvertedBy L₁ := fun _ _ f hf => by
    rw [← isIso_iff_of_reflects_iso _ F]
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
    ⟨fun X => ⟨W₁.Q.obj (L₁.objPreimage X), ⟨e.app _ ≪≫ L₁.objObjPreimageIso X⟩⟩⟩
  have : G.IsEquivalence := { }
  exact IsLocalization.of_equivalence_target W₁.Q W₁ L₁ G.asEquivalence e

/--
Instance `IsLocalizedFullyFaithful.comp` / 实例 `IsLocalizedFullyFaithful.comp`

English:
instance IsLocalizedFullyFaithful.comp
  body: letI : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q
      (Φ.localizedFunctor W₁.Q W₂.Q ⋙ Ψ.localizedFunctor W₂.Q W₃.Q) :=
    CatCommSq.hComp _ _ _ W₂.Q _ _ _
  IsLocalizedFullyFaithful.mk' _ W₁.Q W₃.Q _
    ((Φ.fullyFaithfulLocalizedFunctor W₁.Q W₂.Q).comp
      (Ψ.fullyFaithfulLocalizedFunctor W₂.Q W₃.

中文:
实例 是LocalizedFullyFaithful.comp
  定义体: letI : CatCommSq (Φ.comp Ψ).functor W₁.Q W₃.Q
      (Φ.localizedFunctor W₁.Q W₂.Q ⋙ Ψ.localizedFunctor W₂.Q W₃.Q) :=
    CatCommSq.hComp _ _ _ W₂.Q _ _ _
  IsLocalizedFullyFaithful.mk' _ W₁.Q W₃.Q _
    ((Φ.fullyFaithfulLocalizedFunctor W₁.Q W₂.Q).comp
      (Ψ.fullyFaithfulLocalizedFunctor W₂.Q W₃.

Depends on / 依赖: CatCommSq, CatCommSq.hComp, IsLocalizedFullyFaithful, IsLocalizedFullyFaithful.mk, fullyFaithfulLocalizedFunctor, functor, localizedFunctor
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

/--
Definition of `arrow` / `arrow` 的定义

English:
abbreviation arrow
  signature: : LocalizerMorphism W₁.arrow W₂.arrow where
  body: Φ.functor.mapArrow
  map _ _ _ hf := ⟨Φ.map _ hf.1, Φ.map _ hf.2⟩

中文:
缩写 arrow
  签名: : Localizer态射 W₁.arrow W₂.arrow where
  定义体: Φ.functor.mapArrow
  map _ _ _ hf := ⟨Φ.map _ hf.1, Φ.map _ hf.2⟩

Depends on / 依赖: Category, Category.assoc, F.map_comp_assoc, Functor, Functor.map_comp_assoc, NatTrans, NatTrans.naturality_2, NatTrans.naturality_assoc, _assoc_hom_app, _assoc_inv_app, _hom_app, ec.hom, functor, functor.mapArrow, isoAdd, mapArrow, map_comp_assoc, naturality_2, naturality_assoc, shiftFunctorAdd
-/
abbrev arrow : LocalizerMorphism W₁.arrow W₂.arrow where
  functor := Φ.functor.mapArrow
  map _ _ _ hf := ⟨Φ.map _ hf.1, Φ.map _ hf.2⟩

/--
Definition of `IsInduced` / `IsInduced` 的定义

English:
class IsInduced
  parameters: (Φ : LocalizerMorphism W₁ W₂)
  axioms and operations (1):
    - inverseImage_eq((Φ)) : W₂.inverseImage Φ.functor = W₁

中文:
类 是Induced
  参数: (Φ : Localizer态射 W₁ W₂)
  公理与运算 (1 个):
    - inverseImage_eq((Φ)) : W₂.inverseImage Φ.functor = W₁
-/
class IsInduced (Φ : LocalizerMorphism W₁ W₂) : Prop where
  inverseImage_eq (Φ) : W₂.inverseImage Φ.functor = W₁

export IsInduced (inverseImage_eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsInduced]
  signature: : Φ.op.IsInduced where
  body: by
    simp [← Φ.inverseImage_eq]

中文:
实例 [Φ.是Induced]
  签名: : Φ.op.是Induced where
  定义体: by
    simp [← Φ.inverseImage_eq]

Depends on / 依赖: inverseImage_eq
-/
instance [Φ.IsInduced] : Φ.op.IsInduced where
  inverseImage_eq := by
    simp [← Φ.inverseImage_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (id W₁).IsInduced
  body: rfl

中文:
实例 :
  签名: (id W₁).是Induced
  定义体: rfl
-/
instance : (id W₁).IsInduced where
  inverseImage_eq := rfl

instance (Ψ : LocalizerMorphism W₂ W₃) [Φ.IsInduced] [Ψ.IsInduced] :
    (Φ.comp Ψ).IsInduced where
  inverseImage_eq := by
    simp [← Φ.inverseImage_eq, ← Ψ.inverseImage_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsInduced]
  signature: : Φ.arrow.IsInduced where
  body: by
    simp only [← Φ.inverseImage_eq]
    rfl

中文:
实例 [Φ.是Induced]
  签名: : Φ.arrow.是Induced where
  定义体: by
    simp only [← Φ.inverseImage_eq]
    rfl

Depends on / 依赖: inverseImage_eq
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
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : LocalizerMorphism W₂ W₁ where
  body: Φ.functor.inv
  map := by
    simp only [← Φ.inverseImage_eq]
    intro X Y f hf
    exact (W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))).2 hf

中文:
定义 inv
  签名: : Localizer态射 W₂ W₁ where
  定义体: Φ.functor.inv
  map := by
    simp only [← Φ.inverseImage_eq]
    intro X Y f hf
    exact (W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))).2 hf

Depends on / 依赖: functor, functor.inv
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Φ.inv.functor.IsEquivalence
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: Φ.inv.functor.是等价
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Φ.inv.functor.IsEquivalence := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Functor.asEquivalence_inverse
  Functor.asEquivalence_counitIso_hom_app Functor.asEquivalence_counitIso_inv_app in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Φ.inv.IsInduced
  body: by
    ext X Y f
    simp only [← Φ.inverseImage_eq]
    exact W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))

中文:
实例 :
  签名: Φ.inv.是Induced
  定义体: by
    ext X Y f
    simp only [← Φ.inverseImage_eq]
    exact W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))

Depends on / 依赖: Arrow.isoMk, arrow_mk_iso_iff, asEquivalence, counitIso, functor, functor.asEquivalence.counitIso.app, inverseImage_eq
-/
instance : Φ.inv.IsInduced where
  inverseImage_eq := by
    ext X Y f
    simp only [← Φ.inverseImage_eq]
    exact W₂.arrow_mk_iso_iff
      (Arrow.isoMk (Φ.functor.asEquivalence.counitIso.app _)
        (Φ.functor.asEquivalence.counitIso.app _))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isLocalizedEquivalence_of_isInduced` / 引理 `isLocalizedEquivalence_of_isInduced`

English:
lemma isLocalizedEquivalence_of_isInduced
  proof: by
  refine IsLocalizedEquivalence.of_equivalence _ (fun X Y f hf => ?_)
  let e :
      Arrow.mk (Φ.functor.map (Φ.functor.preimage
        ((Φ.functor.objObjPreimageIso X).hom ≫ f ≫ (Φ.functor.objObjPreimageIso Y).inv))) ≅
      Arrow.mk f :=
    Arrow.isoMk (Φ.functor.objObjPreimageIso X) (Φ.func

中文:
引理 isLocalizedEquivalence_of_isInduced
  证明: by
  refine IsLocalizedEquivalence.of_equivalence _ (fun X Y f hf => ?_)
  let e :
      Arrow.mk (Φ.functor.map (Φ.functor.preimage
        ((Φ.functor.objObjPreimageIso X).hom ≫ f ≫ (Φ.functor.objObjPreimageIso Y).inv))) ≅
      Arrow.mk f :=
    Arrow.isoMk (Φ.functor.objObjPreimageIso X) (Φ.func

Depends on / 依赖: Arrow.isoMk, Arrow.mk, IsLocalizedEquivalence, IsLocalizedEquivalence.of_equivalence, arrow_mk_iso_iff, functor, functor.map, functor.objObjPreimageIso, functor.preimage, inverseImage_eq, objObjPreimageIso, of_equivalence, preimage
-/
lemma isLocalizedEquivalence_of_isInduced :
    Φ.IsLocalizedEquivalence := by
  refine IsLocalizedEquivalence.of_equivalence _ (fun X Y f hf => ?_)
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
