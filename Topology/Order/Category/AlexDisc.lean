/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Specialization

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

@[expose] public section

open CategoryTheory Topology

/--
Definition of `AlexDisc` / `AlexDisc` 的定义

English:
structure AlexDisc
  parameters: extends TopCat
  extends: TopCat
  axioms and operations (1):
    - [is_alexandrovDiscrete : AlexandrovDiscrete carrier]

中文:
结构 AlexDisc
  参数: extends TopCat
  继承: TopCat
  公理与运算 (1 个):
    - [is_alexandrovDiscrete : AlexandrovDiscrete carrier]
-/
structure AlexDisc extends TopCat where
  [is_alexandrovDiscrete : AlexandrovDiscrete carrier]

namespace AlexDisc

attribute [instance] is_alexandrovDiscrete

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort AlexDisc (Type _)
  body: ⟨fun X => X.toTopCat⟩

中文:
实例 :
  签名: CoeSort AlexDisc (Type _)
  定义体: ⟨fun X => X.toTopCat⟩

Depends on / 依赖: X.toTopCat, toTopCat
-/
instance : CoeSort AlexDisc (Type _) :=
  ⟨fun X => X.toTopCat⟩

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category AlexDisc
  body: inferInstanceAs Category (InducedCategory _ toTopCat)

中文:
实例 category
  签名: : Category AlexDisc
  定义体: inferInstanceAs Category (InducedCategory _ toTopCat)

Depends on / 依赖: Category, InducedCategory, toTopCat
-/
instance category : Category AlexDisc :=
inferInstanceAs Category (InducedCategory _ toTopCat)

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory AlexDisc (C(·, ·))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toTopCat) _

中文:
实例 concreteCategory
  签名: : ConcreteCategory AlexDisc (C(·, ·))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toTopCat) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toTopCat
-/
instance concreteCategory : ConcreteCategory AlexDisc (C(·, ·)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toTopCat) _

/--
Instance `instHasForgetToTop` / 实例 `instHasForgetToTop`

English:
instance instHasForgetToTop
  signature: : HasForget₂ AlexDisc TopCat
  body: inferInstanceAs HasForget₂ (InducedCategory _ toTopCat) _

中文:
实例 instHasForgetToTop
  签名: : HasForget₂ AlexDisc TopCat
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toTopCat) _

Depends on / 依赖: InducedCategory, toTopCat
-/
instance instHasForgetToTop : HasForget₂ AlexDisc TopCat :=
inferInstanceAs HasForget₂ (InducedCategory _ toTopCat) _

-- TODO: generalize to `InducedCategory.forget₂_full`?
/--
Instance `forgetToTop_full` / 实例 `forgetToTop_full`

English:
instance forgetToTop_full
  signature: : (forget₂ AlexDisc TopCat).Full where
  body: ⟨InducedCategory.homMk f, rfl⟩

中文:
实例 forgetToTop_full
  签名: : (forget₂ AlexDisc TopCat).Full where
  定义体: ⟨InducedCategory.homMk f, rfl⟩

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
instance forgetToTop_full : (forget₂ AlexDisc TopCat).Full where
  map_surjective f := ⟨InducedCategory.homMk f, rfl⟩

/--
Instance `forgetToTop_faithful` / 实例 `forgetToTop_faithful`

English:
instance forgetToTop_faithful
  signature: : (forget₂ AlexDisc TopCat).Faithful where
  body: by
    ext x
    exact ConcreteCategory.congr_hom h x

中文:
实例 forgetToTop_faithful
  签名: : (forget₂ AlexDisc TopCat).Faithful where
  定义体: by
    ext x
    exact ConcreteCategory.congr_hom h x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
instance forgetToTop_faithful : (forget₂ AlexDisc TopCat).Faithful where
  map_injective {X Y f g} h := by
    ext x
    exact ConcreteCategory.congr_hom h x


/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X]
  body: TopCat.of X

中文:
缩写 of
  签名: (X : 类型) [TopologicalSpace X] [AlexandrovDiscrete X]
  定义体: TopCat.of X

Depends on / 依赖: TopCat, TopCat.of
-/
abbrev of (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X] : AlexDisc where
  toTopCat := TopCat.of X

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α]
  statement: ↥(of α) = α
  proof: rfl

中文:
引理 coe_of
  条件: (α : 类型) [TopologicalSpace α] [AlexandrovDiscrete α]
  结论: ↥(of α) = α
  证明: rfl
-/
lemma coe_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : ↥(of α) = α := rfl

/--
lemma `forgetToTop_of` / 引理 `forgetToTop_of`

English:
lemma forgetToTop_of
  given: (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α]
  proof: rfl

中文:
引理 forgetToTop_of
  条件: (α : 类型) [TopologicalSpace α] [AlexandrovDiscrete α]
  证明: rfl
-/
@[simp] lemma forgetToTop_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
    (forget₂ AlexDisc TopCat).obj (of α) = TopCat.of α := rfl

/--
lemma `coe_forgetToTop` / 引理 `coe_forgetToTop`

English:
lemma coe_forgetToTop
  given: (X : AlexDisc)
  statement: ↥((forget₂ _ TopCat).obj X) = X
  proof: rfl

中文:
引理 coe_forgetToTop
  条件: (X : AlexDisc)
  结论: ↥((forget₂ _ TopCat).obj X) = X
  证明: rfl
-/
@[simp] lemma coe_forgetToTop (X : AlexDisc) : ↥((forget₂ _ TopCat).obj X) = X := rfl

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : AlexDisc} (e : α ≃ₜ β)
  body: ConcreteCategory.ofHom (e : ContinuousMap α β)
  inv := ConcreteCategory.ofHom (e.symm : ContinuousMap β α)
  hom_inv_id := by ext; apply e.symm_apply_apply
  inv_hom_id := by ext; apply e.apply_symm_apply

中文:
定义 Iso.mk
  签名: {α β : AlexDisc} (e : α ≃ₜ β)
  定义体: ConcreteCategory.ofHom (e : ContinuousMap α β)
  inv := ConcreteCategory.ofHom (e.symm : ContinuousMap β α)
  hom_inv_id := by ext; apply e.symm_apply_apply
  inv_hom_id := by ext; apply e.apply_symm_apply
-/
def Iso.mk {α β : AlexDisc} (e : α ≃ₜ β) : α ≅ β where
  hom := ConcreteCategory.ofHom (e : ContinuousMap α β)
  inv := ConcreteCategory.ofHom (e.symm : ContinuousMap β α)
  hom_inv_id := by ext; apply e.symm_apply_apply
  inv_hom_id := by ext; apply e.apply_symm_apply

end AlexDisc

/-- Sends a topological space to its specialisation order. -/
@[simps]
/--
Definition of `alexDiscEquivPreord` / `alexDiscEquivPreord` 的定义

English:
definition alexDiscEquivPreord
  signature: : AlexDisc ≌ Preord where
  body: forget₂ _ _ ⋙ topToPreord
  inverse.obj X := AlexDisc.of (WithUpperSet X)
  inverse.map f := ConcreteCategory.ofHom (WithUpperSet.map f.hom)
unitIso := NatIso.ofComponents fun X => AlexDisc.Iso.mk by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
counitIso := NatIso.ofComponents fun X => Preor

中文:
定义 alexDiscEquivPreord
  签名: : AlexDisc ≌ Preord where
  定义体: forget₂ _ _ ⋙ topToPreord
  inverse.obj X := AlexDisc.of (WithUpperSet X)
  inverse.map f := ConcreteCategory.ofHom (WithUpperSet.map f.hom)
unitIso := NatIso.ofComponents fun X => AlexDisc.Iso.mk by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
counitIso := NatIso.ofComponents fun X => Preor

Depends on / 依赖: topToPreord
-/
def alexDiscEquivPreord : AlexDisc ≌ Preord where
  functor := forget₂ _ _ ⋙ topToPreord
  inverse.obj X := AlexDisc.of (WithUpperSet X)
  inverse.map f := ConcreteCategory.ofHom (WithUpperSet.map f.hom)
unitIso := NatIso.ofComponents fun X => AlexDisc.Iso.mk by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
counitIso := NatIso.ofComponents fun X => Preord.Iso.mk by
    dsimp; exact (orderIsoSpecializationWithUpperSetTopology X).symm
