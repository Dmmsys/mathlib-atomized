/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen, Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, coproducts,
and composition, with dual statements for the right lifting property.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

/--
Definition of `llp` / `llp` 的定义

English:
definition llp
  signature: : MorphismProperty C
  body: fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

中文:
定义 llp
  签名: : Morphism命题erty C
  定义体: fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g
-/
def llp : MorphismProperty C := fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

/--
Definition of `rlp` / `rlp` 的定义

English:
definition rlp
  signature: : MorphismProperty C
  body: fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

中文:
定义 rlp
  签名: : Morphism命题erty C
  定义体: fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f
-/
def rlp : MorphismProperty C := fun _ _ f =>
  forall ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

/--
lemma `llp_of_isIso` / 引理 `llp_of_isIso`

English:
lemma llp_of_isIso
  given: {A B : C} (i : A ⟶ B) [IsIso i]
  proof: fun _ _ _ _ => inferInstance

中文:
引理 llp_of_isIso
  条件: {A B : C} (i : A ⟶ B) [IsIso i]
  证明: fun _ _ _ _ => inferInstance
-/
lemma llp_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] :
    T.llp i :=
  fun _ _ _ _ => inferInstance

/--
lemma `rlp_of_isIso` / 引理 `rlp_of_isIso`

English:
lemma rlp_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  proof: fun _ _ _ _ => inferInstance

中文:
引理 rlp_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f]
  证明: fun _ _ _ _ => inferInstance
-/
lemma rlp_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    T.rlp f :=
  fun _ _ _ _ => inferInstance

/--
Instance `llp_isStableUnderRetracts` / 实例 `llp_isStableUnderRetracts`

English:
instance llp_isStableUnderRetracts
  signature: : T.llp.IsStableUnderRetracts where
  body: letI := hg _ hf
    h.leftLiftingProperty f

中文:
实例 llp_isStableUnderRetracts
  签名: : T.llp.IsStableUnderRetracts where
  定义体: letI := hg _ hf
    h.leftLiftingProperty f

Depends on / 依赖: h.leftLiftingProperty, leftLiftingProperty
-/
instance llp_isStableUnderRetracts : T.llp.IsStableUnderRetracts where
  of_retract h hg _ _ f hf :=
    letI := hg _ hf
    h.leftLiftingProperty f

/--
Instance `rlp_isStableUnderRetracts` / 实例 `rlp_isStableUnderRetracts`

English:
instance rlp_isStableUnderRetracts
  signature: : T.rlp.IsStableUnderRetracts where
  body: letI := hf _ hg
    h.rightLiftingProperty g

中文:
实例 rlp_isStableUnderRetracts
  签名: : T.rlp.IsStableUnderRetracts where
  定义体: letI := hf _ hg
    h.rightLiftingProperty g

Depends on / 依赖: h.rightLiftingProperty, rightLiftingProperty
-/
instance rlp_isStableUnderRetracts : T.rlp.IsStableUnderRetracts where
  of_retract h hf _ _ g hg :=
    letI := hf _ hg
    h.rightLiftingProperty g

/--
Instance `llp_isStableUnderCobaseChange` / 实例 `llp_isStableUnderCobaseChange`

English:
instance llp_isStableUnderCobaseChange
  signature: : T.llp.IsStableUnderCobaseChange where
  body: letI := hf _ hg'
    h.hasLiftingProperty g'

中文:
实例 llp_isStableUnderCobaseChange
  签名: : T.llp.IsStableUnderCobaseChange where
  定义体: letI := hf _ hg'
    h.hasLiftingProperty g'

Depends on / 依赖: h.hasLiftingProperty, hasLiftingProperty
-/
instance llp_isStableUnderCobaseChange : T.llp.IsStableUnderCobaseChange where
  of_isPushout h hf _ _ g' hg' :=
    letI := hf _ hg'
    h.hasLiftingProperty g'

open IsPullback in
/--
Instance `rlp_isStableUnderBaseChange` / 实例 `rlp_isStableUnderBaseChange`

English:
instance rlp_isStableUnderBaseChange
  signature: : T.rlp.IsStableUnderBaseChange where
  body: letI := hf _ hf'
    h.hasLiftingProperty f'

中文:
实例 rlp_isStableUnderBaseChange
  签名: : T.rlp.IsStableUnderBaseChange where
  定义体: letI := hf _ hf'
    h.hasLiftingProperty f'

Depends on / 依赖: h.hasLiftingProperty, hasLiftingProperty
-/
instance rlp_isStableUnderBaseChange : T.rlp.IsStableUnderBaseChange where
  of_isPullback h hf _ _ f' hf' :=
    letI := hf _ hf'
    h.hasLiftingProperty f'

/--
Instance `llp_isMultiplicative` / 实例 `llp_isMultiplicative`

English:
instance llp_isMultiplicative
  signature: : T.llp.IsMultiplicative where
  body: by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

中文:
实例 llp_isMultiplicative
  签名: : T.llp.IsMultiplicative where
  定义体: by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

Depends on / 依赖: comp_mem, infer_instance
-/
instance llp_isMultiplicative : T.llp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

/--
Instance `rlp_isMultiplicative` / 实例 `rlp_isMultiplicative`

English:
instance rlp_isMultiplicative
  signature: : T.rlp.IsMultiplicative where
  body: by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

中文:
实例 rlp_isMultiplicative
  签名: : T.rlp.IsMultiplicative where
  定义体: by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

Depends on / 依赖: comp_mem, infer_instance
-/
instance rlp_isMultiplicative : T.rlp.IsMultiplicative where
  id_mem X _ _ p hp := by infer_instance
  comp_mem i j hi hj _ _ p hp := by
    have := hi _ hp
    have := hj _ hp
    infer_instance

/--
Instance `llp_isStableUnderCoproductsOfShape` / 实例 `llp_isStableUnderCoproductsOfShape`

English:
instance llp_isStableUnderCoproductsOfShape
  signature: (J : Type*)
  body: by
  apply IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

中文:
实例 llp_isStableUnderCoproductsOfShape
  签名: (J : 类型)
  定义体: by
  apply IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

Depends on / 依赖: IsStableUnderCoproductsOfShape, IsStableUnderCoproductsOfShape.mk, infer_instance
-/
instance llp_isStableUnderCoproductsOfShape (J : Type*) :
    T.llp.IsStableUnderCoproductsOfShape J := by
  apply IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderCoproducts.{w} T.llp

中文:
实例 :
  签名: IsStableUnderCoproducts.{w} T.llp
-/
instance : IsStableUnderCoproducts.{w} T.llp where

/--
Instance `rlp_isStableUnderProductsOfShape` / 实例 `rlp_isStableUnderProductsOfShape`

English:
instance rlp_isStableUnderProductsOfShape
  signature: (J : Type*)
  body: by
  apply IsStableUnderProductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

中文:
实例 rlp_isStableUnderProductsOfShape
  签名: (J : 类型)
  定义体: by
  apply IsStableUnderProductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

Depends on / 依赖: IsStableUnderProductsOfShape, IsStableUnderProductsOfShape.mk, infer_instance
-/
instance rlp_isStableUnderProductsOfShape (J : Type*) :
    T.rlp.IsStableUnderProductsOfShape J := by
  apply IsStableUnderProductsOfShape.mk
  intro A B _ _ f hf X Y p hp
  have := fun j => hf j _ hp
  infer_instance

/--
lemma `le_llp_iff_le_rlp` / 引理 `le_llp_iff_le_rlp`

English:
lemma le_llp_iff_le_rlp
  given: (T' : MorphismProperty C)
  proof: ⟨fun h _ _ _ hp _ _ _ hi => h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp => h _ hp _ hi⟩

中文:
引理 le_llp_iff_le_rlp
  条件: (T' : Morphism命题erty C)
  证明: ⟨fun h _ _ _ hp _ _ _ hi => h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp => h _ hp _ hi⟩
-/
lemma le_llp_iff_le_rlp (T' : MorphismProperty C) :
    T <= T'.llp ↔ T' <= T.rlp :=
  ⟨fun h _ _ _ hp _ _ _ hi => h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp => h _ hp _ hi⟩

/--
lemma `gc_llp_rlp` / 引理 `gc_llp_rlp`

English:
lemma gc_llp_rlp
  proof: fun _ _ => le_llp_iff_le_rlp _ _

中文:
引理 gc_llp_rlp
  证明: fun _ _ => le_llp_iff_le_rlp _ _

Depends on / 依赖: MorphismProperty
-/
lemma gc_llp_rlp :
    GaloisConnection (OrderDual.toDual (α := MorphismProperty C) ∘ llp)
      (rlp ∘ OrderDual.ofDual) :=
  fun _ _ => le_llp_iff_le_rlp _ _

/--
lemma `le_llp_rlp` / 引理 `le_llp_rlp`

English:
lemma le_llp_rlp
  statement: T <= T.rlp.llp
  proof: by
  rw [le_llp_iff_le_rlp]

@[simp]

中文:
引理 le_llp_rlp
  结论: T <= T.rlp.llp
  证明: by
  rw [le_llp_iff_le_rlp]

@[simp]

Depends on / 依赖: le_llp_iff_le_rlp
-/
lemma le_llp_rlp : T <= T.rlp.llp := by
  rw [le_llp_iff_le_rlp]

@[simp]
/--
lemma `rlp_llp_rlp` / 引理 `rlp_llp_rlp`

English:
lemma rlp_llp_rlp
  statement: T.rlp.llp.rlp = T.rlp
  proof: gc_llp_rlp.u_l_u_eq_u T

@[simp]

中文:
引理 rlp_llp_rlp
  结论: T.rlp.llp.rlp = T.rlp
  证明: gc_llp_rlp.u_l_u_eq_u T

@[simp]

Depends on / 依赖: gc_llp_rlp, gc_llp_rlp.u_l_u_eq_u, u_l_u_eq_u
-/
lemma rlp_llp_rlp : T.rlp.llp.rlp = T.rlp :=
  gc_llp_rlp.u_l_u_eq_u T

@[simp]
/--
lemma `llp_rlp_llp` / 引理 `llp_rlp_llp`

English:
lemma llp_rlp_llp
  statement: T.llp.rlp.llp = T.llp
  proof: gc_llp_rlp.l_u_l_eq_l T

中文:
引理 llp_rlp_llp
  结论: T.llp.rlp.llp = T.llp
  证明: gc_llp_rlp.l_u_l_eq_l T

Depends on / 依赖: gc_llp_rlp, gc_llp_rlp.l_u_l_eq_l, l_u_l_eq_l
-/
lemma llp_rlp_llp : T.llp.rlp.llp = T.llp :=
  gc_llp_rlp.l_u_l_eq_l T

/--
lemma `antitone_rlp` / 引理 `antitone_rlp`

English:
lemma antitone_rlp
  statement: Antitone (rlp : MorphismProperty C -> _)
  proof: fun _ _ h => gc_llp_rlp.monotone_u h

中文:
引理 antitone_rlp
  结论: Antitone (rlp : Morphism命题erty C -> _)
  证明: fun _ _ h => gc_llp_rlp.monotone_u h

Depends on / 依赖: gc_llp_rlp, gc_llp_rlp.monotone_u, monotone_u
-/
lemma antitone_rlp : Antitone (rlp : MorphismProperty C -> _) :=
  fun _ _ h => gc_llp_rlp.monotone_u h

/--
lemma `antitone_llp` / 引理 `antitone_llp`

English:
lemma antitone_llp
  statement: Antitone (llp : MorphismProperty C -> _)
  proof: fun _ _ h => gc_llp_rlp.monotone_l h

中文:
引理 antitone_llp
  结论: Antitone (llp : Morphism命题erty C -> _)
  证明: fun _ _ h => gc_llp_rlp.monotone_l h

Depends on / 依赖: gc_llp_rlp, gc_llp_rlp.monotone_l, monotone_l
-/
lemma antitone_llp : Antitone (llp : MorphismProperty C -> _) :=
  fun _ _ h => gc_llp_rlp.monotone_l h

/--
lemma `pushouts_le_llp_rlp` / 引理 `pushouts_le_llp_rlp`

English:
lemma pushouts_le_llp_rlp
  statement: T.pushouts <= T.rlp.llp
  proof: by
  intro A B i hi
  exact (T.rlp.llp.isStableUnderCobaseChange_iff_pushouts_le).1 inferInstance i
    (pushouts_monotone T.le_llp_rlp _ hi)

@[simp]

中文:
引理 pushouts_le_llp_rlp
  结论: T.pushouts <= T.rlp.llp
  证明: by
  intro A B i hi
  exact (T.rlp.llp.isStableUnderCobaseChange_iff_pushouts_le).1 inferInstance i
    (pushouts_monotone T.le_llp_rlp _ hi)

@[simp]

Depends on / 依赖: T.le_llp_rlp, T.rlp.llp.isStableUnderCobaseChange_iff_pushouts_le, isStableUnderCobaseChange_iff_pushouts_le, le_llp_rlp, pushouts_monotone
-/
lemma pushouts_le_llp_rlp : T.pushouts <= T.rlp.llp := by
  intro A B i hi
  exact (T.rlp.llp.isStableUnderCobaseChange_iff_pushouts_le).1 inferInstance i
    (pushouts_monotone T.le_llp_rlp _ hi)

@[simp]
/--
lemma `rlp_pushouts` / 引理 `rlp_pushouts`

English:
lemma rlp_pushouts
  statement: T.pushouts.rlp = T.rlp
  proof: by
  apply le_antisymm
  · exact antitone_rlp T.le_pushouts
  · rw [← le_llp_iff_le_rlp]
    exact T.pushouts_le_llp_rlp

中文:
引理 rlp_pushouts
  结论: T.pushouts.rlp = T.rlp
  证明: by
  apply le_antisymm
  · exact antitone_rlp T.le_pushouts
  · rw [← le_llp_iff_le_rlp]
    exact T.pushouts_le_llp_rlp

Depends on / 依赖: T.le_pushouts, T.pushouts_le_llp_rlp, antitone_rlp, le_antisymm, le_llp_iff_le_rlp, le_pushouts, pushouts_le_llp_rlp
-/
lemma rlp_pushouts : T.pushouts.rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_pushouts
  · rw [← le_llp_iff_le_rlp]
    exact T.pushouts_le_llp_rlp

/--
lemma `colimitsOfShape_discrete_le_llp_rlp` / 引理 `colimitsOfShape_discrete_le_llp_rlp`

English:
lemma colimitsOfShape_discrete_le_llp_rlp
  given: (J : Type w)
  proof: by
  intro A B i hi
  exact MorphismProperty.colimitsOfShape_le _ (colimitsOfShape_monotone T.le_llp_rlp _ _ hi)

中文:
引理 colimitsOfShape_discrete_le_llp_rlp
  条件: (J : Type w)
  证明: by
  intro A B i hi
  exact MorphismProperty.colimitsOfShape_le _ (colimitsOfShape_monotone T.le_llp_rlp _ _ hi)

Depends on / 依赖: MorphismProperty, MorphismProperty.colimitsOfShape_le, T.le_llp_rlp, colimitsOfShape_le, colimitsOfShape_monotone, le_llp_rlp
-/
lemma colimitsOfShape_discrete_le_llp_rlp (J : Type w) :
    T.colimitsOfShape (Discrete J) <= T.rlp.llp := by
  intro A B i hi
  exact MorphismProperty.colimitsOfShape_le _ (colimitsOfShape_monotone T.le_llp_rlp _ _ hi)

/--
lemma `coproducts_le_llp_rlp` / 引理 `coproducts_le_llp_rlp`

English:
lemma coproducts_le_llp_rlp
  statement: (coproducts.{w} T) <= T.rlp.llp
  proof: by
  intro A B i hi
  rw [coproducts_iff] at hi
  obtain ⟨J, hi⟩ := hi
  exact T.colimitsOfShape_discrete_le_llp_rlp J _ hi

@[simp]

中文:
引理 coproducts_le_llp_rlp
  结论: (coproducts.{w} T) <= T.rlp.llp
  证明: by
  intro A B i hi
  rw [coproducts_iff] at hi
  obtain ⟨J, hi⟩ := hi
  exact T.colimitsOfShape_discrete_le_llp_rlp J _ hi

@[simp]

Depends on / 依赖: T.colimitsOfShape_discrete_le_llp_rlp, colimitsOfShape_discrete_le_llp_rlp, coproducts_iff
-/
lemma coproducts_le_llp_rlp : (coproducts.{w} T) <= T.rlp.llp := by
  intro A B i hi
  rw [coproducts_iff] at hi
  obtain ⟨J, hi⟩ := hi
  exact T.colimitsOfShape_discrete_le_llp_rlp J _ hi

@[simp]
/--
lemma `rlp_coproducts` / 引理 `rlp_coproducts`

English:
lemma rlp_coproducts
  statement: (coproducts.{w} T).rlp = T.rlp
  proof: by
  apply le_antisymm
  · exact antitone_rlp T.le_coproducts
  · rw [← le_llp_iff_le_rlp]
    exact T.coproducts_le_llp_rlp

中文:
引理 rlp_coproducts
  结论: (coproducts.{w} T).rlp = T.rlp
  证明: by
  apply le_antisymm
  · exact antitone_rlp T.le_coproducts
  · rw [← le_llp_iff_le_rlp]
    exact T.coproducts_le_llp_rlp

Depends on / 依赖: T.coproducts_le_llp_rlp, T.le_coproducts, antitone_rlp, coproducts_le_llp_rlp, le_antisymm, le_coproducts, le_llp_iff_le_rlp
-/
lemma rlp_coproducts : (coproducts.{w} T).rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_coproducts
  · rw [← le_llp_iff_le_rlp]
    exact T.coproducts_le_llp_rlp

/--
lemma `retracts_le_llp_rlp` / 引理 `retracts_le_llp_rlp`

English:
lemma retracts_le_llp_rlp
  statement: T.retracts <= T.rlp.llp
  proof: le_trans (retracts_monotone T.le_llp_rlp) T.rlp.llp.retracts_le

@[simp]

中文:
引理 retracts_le_llp_rlp
  结论: T.retracts <= T.rlp.llp
  证明: le_trans (retracts_monotone T.le_llp_rlp) T.rlp.llp.retracts_le

@[simp]

Depends on / 依赖: T.le_llp_rlp, T.rlp.llp.retracts_le, le_llp_rlp, le_trans, retracts_le, retracts_monotone
-/
lemma retracts_le_llp_rlp : T.retracts <= T.rlp.llp :=
  le_trans (retracts_monotone T.le_llp_rlp) T.rlp.llp.retracts_le

@[simp]
/--
lemma `rlp_retracts` / 引理 `rlp_retracts`

English:
lemma rlp_retracts
  statement: T.retracts.rlp = T.rlp
  proof: by
  apply le_antisymm
  · exact antitone_rlp T.le_retracts
  · rw [← le_llp_iff_le_rlp]
    exact T.retracts_le_llp_rlp

中文:
引理 rlp_retracts
  结论: T.retracts.rlp = T.rlp
  证明: by
  apply le_antisymm
  · exact antitone_rlp T.le_retracts
  · rw [← le_llp_iff_le_rlp]
    exact T.retracts_le_llp_rlp

Depends on / 依赖: T.le_retracts, T.retracts_le_llp_rlp, antitone_rlp, le_antisymm, le_llp_iff_le_rlp, le_retracts, retracts_le_llp_rlp
-/
lemma rlp_retracts : T.retracts.rlp = T.rlp := by
  apply le_antisymm
  · exact antitone_rlp T.le_retracts
  · rw [← le_llp_iff_le_rlp]
    exact T.retracts_le_llp_rlp

/--
lemma `rlp_ofHoms_iff_hasLiftingProperty` / 引理 `rlp_ofHoms_iff_hasLiftingProperty`

English:
lemma rlp_ofHoms_iff_hasLiftingProperty
  statement: (ι : Type*) [Nonempty ι] {A B X Y : C}
  proof: ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

中文:
引理 rlp_ofHoms_iff_hasLiftingProperty
  结论: (ι : 类型) [Nonempty ι] {A B X Y : C}
  证明: ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
lemma rlp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun (_ : ι) => i)).rlp p ↔ HasLiftingProperty i p :=
  ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

/--
lemma `llp_ofHoms_iff_hasLiftingProperty` / 引理 `llp_ofHoms_iff_hasLiftingProperty`

English:
lemma llp_ofHoms_iff_hasLiftingProperty
  statement: (ι : Type*) [Nonempty ι] {A B X Y : C}
  proof: ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

中文:
引理 llp_ofHoms_iff_hasLiftingProperty
  结论: (ι : 类型) [Nonempty ι] {A B X Y : C}
  证明: ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
lemma llp_ofHoms_iff_hasLiftingProperty (ι : Type*) [Nonempty ι] {A B X Y : C}
    (i : A ⟶ B) (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun (_ : ι) => p)).llp i ↔ HasLiftingProperty i p :=
  ⟨fun hp => hp _ ⟨Classical.arbitrary ι⟩,
    by rintro _ _ _ _ ⟨⟩; assumption⟩

end MorphismProperty

/--
lemma `Functor.hasLiftingProperty_iff_of_isEquivalence` / 引理 `Functor.hasLiftingProperty_iff_of_isEquivalence`

English:
lemma Functor.hasLiftingProperty_iff_of_isEquivalence
  proof: by
  #adaptation_note /-- Prior to nightly-2026-05-07, the next three lines were just
  ```
  simp only [dsimp% G.asEquivalence.toAdjunction.hasLiftingProperty_iff,
    ← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  ```
  This is a temporary repair, and authors/maintainers are encourag

中文:
引理 Functor.hasLiftingProperty_iff_of_isEquivalence
  证明: by
  #adaptation_note /-- Prior to nightly-2026-05-07, the next three lines were just
  ```
  simp only [dsimp% G.asEquivalence.toAdjunction.hasLiftingProperty_iff,
    ← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  ```
  This is a temporary repair, and authors/maintainers are encourag

Depends on / 依赖: G.asEquivalenc, G.asEquivalence.functor.map, G.asEquivalence.toAdjunction.hasLiftingProperty_iff, HasLiftingProperty, MorphismProperty, MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty, adaptation_note, asEquivalenc, asEquivalence, authors, better, either, encouraged, example, functor, hasLiftingProperty_iff, identify, maintainers, minimal, nightly
-/
lemma Functor.hasLiftingProperty_iff_of_isEquivalence
    {D : Type*} [Category* D] (G : C ⥤ D) [G.IsEquivalence]
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (G.map i) (G.map p) ↔
      HasLiftingProperty i p := by
  #adaptation_note /-- Prior to nightly-2026-05-07, the next three lines were just
  ```
  simp only [dsimp% G.asEquivalence.toAdjunction.hasLiftingProperty_iff,
    ← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  ```
  This is a temporary repair, and authors/maintainers are encouraged to either find a better repair,
  or identify a minimal example of an underlying problem in Lean.
  -/
  change HasLiftingProperty (G.asEquivalence.functor.map i) (G.asEquivalence.functor.map p) ↔ _
  rw [G.asEquivalence.toAdjunction.hasLiftingProperty_iff]
  simp only [← MorphismProperty.rlp_ofHoms_iff_hasLiftingProperty Unit]
  exact MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (G.asEquivalence.unitIso.symm.app _)
      (G.asEquivalence.unitIso.symm.app _)
      (G.asEquivalence.unitIso.inv.naturality p).symm)

end CategoryTheory
