/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Preord
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Specialization order

This file defines a type synonym for a topological space considered with its specialisation order.
-/

@[expose] public section

open CategoryTheory Topology

/--
Definition of `Specialization` / `Specialization` 的定义

English:
definition Specialization
  signature: (α : Type*)
  body: α

中文:
定义 Specialization
  签名: (α : 类型)
  定义体: α
-/
def Specialization (α : Type*) := α

namespace Specialization
variable {α β γ : Type*}

/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: : α ≃ Specialization α
  body: Equiv.refl _

中文:
定义 toEquiv
  签名: : α ≃ Specialization α
  定义体: Equiv.refl _
-/
@[match_pattern] def toEquiv : α ≃ Specialization α := Equiv.refl _

/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: : Specialization α ≃ α
  body: Equiv.refl _

中文:
定义 ofEquiv
  签名: : Specialization α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofEquiv : Specialization α ≃ α := Equiv.refl _

/--
lemma `toEquiv_symm` / 引理 `toEquiv_symm`

English:
lemma toEquiv_symm
  statement: (@toEquiv α).symm = ofEquiv
  proof: rfl

中文:
引理 toEquiv_symm
  结论: (@toEquiv α).symm = ofEquiv
  证明: rfl
-/
@[simp] lemma toEquiv_symm : (@toEquiv α).symm = ofEquiv := rfl
/--
lemma `ofEquiv_symm` / 引理 `ofEquiv_symm`

English:
lemma ofEquiv_symm
  statement: (@ofEquiv α).symm = toEquiv
  proof: rfl

中文:
引理 ofEquiv_symm
  结论: (@ofEquiv α).symm = toEquiv
  证明: rfl
-/
@[simp] lemma ofEquiv_symm : (@ofEquiv α).symm = toEquiv := rfl
/--
lemma `toEquiv_ofEquiv` / 引理 `toEquiv_ofEquiv`

English:
lemma toEquiv_ofEquiv
  given: (a : Specialization α)
  statement: toEquiv (ofEquiv a) = a
  proof: rfl

中文:
引理 toEquiv_ofEquiv
  条件: (a : Specialization α)
  结论: toEquiv (ofEquiv a) = a
  证明: rfl
-/
@[simp] lemma toEquiv_ofEquiv (a : Specialization α) : toEquiv (ofEquiv a) = a := rfl
/--
lemma `ofEquiv_toEquiv` / 引理 `ofEquiv_toEquiv`

English:
lemma ofEquiv_toEquiv
  given: (a : α)
  statement: ofEquiv (toEquiv a) = a
  proof: rfl

中文:
引理 ofEquiv_toEquiv
  条件: (a : α)
  结论: ofEquiv (toEquiv a) = a
  证明: rfl
-/
@[simp] lemma ofEquiv_toEquiv (a : α) : ofEquiv (toEquiv a) = a := rfl

-- In Lean 3, `dsimp` would use theorems proved by `Iff.rfl`.
-- If that were still the case, this would useful as a `@[simp]` lemma,
-- despite the fact that it is provable by `simp` (but not `dsimp`).
@[simp, nolint simpNF] -- See https://github.com/leanprover-community/mathlib4/issues/10675
/--
lemma `toEquiv_inj` / 引理 `toEquiv_inj`

English:
lemma toEquiv_inj
  given: {a b : α}
  statement: toEquiv a = toEquiv b ↔ a = b
  proof: Iff.rfl

中文:
引理 toEquiv_inj
  条件: {a b : α}
  结论: toEquiv a = toEquiv b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toEquiv_inj {a b : α} : toEquiv a = toEquiv b ↔ a = b := Iff.rfl

-- In Lean 3, `dsimp` would use theorems proved by `Iff.rfl`.
-- If that were still the case, this would useful as a `@[simp]` lemma,
-- despite the fact that it is provable by `simp` (but not `dsimp`).
@[simp, nolint simpNF] -- See https://github.com/leanprover-community/mathlib4/issues/10675
/--
lemma `ofEquiv_inj` / 引理 `ofEquiv_inj`

English:
lemma ofEquiv_inj
  given: {a b : Specialization α}
  statement: ofEquiv a = ofEquiv b ↔ a = b
  proof: Iff.rfl

中文:
引理 ofEquiv_inj
  条件: {a b : Specialization α}
  结论: ofEquiv a = ofEquiv b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofEquiv_inj {a b : Specialization α} : ofEquiv a = ofEquiv b ↔ a = b :=
  Iff.rfl

/-- A recursor for `Specialization`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {β : Specialization α -> Sort*} (h : forall a, β (toEquiv a)) (a : Specialization α)
  body: h (ofEquiv a)

中文:
定义 rec
  签名: {β : Specialization α -> 类型层*} (h : 对任意 a, β (toEquiv a)) (a : Specialization α)
  定义体: h (ofEquiv a)
-/
protected def rec {β : Specialization α -> Sort*} (h : forall a, β (toEquiv a)) (a : Specialization α) :
    β a :=
  h (ofEquiv a)

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (Specialization α)
  body: fast_instance% specializationPreorder α

中文:
实例 instPreorder
  签名: : 预序 (Specialization α)
  定义体: fast_instance% specializationPreorder α

Depends on / 依赖: fast_instance, specializationPreorder
-/
instance instPreorder : Preorder (Specialization α) :=
  fast_instance% specializationPreorder α

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: [T0Space α]
  body: fast_instance% specializationOrder α

中文:
实例 instPartialOrder
  签名: [T0空间 α]
  定义体: fast_instance% specializationOrder α

Depends on / 依赖: fast_instance, specializationOrder
-/
instance instPartialOrder [T0Space α] : PartialOrder (Specialization α) :=
  fast_instance% specializationOrder α

/--
lemma `toEquiv_le_toEquiv` / 引理 `toEquiv_le_toEquiv`

English:
lemma toEquiv_le_toEquiv
  given: {a b : α}
  statement: toEquiv a <= toEquiv b ↔ b ⤳ a
  proof: Iff.rfl

中文:
引理 toEquiv_le_toEquiv
  条件: {a b : α}
  结论: toEquiv a <= toEquiv b ↔ b ⤳ a
  证明: Iff.rfl
-/
@[simp] lemma toEquiv_le_toEquiv {a b : α} : toEquiv a <= toEquiv b ↔ b ⤳ a := Iff.rfl
/--
lemma `ofEquiv_specializes_ofEquiv` / 引理 `ofEquiv_specializes_ofEquiv`

English:
lemma ofEquiv_specializes_ofEquiv
  given: {a b : Specialization α}
  proof: Iff.rfl

中文:
引理 ofEquiv_specializes_ofEquiv
  条件: {a b : Specialization α}
  证明: Iff.rfl
-/
@[simp] lemma ofEquiv_specializes_ofEquiv {a b : Specialization α} :
    ofEquiv a ⤳ ofEquiv b ↔ b <= a := Iff.rfl

/--
lemma `isOpen_toEquiv_preimage` / 引理 `isOpen_toEquiv_preimage`

English:
lemma isOpen_toEquiv_preimage
  given: [AlexandrovDiscrete α] {s : Set (Specialization α)}
  proof: isOpen_iff_forall_specializes.trans forall_comm

中文:
引理 isOpen_toEquiv_preimage
  条件: [AlexandrovDiscrete α] {s : 集合 (Specialization α)}
  证明: isOpen_iff_forall_specializes.trans forall_comm
-/
@[simp] lemma isOpen_toEquiv_preimage [AlexandrovDiscrete α] {s : Set (Specialization α)} :
    IsOpen (toEquiv ⁻¹' s) ↔ IsUpperSet s := isOpen_iff_forall_specializes.trans forall_comm

/--
lemma `isUpperSet_ofEquiv_preimage` / 引理 `isUpperSet_ofEquiv_preimage`

English:
lemma isUpperSet_ofEquiv_preimage
  given: [AlexandrovDiscrete α] {s : Set α}
  proof: isOpen_toEquiv_preimage.symm

中文:
引理 isUpperSet_ofEquiv_preimage
  条件: [AlexandrovDiscrete α] {s : 集合 α}
  证明: isOpen_toEquiv_preimage.symm
-/
@[simp] lemma isUpperSet_ofEquiv_preimage [AlexandrovDiscrete α] {s : Set α} :
    IsUpperSet (ofEquiv ⁻¹' s) ↔ IsOpen s := isOpen_toEquiv_preimage.symm

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : C(α, β))
  body: toEquiv ∘ f ∘ ofEquiv
  monotone' := (map_continuous f).specialization_monotone

中文:
定义 map
  签名: (f : C(α, β))
  定义体: toEquiv ∘ f ∘ ofEquiv
  monotone' := (map_continuous f).specialization_monotone

Depends on / 依赖: ofEquiv, toEquiv
-/
def map (f : C(α, β)) : Specialization α ->o Specialization β where
  toFun := toEquiv ∘ f ∘ ofEquiv
  monotone' := (map_continuous f).specialization_monotone

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (ContinuousMap.id α) = OrderHom.id
  proof: rfl

中文:
引理 map_id
  结论: map (连续映射.id α) = 序态射.id
  证明: rfl
-/
@[simp] lemma map_id : map (ContinuousMap.id α) = OrderHom.id := rfl
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (g : C(β, γ)) (f : C(α, β))
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

中文:
引理 map_comp
  条件: (g : C(β, γ)) (f : C(α, β))
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl
-/
@[simp] lemma map_comp (g : C(β, γ)) (f : C(α, β)) : map (g.comp f) = (map g).comp (map f) := rfl

end Specialization

open Set Specialization WithUpperSet

/--
Definition of `orderIsoSpecializationWithUpperSetTopology` / `orderIsoSpecializationWithUpperSetTopology` 的定义

English:
definition orderIsoSpecializationWithUpperSetTopology
  signature: (α : Type*) [Preorder α]
  body: toUpperSet.trans toEquiv
  map_rel_iff' := by simp

中文:
定义 orderIsoSpecializationWithUpperSetTopology
  签名: (α : 类型) [预序 α]
  定义体: toUpperSet.trans toEquiv
  map_rel_iff' := by simp

Depends on / 依赖: toEquiv, toUpperSet, toUpperSet.trans
-/
def orderIsoSpecializationWithUpperSetTopology (α : Type*) [Preorder α] :
    α ≃o Specialization (WithUpperSet α) where
  toEquiv := toUpperSet.trans toEquiv
  map_rel_iff' := by simp

/--
Definition of `homeoWithUpperSetTopologyorderIso` / `homeoWithUpperSetTopologyorderIso` 的定义

English:
definition homeoWithUpperSetTopologyorderIso
  signature: (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α]
  body: (toEquiv.trans toUpperSet).toHomeomorph fun s => by simp [Set.preimage_comp]

中文:
定义 homeoWithUpperSetTopologyorderIso
  签名: (α : 类型) [拓扑空间 α] [AlexandrovDiscrete α]
  定义体: (toEquiv.trans toUpperSet).toHomeomorph fun s => by simp [Set.preimage_comp]

Depends on / 依赖: Set.preimage_comp, preimage_comp, toEquiv, toEquiv.trans, toHomeomorph, toUpperSet
-/
def homeoWithUpperSetTopologyorderIso (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
    α ≃ₜ WithUpperSet (Specialization α) :=
  (toEquiv.trans toUpperSet).toHomeomorph fun s => by simp [Set.preimage_comp]

/-- Sends a topological space to its specialisation order. -/
@[simps]
/--
Definition of `topToPreord` / `topToPreord` 的定义

English:
definition topToPreord
  signature: : TopCat ⥤ Preord where
  body: .of Specialization X
map f := Preord.ofHom Specialization.map f.hom

中文:
定义 topToPreord
  签名: : 顶元素范畴 ⥤ 预序 where
  定义体: .of Specialization X
map f := Preord.ofHom Specialization.map f.hom

Depends on / 依赖: Specialization
-/
def topToPreord : TopCat ⥤ Preord where
obj X := .of Specialization X
map f := Preord.ofHom Specialization.map f.hom
