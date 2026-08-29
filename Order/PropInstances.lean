/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Disjoint

/-!

# The order on `Prop`

Instances on `Prop` such as `DistribLattice`, `BoundedOrder`, `LinearOrder`.

-/

public section

/--
Instance `Prop.instDistribLattice` / 实例 `Prop.instDistribLattice`

English:
instance Prop.instDistribLattice
  signature: : DistribLattice Prop where
  body: Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

中文:
实例 命题.instDistribLattice
  签名: : Distrib格 命题 where
  定义体: Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

Depends on / 依赖: _eq_of_eq, toLocalizationMap
-/
instance Prop.instDistribLattice : DistribLattice Prop where
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

/--
Instance `Prop.instBoundedOrder` / 实例 `Prop.instBoundedOrder`

English:
instance Prop.instBoundedOrder
  signature: : BoundedOrder Prop where
  body: True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

@[simp]

中文:
实例 命题.instBoundedOrder
  签名: : 有界序 命题 where
  定义体: True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

@[simp]

Depends on / 依赖: _eq_of_eq, toLocalizationMap
-/
instance Prop.instBoundedOrder : BoundedOrder Prop where
  top := True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

@[simp]
/--
theorem `Prop.bot_eq_false` / 定理 `Prop.bot_eq_false`

English:
theorem Prop.bot_eq_false
  statement: (⊥ : Prop) = False
  proof: rfl

@[simp]

中文:
定理 命题.bot_eq_false
  结论: (⊥ : 命题) = 假
  证明: rfl

@[simp]

Depends on / 依赖: _cancel, toLocalizationMap
-/
theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl

@[simp]
/--
theorem `Prop.top_eq_true` / 定理 `Prop.top_eq_true`

English:
theorem Prop.top_eq_true
  statement: (⊤ : Prop) = True
  proof: rfl

中文:
定理 命题.top_eq_true
  结论: (⊤ : 命题) = 真
  证明: rfl

Depends on / 依赖: _self, toLocalizationMap
-/
theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl

/--
Instance `Prop.le_total` / 实例 `Prop.le_total`

English:
instance Prop.le_total
  signature: : @Std.Total Prop (· <= ·)
  body: ⟨fun p q => by by_cases h : q <;> simp [h]⟩

中文:
实例 命题.le_total
  签名: : @Std.全 命题 (· <= ·)
  定义体: ⟨fun p q => by by_cases h : q <;> simp [h]⟩

Depends on / 依赖: _self, toLocalizationMap
-/
instance Prop.le_total : @Std.Total Prop (· <= ·) :=
  ⟨fun p q => by by_cases h : q <;> simp [h]⟩

/--
Instance `Prop.linearOrder` / 实例 `Prop.linearOrder`

English:
instance Prop.linearOrder
  signature: : LinearOrder Prop
  body: by
  classical
  exact Lattice.toLinearOrder Prop

@[simp]

中文:
实例 命题.linearOrder
  签名: : 线性序 命题
  定义体: by
  classical
  exact Lattice.toLinearOrder Prop

@[simp]

Depends on / 依赖: Lattice, Lattice.toLinearOrder, _self, classical, toLinearOrder
-/
noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical
  exact Lattice.toLinearOrder Prop

@[simp]
/--
theorem `sup_Prop_eq` / 定理 `sup_Prop_eq`

English:
theorem sup_Prop_eq
  statement: (· ⊔ ·) = (· ∨ ·)
  proof: rfl

@[simp]

中文:
定理 sup_Prop_eq
  结论: (· ⊔ ·) = (· ∨ ·)
  证明: rfl

@[simp]
-/
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl

@[simp]
/--
theorem `inf_Prop_eq` / 定理 `inf_Prop_eq`

English:
theorem inf_Prop_eq
  statement: (· ⊓ ·) = (· ∧ ·)
  proof: rfl

中文:
定理 inf_Prop_eq
  结论: (· ⊓ ·) = (· ∧ ·)
  证明: rfl

Depends on / 依赖: _one_eq_mk, mul_mk, toLocalizationMap
-/
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl

namespace Pi

variable {ι α : Type*} {α' : ι -> Type*} [forall i, PartialOrder (α' i)]

/--
theorem `disjoint_iff` / 定理 `disjoint_iff`

English:
theorem disjoint_iff
  given: [forall i, OrderBot (α' i)] {f g : forall i, α' i}
  proof: by
  classical
  constructor
  · intro h i x hf hg
    exact (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => bot_le⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => bot_le⟩)).1
  · intro h x hf hg i
    apply h i (hf i) (hg i)

中文:
定理 disjoint_iff
  条件: [对任意 i, 有底序 (α' i)] {f g : 对任意 i, α' i}
  证明: by
  classical
  constructor
  · intro h i x hf hg
    exact (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => bot_le⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => bot_le⟩)).1
  · intro h x hf hg i
    apply h i (hf i) (hg i)

Depends on / 依赖: _mul_cancel_left, bot_le, classical, toLocalizationMap, update_le_iff, update_le_iff.mp, update_le_iff.mpr
-/
theorem disjoint_iff [forall i, OrderBot (α' i)] {f g : forall i, α' i} :
    Disjoint f g ↔ forall i, Disjoint (f i) (g i) := by
  classical
  constructor
  · intro h i x hf hg
    exact (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => bot_le⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => bot_le⟩)).1
  · intro h x hf hg i
    apply h i (hf i) (hg i)

/--
theorem `codisjoint_iff` / 定理 `codisjoint_iff`

English:
theorem codisjoint_iff
  given: [forall i, OrderTop (α' i)] {f g : forall i, α' i}
  proof: @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _

中文:
定理 codisjoint_iff
  条件: [对任意 i, 有顶序 (α' i)] {f g : 对任意 i, α' i}
  证明: @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _

Depends on / 依赖: _mul_cancel_right, disjoint_iff, toLocalizationMap
-/
theorem codisjoint_iff [forall i, OrderTop (α' i)] {f g : forall i, α' i} :
    Codisjoint f g ↔ forall i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _

/--
theorem `isCompl_iff` / 定理 `isCompl_iff`

English:
theorem isCompl_iff
  given: [forall i, BoundedOrder (α' i)] {f g : forall i, α' i}
  proof: by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]

中文:
定理 isCompl_iff
  条件: [对任意 i, 有界序 (α' i)] {f g : 对任意 i, α' i}
  证明: by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]

Depends on / 依赖: _mul, _root_, _root_.isCompl_iff, _self, codisjoint_iff, disjoint_iff, forall_and, isCompl_iff, mul_comm, simp_rw
-/
theorem isCompl_iff [forall i, BoundedOrder (α' i)] {f g : forall i, α' i} :
    IsCompl f g ↔ forall i, IsCompl (f i) (g i) := by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]

instance (α : Type*) : Std.Symm (α := α) ⊤ where
  symm _ _ := id

instance (α : Type*) : Std.Symm (α := α) ⊥ where
  symm _ _ := id

@[nontriviality]
/--
theorem `eq_top_iff_refl_of_subsingleton` / 定理 `eq_top_iff_refl_of_subsingleton`

English:
theorem eq_top_iff_refl_of_subsingleton
  given: [Subsingleton α] {r : α -> α -> Prop}
  statement: r = ⊤ ↔ Std.Refl r
  proof: ⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [rel_of_subsingleton]⟩

@[nontriviality]

中文:
定理 eq_top_iff_refl_of_subsingleton
  条件: [子单例 α] {r : α -> α -> 命题}
  结论: r = ⊤ ↔ Std.Refl r
  证明: ⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [rel_of_subsingleton]⟩

@[nontriviality]

Depends on / 依赖: _eq_one, _mul_mk, rel_of_subsingleton
-/
theorem eq_top_iff_refl_of_subsingleton [Subsingleton α] {r : α -> α -> Prop} : r = ⊤ ↔ Std.Refl r :=
⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [rel_of_subsingleton]⟩

@[nontriviality]
/--
theorem `eq_bot_iff_irrefl_of_subsingleton` / 定理 `eq_bot_iff_irrefl_of_subsingleton`

English:
theorem eq_bot_iff_irrefl_of_subsingleton
  given: [Subsingleton α] {r : α -> α -> Prop}
  proof: ⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [not_rel_of_subsingleton]⟩

中文:
定理 eq_bot_iff_irrefl_of_subsingleton
  条件: [子单例 α] {r : α -> α -> 命题}
  证明: ⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [not_rel_of_subsingleton]⟩

Depends on / 依赖: not_rel_of_subsingleton
-/
theorem eq_bot_iff_irrefl_of_subsingleton [Subsingleton α] {r : α -> α -> Prop} :
    r = ⊥ ↔ Std.Irrefl r :=
⟨fun h => ⟨by simp [h]⟩, fun _ => funext₂ by simp [not_rel_of_subsingleton]⟩

end Pi

@[simp]
/--
theorem `Prop.disjoint_iff` / 定理 `Prop.disjoint_iff`

English:
theorem Prop.disjoint_iff
  given: {P Q : Prop}
  statement: Disjoint P Q ↔ ¬(P ∧ Q)
  proof: disjoint_iff_inf_le

@[simp]

中文:
定理 命题.disjoint_iff
  条件: {P Q : 命题}
  结论: Disjoint P Q ↔ ¬(P ∧ Q)
  证明: disjoint_iff_inf_le

@[simp]

Depends on / 依赖: disjoint_iff_inf_le
-/
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le

@[simp]
/--
theorem `Prop.codisjoint_iff` / 定理 `Prop.codisjoint_iff`

English:
theorem Prop.codisjoint_iff
  given: {P Q : Prop}
  statement: Codisjoint P Q ↔ P ∨ Q
  proof: codisjoint_iff_le_sup.trans forall_const True

@[simp]

中文:
定理 命题.codisjoint_iff
  条件: {P Q : 命题}
  结论: Codisjoint P Q ↔ P ∨ Q
  证明: codisjoint_iff_le_sup.trans forall_const True

@[simp]

Depends on / 依赖: codisjoint_iff_le_sup, codisjoint_iff_le_sup.trans, forall_const
-/
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
codisjoint_iff_le_sup.trans forall_const True

@[simp]
/--
theorem `Prop.isCompl_iff` / 定理 `Prop.isCompl_iff`

English:
theorem Prop.isCompl_iff
  given: {P Q : Prop}
  statement: IsCompl P Q ↔ ¬(P ↔ Q)
  proof: by
  rw [_root_.isCompl_iff]; rw [Prop.disjoint_iff]; rw [Prop.codisjoint_iff]; rw [not_iff]
  by_cases P <;> by_cases Q <;> simp [*]

中文:
定理 命题.isCompl_iff
  条件: {P Q : 命题}
  结论: 是补集 P Q ↔ ¬(P ↔ Q)
  证明: by
  rw [_root_.isCompl_iff]; rw [Prop.disjoint_iff]; rw [Prop.codisjoint_iff]; rw [not_iff]
  by_cases P <;> by_cases Q <;> simp [*]

Depends on / 依赖: Prop.codisjoint_iff, Prop.disjoint_iff, _root_, _root_.isCompl_iff, codisjoint_iff, disjoint_iff, isCompl_iff, not_iff
-/
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [_root_.isCompl_iff]; rw [Prop.disjoint_iff]; rw [Prop.codisjoint_iff]; rw [not_iff]
  by_cases P <;> by_cases Q <;> simp [*]

section decidable_instances

universe u
variable {α : Type u}

/--
Instance `Prop.decidablePredBot` / 实例 `Prop.decidablePredBot`

English:
instance Prop.decidablePredBot
  signature: : DecidablePred (⊥ : α -> Prop)
  body: fun _ => instDecidableFalse

中文:
实例 命题.decidablePredBot
  签名: : DecidablePred (⊥ : α -> 命题)
  定义体: fun _ => instDecidableFalse

Depends on / 依赖: Eq.symm, Submonoid, Submonoid.coe_mul, _add_eq_iff_add_mul_eq_mul, _eq_iff_eq_mul, _eq_mk, _of_mul, add_comm, coe_mul, instDecidableFalse, map_add, map_mul, mul_add, mul_assoc, mul_comm, mul_mk
-/
instance Prop.decidablePredBot : DecidablePred (⊥ : α -> Prop) := fun _ => instDecidableFalse

/--
Instance `Prop.decidablePredTop` / 实例 `Prop.decidablePredTop`

English:
instance Prop.decidablePredTop
  signature: : DecidablePred (⊤ : α -> Prop)
  body: fun _ => instDecidableTrue

中文:
实例 命题.decidablePredTop
  签名: : DecidablePred (⊤ : α -> 命题)
  定义体: fun _ => instDecidableTrue

Depends on / 依赖: instDecidableTrue
-/
instance Prop.decidablePredTop : DecidablePred (⊤ : α -> Prop) := fun _ => instDecidableTrue

/--
Instance `Prop.decidableRelBot` / 实例 `Prop.decidableRelBot`

English:
instance Prop.decidableRelBot
  signature: : DecidableRel (⊥ : α -> α -> Prop)
  body: fun _ _ => instDecidableFalse

中文:
实例 命题.decidableRelBot
  签名: : DecidableRel (⊥ : α -> α -> 命题)
  定义体: fun _ _ => instDecidableFalse

Depends on / 依赖: instDecidableFalse
-/
instance Prop.decidableRelBot : DecidableRel (⊥ : α -> α -> Prop) := fun _ _ => instDecidableFalse

/--
Instance `Prop.decidableRelTop` / 实例 `Prop.decidableRelTop`

English:
instance Prop.decidableRelTop
  signature: : DecidableRel (⊤ : α -> α -> Prop)
  body: fun _ _ => instDecidableTrue

中文:
实例 命题.decidableRelTop
  签名: : DecidableRel (⊤ : α -> α -> 命题)
  定义体: fun _ _ => instDecidableTrue

Depends on / 依赖: instDecidableTrue
-/
instance Prop.decidableRelTop : DecidableRel (⊤ : α -> α -> Prop) := fun _ _ => instDecidableTrue

end decidable_instances
