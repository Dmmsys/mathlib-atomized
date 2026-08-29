/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Data.FunLike.Module

/-!
# Operations on outer measures

In this file we define algebraic operations (addition, scalar multiplication)
on the type of outer measures on a type.
We also show that outer measures on a type `α` form a complete lattice.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure

-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section Basic

variable {α β : Type*} {m : OuterMeasure α}

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (OuterMeasure α)
  body: ⟨{ measureOf _ := 0
      empty := rfl
      mono _ := le_rfl
      iUnion_nat _ _ := zero_le }⟩

中文:
实例 instZero
  签名: : 零 (外测度 α)
  定义体: ⟨{ measureOf _ := 0
      empty := rfl
      mono _ := le_rfl
      iUnion_nat _ _ := zero_le }⟩

Depends on / 依赖: iUnion_nat, le_rfl, measureOf, zero_le
-/
instance instZero : Zero (OuterMeasure α) :=
  ⟨{ measureOf _ := 0
      empty := rfl
      mono _ := le_rfl
      iUnion_nat _ _ := zero_le }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (OuterMeasure α) (Set α) Real>=0∞
  body: rfl

@[deprecated (since := "2026-06-23")] alias coe_zero := FunLike.coe_zero

中文:
实例 :
  签名: 是ZeroApply (外测度 α) (集合 α) 实数>=0∞
  定义体: rfl

@[deprecated (since := "2026-06-23")] alias coe_zero := FunLike.coe_zero
-/
instance : IsZeroApply (OuterMeasure α) (Set α) Real>=0∞ where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_zero := FunLike.coe_zero

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (OuterMeasure α)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : 可居 (外测度 α)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited (OuterMeasure α) :=
  ⟨0⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (OuterMeasure α)
  body: ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      empty := show m₁ ∅ + m₂ ∅ = 0 by simp
      mono := fun {_ _} h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s _ =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) <= (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (measure_iUnion_le s) (measure_iUnion_le s)
          _ = _ := ENNReal.tsum_add.symm }⟩

中文:
实例 instAdd
  签名: : 加法 (外测度 α)
  定义体: ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      empty := show m₁ ∅ + m₂ ∅ = 0 by simp
      mono := fun {_ _} h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s _ =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) <= (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (measure_iUnion_le s) (measure_iUnion_le s)
          _ = _ := ENNReal.tsum_add.symm }⟩

Depends on / 依赖: ENNReal, ENNReal.tsum_add.symm, add_le_add, iUnion_nat, measureOf, measure_iUnion_le, tsum_add
-/
instance instAdd : Add (OuterMeasure α) :=
  ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      empty := show m₁ ∅ + m₂ ∅ = 0 by simp
      mono := fun {_ _} h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s _ =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) <= (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (measure_iUnion_le s) (measure_iUnion_le s)
          _ = _ := ENNReal.tsum_add.symm }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (OuterMeasure α) (Set α) Real>=0∞
  body: rfl

@[deprecated (since := "2026-06-23")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-23")] protected alias add_apply := add_apply

中文:
实例 :
  签名: 是加法Apply (外测度 α) (集合 α) 实数>=0∞
  定义体: rfl

@[deprecated (since := "2026-06-23")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-23")] protected alias add_apply := add_apply
-/
instance : IsAddApply (OuterMeasure α) (Set α) Real>=0∞ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-23")] protected alias add_apply := add_apply

section SMul

variable {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
variable {R' : Type*} [SMul R' Real>=0∞] [IsScalarTower R' Real>=0∞ Real>=0∞]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R (OuterMeasure α)
  body: ⟨fun c m =>
    { measureOf := fun s => c • m s
      empty := by simp only [measure_empty]; rw [← smul_one_mul c]; simp
      mono := fun {s t} h => by
        rw [← smul_one_mul c]; rw [← smul_one_mul c (m t)]
        exact mul_right_mono (m.mono h)
      iUnion_nat := fun s _ => by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact mul_right_mono (measure_iUnion_le _) }⟩

中文:
实例 instSMul
  签名: : 标量乘法 R (外测度 α)
  定义体: ⟨fun c m =>
    { measureOf := fun s => c • m s
      empty := by simp only [measure_empty]; rw [← smul_one_mul c]; simp
      mono := fun {s t} h => by
        rw [← smul_one_mul c]; rw [← smul_one_mul c (m t)]
        exact mul_right_mono (m.mono h)
      iUnion_nat := fun s _ => by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact mul_right_mono (measure_iUnion_le _) }⟩

Depends on / 依赖: ENNReal, ENNReal.tsum_mul_left, iUnion_nat, m.mono, measureOf, measure_empty, measure_iUnion_le, mul_right_mono, simp_rw, smul_one_mul, tsum_mul_left
-/
instance instSMul : SMul R (OuterMeasure α) :=
  ⟨fun c m =>
    { measureOf := fun s => c • m s
      empty := by simp only [measure_empty]; rw [← smul_one_mul c]; simp
      mono := fun {s t} h => by
        rw [← smul_one_mul c]; rw [← smul_one_mul c (m t)]
        exact mul_right_mono (m.mono h)
      iUnion_nat := fun s _ => by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact mul_right_mono (measure_iUnion_le _) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R (OuterMeasure α) (Set α) Real>=0∞
  body: rfl

@[deprecated (since := "2026-06-23")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-23")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: 是SMulApply R (外测度 α) (集合 α) 实数>=0∞
  定义体: rfl

@[deprecated (since := "2026-06-23")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-23")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply R (OuterMeasure α) (Set α) Real>=0∞ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-23")] protected alias smul_apply := smul_apply

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass R R' Real>=0∞]
  body: FunLike.smulCommClass

中文:
实例 instSMulCommClass
  签名: [标量交换类 R R' 实数>=0∞]
  定义体: FunLike.smulCommClass

Depends on / 依赖: FunLike, FunLike.smulCommClass, smulCommClass
-/
instance instSMulCommClass [SMulCommClass R R' Real>=0∞] : SMulCommClass R R' (OuterMeasure α) :=
  FunLike.smulCommClass

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul R R'] [IsScalarTower R R' Real>=0∞]
  body: FunLike.isScalarTower

中文:
实例 instIsScalarTower
  签名: [标量乘法 R R'] [标量塔 R R' 实数>=0∞]
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance instIsScalarTower [SMul R R'] [IsScalarTower R R' Real>=0∞] :
    IsScalarTower R R' (OuterMeasure α) := FunLike.isScalarTower

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞]
  body: FunLike.isCentralScalar

中文:
实例 instIsCentralScalar
  签名: [标量乘法 Rᵐᵒᵖ 实数>=0∞] [中心标量 R 实数>=0∞]
  定义体: FunLike.isCentralScalar

Depends on / 依赖: FunLike, FunLike.isCentralScalar, isCentralScalar
-/
instance instIsCentralScalar [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞] :
    IsCentralScalar R (OuterMeasure α) := FunLike.isCentralScalar

end SMul

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: {R : Type*} [Monoid R] [MulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: fast_instance% FunLike.mulAction

中文:
实例 instMulAction
  签名: {R : 类型} [幺半群 R] [乘法作用 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: fast_instance% FunLike.mulAction

Depends on / 依赖: FunLike, FunLike.mulAction, fast_instance, mulAction
-/
instance instMulAction {R : Type*} [Monoid R] [MulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] :
    MulAction R (OuterMeasure α) := fast_instance% FunLike.mulAction

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (OuterMeasure α)
  body: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (外测度 α)
  定义体: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance addCommMonoid : AddCommMonoid (OuterMeasure α) := fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: {R : Type*} [Monoid R] [DistribMulAction R Real>=0∞]
  body: fast_instance% FunLike.distribMulAction

中文:
实例 instDistribMulAction
  签名: {R : 类型} [幺半群 R] [分配乘法作用 R 实数>=0∞]
  定义体: fast_instance% FunLike.distribMulAction

Depends on / 依赖: FunLike, FunLike.distribMulAction, distribMulAction, fast_instance
-/
instance instDistribMulAction {R : Type*} [Monoid R] [DistribMulAction R Real>=0∞]
    [IsScalarTower R Real>=0∞ Real>=0∞] :
    DistribMulAction R (OuterMeasure α) := fast_instance% FunLike.distribMulAction

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {R : Type*} [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: fast_instance% FunLike.module

中文:
实例 instModule
  签名: {R : 类型} [半环 R] [模 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance instModule {R : Type*} [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] :
    Module R (OuterMeasure α) := fast_instance% FunLike.module

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (OuterMeasure α)
  body: ⟨0⟩

@[simp]

中文:
实例 instBot
  签名: : 底元素 (外测度 α)
  定义体: ⟨0⟩

@[simp]
-/
instance instBot : Bot (OuterMeasure α) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (⊥ : OuterMeasure α) = 0
  proof: rfl

中文:
定理 coe_bot
  结论: (⊥ : 外测度 α) = 0
  证明: rfl
-/
theorem coe_bot : (⊥ : OuterMeasure α) = 0 :=
  rfl

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (OuterMeasure α) where
  body: forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm _ _ hab hba := ext fun s => le_antisymm (hab s) (hba s)

中文:
实例 instPartialOrder
  签名: : 偏序 (外测度 α) where
  定义体: forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm _ _ hab hba := ext fun s => le_antisymm (hab s) (hba s)
-/
instance instPartialOrder : PartialOrder (OuterMeasure α) where
  le m₁ m₂ := forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm _ _ hab hba := ext fun s => le_antisymm (hab s) (hba s)

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: {α : Type*}
  body: add_le_add_left (h s) _

中文:
实例 instIsOrderedAddMonoid
  签名: {α : 类型}
  定义体: add_le_add_left (h s) _

Depends on / 依赖: add_le_add_left
-/
instance instIsOrderedAddMonoid {α : Type*} : IsOrderedAddMonoid (OuterMeasure α) where
  add_le_add_left _ _ h _ s := add_le_add_left (h s) _

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: : OrderBot (OuterMeasure α)
  body: { bot := 0,
    bot_le := fun a s => by simp only [zero_apply, zero_le] }

中文:
实例 orderBot
  签名: : 有底序 (外测度 α)
  定义体: { bot := 0,
    bot_le := fun a s => by simp only [zero_apply, zero_le] }

Depends on / 依赖: bot_le, zero_apply, zero_le
-/
instance orderBot : OrderBot (OuterMeasure α) :=
  { bot := 0,
    bot_le := fun a s => by simp only [zero_apply, zero_le] }

/--
theorem `univ_eq_zero_iff` / 定理 `univ_eq_zero_iff`

English:
theorem univ_eq_zero_iff
  given: (m : OuterMeasure α)
  statement: m univ = 0 ↔ m = 0
  proof: ⟨fun h => bot_unique fun s => (measure_mono <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩

中文:
定理 univ_eq_zero_iff
  条件: (m : 外测度 α)
  结论: m univ = 0 ↔ m = 0
  证明: ⟨fun h => bot_unique fun s => (measure_mono <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩

Depends on / 依赖: bot_unique, h.symm, measure_mono, subset_univ, trans_eq
-/
theorem univ_eq_zero_iff (m : OuterMeasure α) : m univ = 0 ↔ m = 0 :=
  ⟨fun h => bot_unique fun s => (measure_mono <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩

section Supremum

/--
Instance `instSupSet` / 实例 `instSupSet`

English:
instance instSupSet
  signature: : SupSet (OuterMeasure α)
  body: ⟨fun ms =>
    { measureOf := fun s => ⨆ m in ms, (m : OuterMeasure α) s
empty := nonpos_iff_eq_zero.1 iSup₂_le fun m _ => le_of_eq m.empty
      mono := fun {_ _} hs => iSup₂_mono fun m _ => m.mono hs
      iUnion_nat := fun f _ =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) <= ∑' i : Nat, m (f i) := measure_iUnion_le _
            _ <= ∑' i, ⨆ m in ms, (m : OuterMeasure α) (f i) :=
               ENNReal.tsum_le_tsum fun i => by apply le_iSup₂ m hm
             }⟩

中文:
实例 instSupSet
  签名: : 上确界集 (外测度 α)
  定义体: ⟨fun ms =>
    { measureOf := fun s => ⨆ m in ms, (m : OuterMeasure α) s
empty := nonpos_iff_eq_zero.1 iSup₂_le fun m _ => le_of_eq m.empty
      mono := fun {_ _} hs => iSup₂_mono fun m _ => m.mono hs
      iUnion_nat := fun f _ =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) <= ∑' i : Nat, m (f i) := measure_iUnion_le _
            _ <= ∑' i, ⨆ m in ms, (m : OuterMeasure α) (f i) :=
               ENNReal.tsum_le_tsum fun i => by apply le_iSup₂ m hm
             }⟩

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, OuterMeasure, iUnion_nat, le_of_eq, m.empty, m.mono, measureOf, measure_iUnion_le, nonpos_iff_eq_zero, tsum_le_tsum
-/
instance instSupSet : SupSet (OuterMeasure α) :=
  ⟨fun ms =>
    { measureOf := fun s => ⨆ m in ms, (m : OuterMeasure α) s
empty := nonpos_iff_eq_zero.1 iSup₂_le fun m _ => le_of_eq m.empty
      mono := fun {_ _} hs => iSup₂_mono fun m _ => m.mono hs
      iUnion_nat := fun f _ =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) <= ∑' i : Nat, m (f i) := measure_iUnion_le _
            _ <= ∑' i, ⨆ m in ms, (m : OuterMeasure α) (f i) :=
               ENNReal.tsum_le_tsum fun i => by apply le_iSup₂ m hm
             }⟩

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (OuterMeasure α)
  body: { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => by apply le_iSup₂ m hm, fun _ hm s => iSup₂_le fun _ hm' => hm hm' s⟩ with }

@[simp]

中文:
实例 instCompleteLattice
  签名: : 完备格 (外测度 α)
  定义体: { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => by apply le_iSup₂ m hm, fun _ hm s => iSup₂_le fun _ hm' => hm hm' s⟩ with }

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.orderBot, completeLatticeOfSup, orderBot
-/
instance instCompleteLattice : CompleteLattice (OuterMeasure α) :=
  { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => by apply le_iSup₂ m hm, fun _ hm s => iSup₂_le fun _ hm' => hm hm' s⟩ with }

@[simp]
/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: (ms : Set (OuterMeasure α)) (s : Set α)
  proof: rfl

@[simp]

中文:
定理 sSup_apply
  条件: (ms : 集合 (外测度 α)) (s : 集合 α)
  证明: rfl

@[simp]
-/
theorem sSup_apply (ms : Set (OuterMeasure α)) (s : Set α) :
    (sSup ms) s = ⨆ m in ms, (m : OuterMeasure α) s :=
  rfl

@[simp]
/--
theorem `iSup_apply` / 定理 `iSup_apply`

English:
theorem iSup_apply
  given: {ι} (f : ι -> OuterMeasure α) (s : Set α)
  statement: (⨆ i : ι, f i) s = ⨆ i, f i s
  proof: by
  rw [iSup]; rw [sSup_apply]; rw [iSup_range]

@[norm_cast]

中文:
定理 iSup_apply
  条件: {ι} (f : ι -> 外测度 α) (s : 集合 α)
  结论: (⨆ i : ι, f i) s = ⨆ i, f i s
  证明: by
  rw [iSup]; rw [sSup_apply]; rw [iSup_range]

@[norm_cast]

Depends on / 依赖: iSup_range, sSup_apply
-/
theorem iSup_apply {ι} (f : ι -> OuterMeasure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s := by
  rw [iSup]; rw [sSup_apply]; rw [iSup_range]

@[norm_cast]
/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι} (f : ι -> OuterMeasure α)
  statement: ⇑(⨆ i, f i) = ⨆ i, ⇑(f i)
  proof: funext fun s => by simp

@[simp]

中文:
定理 coe_iSup
  条件: {ι} (f : ι -> 外测度 α)
  结论: ⇑(⨆ i, f i) = ⨆ i, ⇑(f i)
  证明: funext fun s => by simp

@[simp]
-/
theorem coe_iSup {ι} (f : ι -> OuterMeasure α) : ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) :=
  funext fun s => by simp

@[simp]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (m₁ m₂ : OuterMeasure α) (s : Set α)
  statement: (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s
  proof: by
  have := iSup_apply (fun b => cond b m₁ m₂) s; rwa [iSup_bool_eq, iSup_bool_eq] at this

中文:
定理 sup_apply
  条件: (m₁ m₂ : 外测度 α) (s : 集合 α)
  结论: (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s
  证明: by
  have := iSup_apply (fun b => cond b m₁ m₂) s; rwa [iSup_bool_eq, iSup_bool_eq] at this

Depends on / 依赖: iSup_apply, iSup_bool_eq
-/
theorem sup_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s := by
  have := iSup_apply (fun b => cond b m₁ m₂) s; rwa [iSup_bool_eq, iSup_bool_eq] at this

/--
theorem `smul_iSup` / 定理 `smul_iSup`

English:
theorem smul_iSup
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]

中文:
定理 smul_iSup
  结论: {R : 类型} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]

Depends on / 依赖: ENNReal, ENNReal.smul_iSup, iSup_apply, smul_apply, smul_iSup
-/
theorem smul_iSup {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    {ι : Sort*} (f : ι -> OuterMeasure α) (c : R) :
    (c • ⨆ i, f i) = ⨆ i, c • f i :=
  ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]

end Supremum

@[mono, gcongr]
/--
theorem `mono''` / 定理 `mono''`

English:
theorem mono''
  given: {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ <= m₂) (hs : s₁ subseteq s₂)
  proof: (hm s₁).trans (m₂.mono hs)

中文:
定理 mono''
  条件: {m₁ m₂ : 外测度 α} {s₁ s₂ : 集合 α} (hm : m₁ <= m₂) (hs : s₁ subseteq s₂)
  证明: (hm s₁).trans (m₂.mono hs)
-/
theorem mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ <= m₂) (hs : s₁ subseteq s₂) :
    m₁ s₁ <= m₂ s₂ :=
  (hm s₁).trans (m₂.mono hs)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β} (f : α -> β)
  body: { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {_ _} h => m.mono (preimage_mono h)
      iUnion_nat := fun s _ => by simpa using measure_iUnion_le fun i => f ⁻¹' s i }
  map_add' _ _ := coe_fn_injective rfl
  map_smul' _ _ := coe_fn_injective rfl

@[simp]

中文:
定义 map
  签名: {β} (f : α -> β)
  定义体: { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {_ _} h => m.mono (preimage_mono h)
      iUnion_nat := fun s _ => by simpa using measure_iUnion_le fun i => f ⁻¹' s i }
  map_add' _ _ := coe_fn_injective rfl
  map_smul' _ _ := coe_fn_injective rfl

@[simp]

Depends on / 依赖: coe_fn_injective, iUnion_nat, m.empty, m.mono, map_add, map_smul, measureOf, measure_iUnion_le, preimage_mono
-/
def map {β} (f : α -> β) : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β where
  toFun m :=
    { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {_ _} h => m.mono (preimage_mono h)
      iUnion_nat := fun s _ => by simpa using measure_iUnion_le fun i => f ⁻¹' s i }
  map_add' _ _ := coe_fn_injective rfl
  map_smul' _ _ := coe_fn_injective rfl

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {β} (f : α -> β) (m : OuterMeasure α) (s : Set β)
  statement: map f m s = m (f ⁻¹' s)
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: {β} (f : α -> β) (m : 外测度 α) (s : 集合 β)
  结论: map f m s = m (f ⁻¹' s)
  证明: rfl

@[simp]
-/
theorem map_apply {β} (f : α -> β) (m : OuterMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (m : OuterMeasure α)
  statement: map id m = m
  proof: ext fun _ => rfl

@[simp]

中文:
定理 map_id
  条件: (m : 外测度 α)
  结论: map id m = m
  证明: ext fun _ => rfl

@[simp]
-/
theorem map_id (m : OuterMeasure α) : map id m = m :=
  ext fun _ => rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {β γ} (f : α -> β) (g : β -> γ) (m : OuterMeasure α)
  proof: ext fun _ => rfl

@[gcongr, mono]

中文:
定理 map_map
  条件: {β γ} (f : α -> β) (g : β -> γ) (m : 外测度 α)
  证明: ext fun _ => rfl

@[gcongr, mono]
-/
theorem map_map {β γ} (f : α -> β) (g : β -> γ) (m : OuterMeasure α) :
    map g (map f m) = map (g ∘ f) m :=
  ext fun _ => rfl

@[gcongr, mono]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {β} (f : α -> β)
  statement: Monotone (map f)
  proof: fun _ _ h _ => h _

@[simp]

中文:
定理 map_mono
  条件: {β} (f : α -> β)
  结论: 递增 (map f)
  证明: fun _ _ h _ => h _

@[simp]
-/
theorem map_mono {β} (f : α -> β) : Monotone (map f) := fun _ _ h _ => h _

@[simp]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: {β} (f : α -> β) (m m' : OuterMeasure α)
  statement: map f (m ⊔ m') = map f m ⊔ map f m'
  proof: ext fun s => by simp only [map_apply, sup_apply]

@[simp]

中文:
定理 map_sup
  条件: {β} (f : α -> β) (m m' : 外测度 α)
  结论: map f (m ⊔ m') = map f m ⊔ map f m'
  证明: ext fun s => by simp only [map_apply, sup_apply]

@[simp]

Depends on / 依赖: map_apply, sup_apply
-/
theorem map_sup {β} (f : α -> β) (m m' : OuterMeasure α) : map f (m ⊔ m') = map f m ⊔ map f m' :=
  ext fun s => by simp only [map_apply, sup_apply]

@[simp]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {β ι} (f : α -> β) (m : ι -> OuterMeasure α)
  statement: map f (⨆ i, m i) = ⨆ i, map f (m i)
  proof: ext fun s => by simp only [map_apply, iSup_apply]

中文:
定理 map_iSup
  条件: {β ι} (f : α -> β) (m : ι -> 外测度 α)
  结论: map f (⨆ i, m i) = ⨆ i, map f (m i)
  证明: ext fun s => by simp only [map_apply, iSup_apply]

Depends on / 依赖: iSup_apply, map_apply
-/
theorem map_iSup {β ι} (f : α -> β) (m : ι -> OuterMeasure α) : map f (⨆ i, m i) = ⨆ i, map f (m i) :=
  ext fun s => by simp only [map_apply, iSup_apply]

/--
Instance `instFunctor` / 实例 `instFunctor`

English:
instance instFunctor
  signature: : Functor OuterMeasure where map {_ _} f
  body: map f

中文:
实例 instFunctor
  签名: : 函子 外测度 where map {_ _} f
  定义体: map f
-/
instance instFunctor : Functor OuterMeasure where map {_ _} f := map f

/--
Instance `instLawfulFunctor` / 实例 `instLawfulFunctor`

English:
instance instLawfulFunctor
  signature: : LawfulFunctor OuterMeasure
  body: by constructor <;> intros <;> rfl

中文:
实例 instLawfulFunctor
  签名: : Lawful函子 外测度
  定义体: by constructor <;> intros <;> rfl

Depends on / 依赖: intros
-/
instance instLawfulFunctor : LawfulFunctor OuterMeasure := by constructor <;> intros <;> rfl

/--
Definition of `dirac` / `dirac` 的定义

English:
definition dirac
  signature: (a : α)
  body: indicator s (fun _ => 1) a
  empty := by simp
  mono {_ _} h := by grw [h]
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := Real>=0∞) rfl _ _ _
    _ <= ∑' n, indicator (s n) 1 a := iSup_le fun _ => ENNReal.le_tsum _

@[simp]

中文:
定义 dirac
  签名: (a : α)
  定义体: indicator s (fun _ => 1) a
  empty := by simp
  mono {_ _} h := by grw [h]
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := Real>=0∞) rfl _ _ _
    _ <= ∑' n, indicator (s n) 1 a := iSup_le fun _ => ENNReal.le_tsum _

@[simp]

Depends on / 依赖: indicator
-/
def dirac (a : α) : OuterMeasure α where
  measureOf s := indicator s (fun _ => 1) a
  empty := by simp
  mono {_ _} h := by grw [h]
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := Real>=0∞) rfl _ _ _
    _ <= ∑' n, indicator (s n) 1 a := iSup_le fun _ => ENNReal.le_tsum _

@[simp]
/--
theorem `dirac_apply` / 定理 `dirac_apply`

English:
theorem dirac_apply
  given: (a : α) (s : Set α)
  statement: dirac a s = indicator s (fun _ => 1) a
  proof: rfl

中文:
定理 dirac_apply
  条件: (a : α) (s : 集合 α)
  结论: dirac a s = indicator s (fun _ => 1) a
  证明: rfl
-/
theorem dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a :=
  rfl

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {ι} (f : ι -> OuterMeasure α)
  body: ∑' i, f i s
  empty := by simp
  mono {_ _} h := ENNReal.tsum_le_tsum fun _ => measure_mono h
  iUnion_nat s _ := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => measure_iUnion_le _

@[simp]

中文:
定义 求和
  签名: {ι} (f : ι -> 外测度 α)
  定义体: ∑' i, f i s
  empty := by simp
  mono {_ _} h := ENNReal.tsum_le_tsum fun _ => measure_mono h
  iUnion_nat s _ := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => measure_iUnion_le _

@[simp]
-/
def sum {ι} (f : ι -> OuterMeasure α) : OuterMeasure α where
  measureOf s := ∑' i, f i s
  empty := by simp
  mono {_ _} h := ENNReal.tsum_le_tsum fun _ => measure_mono h
  iUnion_nat s _ := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => measure_iUnion_le _

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: {ι} (f : ι -> OuterMeasure α) (s : Set α)
  statement: sum f s = ∑' i, f i s
  proof: rfl

中文:
定理 sum_apply
  条件: {ι} (f : ι -> 外测度 α) (s : 集合 α)
  结论: 求和 f s = ∑' i, f i s
  证明: rfl
-/
theorem sum_apply {ι} (f : ι -> OuterMeasure α) (s : Set α) : sum f s = ∑' i, f i s :=
  rfl

/--
theorem `smul_dirac_apply` / 定理 `smul_dirac_apply`

English:
theorem smul_dirac_apply
  given: (a : Real>=0∞) (b : α) (s : Set α)
  proof: by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]

中文:
定理 smul_dirac_apply
  条件: (a : 实数>=0∞) (b : α) (s : 集合 α)
  证明: by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]

Depends on / 依赖: dirac_apply, indicator_mul_right, mul_one, smul_apply, smul_eq_mul
-/
theorem smul_dirac_apply (a : Real>=0∞) (b : α) (s : Set α) :
    (a • dirac b) s = indicator s (fun _ => a) b := by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {β} (f : α -> β)
  body: { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {_ _} h => by gcongr
      iUnion_nat := fun s _ => by simpa only [image_iUnion] using measure_iUnion_le _ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 comap
  签名: {β} (f : α -> β)
  定义体: { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {_ _} h => by gcongr
      iUnion_nat := fun s _ => by simpa only [image_iUnion] using measure_iUnion_le _ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: iUnion_nat, image_iUnion, map_add, map_smul, measureOf, measure_iUnion_le
-/
def comap {β} (f : α -> β) : OuterMeasure β ->ₗ[Real>=0∞] OuterMeasure α where
  toFun m :=
    { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {_ _} h => by gcongr
      iUnion_nat := fun s _ => by simpa only [image_iUnion] using measure_iUnion_le _ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: {β} (f : α -> β) (m : OuterMeasure β) (s : Set α)
  statement: comap f m s = m (f '' s)
  proof: rfl

@[gcongr, mono]

中文:
定理 comap_apply
  条件: {β} (f : α -> β) (m : 外测度 β) (s : 集合 α)
  结论: comap f m s = m (f '' s)
  证明: rfl

@[gcongr, mono]
-/
theorem comap_apply {β} (f : α -> β) (m : OuterMeasure β) (s : Set α) : comap f m s = m (f '' s) :=
  rfl

@[gcongr, mono]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {β} (f : α -> β)
  statement: Monotone (comap f)
  proof: fun _ _ h _ => h _

@[simp]

中文:
定理 comap_mono
  条件: {β} (f : α -> β)
  结论: 递增 (comap f)
  证明: fun _ _ h _ => h _

@[simp]
-/
theorem comap_mono {β} (f : α -> β) : Monotone (comap f) := fun _ _ h _ => h _

@[simp]
/--
theorem `comap_iSup` / 定理 `comap_iSup`

English:
theorem comap_iSup
  given: {β ι} (f : α -> β) (m : ι -> OuterMeasure β)
  proof: ext fun s => by simp only [comap_apply, iSup_apply]

中文:
定理 comap_iSup
  条件: {β ι} (f : α -> β) (m : ι -> 外测度 β)
  证明: ext fun s => by simp only [comap_apply, iSup_apply]

Depends on / 依赖: comap_apply, iSup_apply
-/
theorem comap_iSup {β ι} (f : α -> β) (m : ι -> OuterMeasure β) :
    comap f (⨆ i, m i) = ⨆ i, comap f (m i) :=
  ext fun s => by simp only [comap_apply, iSup_apply]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (s : Set α)
  body: (map (↑)).comp (comap ((↑) : s -> α))

中文:
定义 restrict
  签名: (s : 集合 α)
  定义体: (map (↑)).comp (comap ((↑) : s -> α))
-/
def restrict (s : Set α) : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure α :=
  (map (↑)).comp (comap ((↑) : s -> α))

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
@[simp]
/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (s t : Set α) (m : OuterMeasure α)
  statement: restrict s m t = m (t inter s)
  proof: by
  simp [restrict, inter_comm t]

@[mono]

中文:
定理 restrict_apply
  条件: (s t : 集合 α) (m : 外测度 α)
  结论: restrict s m t = m (t inter s)
  证明: by
  simp [restrict, inter_comm t]

@[mono]

Depends on / 依赖: inter_comm, restrict
-/
theorem restrict_apply (s t : Set α) (m : OuterMeasure α) : restrict s m t = m (t inter s) := by
  simp [restrict, inter_comm t]

@[mono]
/--
theorem `restrict_mono` / 定理 `restrict_mono`

English:
theorem restrict_mono
  given: {s t : Set α} (h : s subseteq t) {m m' : OuterMeasure α} (hm : m <= m')
  proof: fun u => by
  simp only [restrict_apply]
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)

@[simp]

中文:
定理 restrict_mono
  条件: {s t : 集合 α} (h : s subseteq t) {m m' : 外测度 α} (hm : m <= m')
  证明: fun u => by
  simp only [restrict_apply]
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)

@[simp]

Depends on / 依赖: inter_subset_inter_right, restrict_apply
-/
theorem restrict_mono {s t : Set α} (h : s subseteq t) {m m' : OuterMeasure α} (hm : m <= m') :
    restrict s m <= restrict t m' := fun u => by
  simp only [restrict_apply]
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)

@[simp]
/--
theorem `restrict_univ` / 定理 `restrict_univ`

English:
theorem restrict_univ
  given: (m : OuterMeasure α)
  statement: restrict univ m = m
  proof: ext fun s => by simp

@[simp]

中文:
定理 restrict_univ
  条件: (m : 外测度 α)
  结论: restrict univ m = m
  证明: ext fun s => by simp

@[simp]
-/
theorem restrict_univ (m : OuterMeasure α) : restrict univ m = m :=
  ext fun s => by simp

@[simp]
/--
theorem `restrict_empty` / 定理 `restrict_empty`

English:
theorem restrict_empty
  given: (m : OuterMeasure α)
  statement: restrict ∅ m = 0
  proof: ext fun s => by simp

@[simp]

中文:
定理 restrict_empty
  条件: (m : 外测度 α)
  结论: restrict ∅ m = 0
  证明: ext fun s => by simp

@[simp]
-/
theorem restrict_empty (m : OuterMeasure α) : restrict ∅ m = 0 :=
  ext fun s => by simp

@[simp]
/--
theorem `restrict_iSup` / 定理 `restrict_iSup`

English:
theorem restrict_iSup
  given: {ι} (s : Set α) (m : ι -> OuterMeasure α)
  proof: by simp [restrict]

中文:
定理 restrict_iSup
  条件: {ι} (s : 集合 α) (m : ι -> 外测度 α)
  证明: by simp [restrict]

Depends on / 依赖: restrict
-/
theorem restrict_iSup {ι} (s : Set α) (m : ι -> OuterMeasure α) :
    restrict s (⨆ i, m i) = ⨆ i, restrict s (m i) := by simp [restrict]

/--
theorem `map_comap` / 定理 `map_comap`

English:
theorem map_comap
  given: {β} (f : α -> β) (m : OuterMeasure β)
  statement: map f (comap f m) = restrict (range f) m
  proof: ext fun s => congr_arg m by simp only [image_preimage_eq_inter_range, Subtype.range_coe]

中文:
定理 map_comap
  条件: {β} (f : α -> β) (m : 外测度 β)
  结论: map f (comap f m) = restrict (range f) m
  证明: ext fun s => congr_arg m by simp only [image_preimage_eq_inter_range, Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.range_coe, congr_arg, image_preimage_eq_inter_range, range_coe
-/
theorem map_comap {β} (f : α -> β) (m : OuterMeasure β) : map f (comap f m) = restrict (range f) m :=
ext fun s => congr_arg m by simp only [image_preimage_eq_inter_range, Subtype.range_coe]

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: {β} (f : α -> β) (m : OuterMeasure β)
  statement: map f (comap f m) <= m
  proof: fun _ =>
m.mono image_preimage_subset _ _

中文:
定理 map_comap_le
  条件: {β} (f : α -> β) (m : 外测度 β)
  结论: map f (comap f m) <= m
  证明: fun _ =>
m.mono image_preimage_subset _ _
-/
theorem map_comap_le {β} (f : α -> β) (m : OuterMeasure β) : map f (comap f m) <= m := fun _ =>
m.mono image_preimage_subset _ _

/--
theorem `restrict_le_self` / 定理 `restrict_le_self`

English:
theorem restrict_le_self
  given: (m : OuterMeasure α) (s : Set α)
  statement: restrict s m <= m
  proof: map_comap_le _ _

@[simp]

中文:
定理 restrict_le_self
  条件: (m : 外测度 α) (s : 集合 α)
  结论: restrict s m <= m
  证明: map_comap_le _ _

@[simp]

Depends on / 依赖: map_comap_le
-/
theorem restrict_le_self (m : OuterMeasure α) (s : Set α) : restrict s m <= m :=
  map_comap_le _ _

@[simp]
/--
theorem `map_le_restrict_range` / 定理 `map_le_restrict_range`

English:
theorem map_le_restrict_range
  given: {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f : α -> β}
  proof: ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s inter range f)⟩

中文:
定理 map_le_restrict_range
  条件: {β} {ma : 外测度 α} {mb : 外测度 β} {f : α -> β}
  证明: ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s inter range f)⟩

Depends on / 依赖: h.trans, restrict_le_self
-/
theorem map_le_restrict_range {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f : α -> β} :
    map f ma <= restrict (range f) mb ↔ map f ma <= mb :=
  ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s inter range f)⟩

/--
theorem `map_comap_of_surjective` / 定理 `map_comap_of_surjective`

English:
theorem map_comap_of_surjective
  given: {β} {f : α -> β} (hf : Surjective f) (m : OuterMeasure β)
  proof: ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]

中文:
定理 map_comap_of_surjective
  条件: {β} {f : α -> β} (hf : 满射 f) (m : 外测度 β)
  证明: ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]

Depends on / 依赖: comap_apply, hf.image_preimage, image_preimage, map_apply
-/
theorem map_comap_of_surjective {β} {f : α -> β} (hf : Surjective f) (m : OuterMeasure β) :
    map f (comap f m) = m :=
  ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: {β} (f : α -> β) (m : OuterMeasure α)
  statement: m <= comap f (map f m)
  proof: fun _ =>
m.mono subset_preimage_image _ _

中文:
定理 le_comap_map
  条件: {β} (f : α -> β) (m : 外测度 α)
  结论: m <= comap f (map f m)
  证明: fun _ =>
m.mono subset_preimage_image _ _
-/
theorem le_comap_map {β} (f : α -> β) (m : OuterMeasure α) : m <= comap f (map f m) := fun _ =>
m.mono subset_preimage_image _ _

/--
theorem `comap_map` / 定理 `comap_map`

English:
theorem comap_map
  given: {β} {f : α -> β} (hf : Injective f) (m : OuterMeasure α)
  statement: comap f (map f m) = m
  proof: ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]

@[simp]

中文:
定理 comap_map
  条件: {β} {f : α -> β} (hf : 单射 f) (m : 外测度 α)
  结论: comap f (map f m) = m
  证明: ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]

@[simp]

Depends on / 依赖: comap_apply, hf.preimage_image, map_apply, preimage_image
-/
theorem comap_map {β} {f : α -> β} (hf : Injective f) (m : OuterMeasure α) : comap f (map f m) = m :=
  ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]

@[simp]
/--
theorem `top_apply` / 定理 `top_apply`

English:
theorem top_apply
  given: {s : Set α} (h : s.Nonempty)
  statement: (⊤ : OuterMeasure α) s = ∞
  proof: let ⟨a, as⟩ := h
top_unique le_trans (by simp [as]) (le_iSup₂ (∞ • dirac a) trivial)

中文:
定理 top_apply
  条件: {s : 集合 α} (h : s.非空)
  结论: (⊤ : 外测度 α) s = ∞
  证明: let ⟨a, as⟩ := h
top_unique le_trans (by simp [as]) (le_iSup₂ (∞ • dirac a) trivial)

Depends on / 依赖: le_trans, top_unique
-/
theorem top_apply {s : Set α} (h : s.Nonempty) : (⊤ : OuterMeasure α) s = ∞ :=
  let ⟨a, as⟩ := h
top_unique le_trans (by simp [as]) (le_iSup₂ (∞ • dirac a) trivial)

/--
theorem `top_apply'` / 定理 `top_apply'`

English:
theorem top_apply'
  given: (s : Set α)
  statement: (⊤ : OuterMeasure α) s = ⨅ _ : s = ∅, 0
  proof: s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]

@[simp]

中文:
定理 top_apply'
  条件: (s : 集合 α)
  结论: (⊤ : 外测度 α) s = ⨅ _ : s = ∅, 0
  证明: s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]

@[simp]

Depends on / 依赖: eq_empty_or_nonempty, h.ne_empty, ne_empty, s.eq_empty_or_nonempty.elim
-/
theorem top_apply' (s : Set α) : (⊤ : OuterMeasure α) s = ⨅ _ : s = ∅, 0 :=
  s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : α -> β)
  statement: comap f ⊤ = ⊤
  proof: ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]

中文:
定理 comap_top
  条件: (f : α -> β)
  结论: comap f ⊤ = ⊤
  证明: ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]

Depends on / 依赖: comap_apply, ext_nonempty, hs.image, top_apply
-/
theorem comap_top (f : α -> β) : comap f ⊤ = ⊤ :=
  ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]

/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : α -> β)
  statement: map f ⊤ = restrict (range f) ⊤
  proof: ext fun s => by
    rw [map_apply]; rw [restrict_apply]; rw [← image_preimage_eq_inter_range]; rw [top_apply']; rw [top_apply']; rw [Set.image_eq_empty]

@[simp]

中文:
定理 map_top
  条件: (f : α -> β)
  结论: map f ⊤ = restrict (range f) ⊤
  证明: ext fun s => by
    rw [map_apply]; rw [restrict_apply]; rw [← image_preimage_eq_inter_range]; rw [top_apply']; rw [top_apply']; rw [Set.image_eq_empty]

@[simp]

Depends on / 依赖: Set.image_eq_empty, image_eq_empty, image_preimage_eq_inter_range, map_apply, restrict_apply, top_apply
-/
theorem map_top (f : α -> β) : map f ⊤ = restrict (range f) ⊤ :=
  ext fun s => by
    rw [map_apply]; rw [restrict_apply]; rw [← image_preimage_eq_inter_range]; rw [top_apply']; rw [top_apply']; rw [Set.image_eq_empty]

@[simp]
/--
theorem `map_top_of_surjective` / 定理 `map_top_of_surjective`

English:
theorem map_top_of_surjective
  given: (f : α -> β) (hf : Surjective f)
  statement: map f ⊤ = ⊤
  proof: by
  rw [map_top]; rw [hf.range_eq]; rw [restrict_univ]

中文:
定理 map_top_of_surjective
  条件: (f : α -> β) (hf : 满射 f)
  结论: map f ⊤ = ⊤
  证明: by
  rw [map_top]; rw [hf.range_eq]; rw [restrict_univ]

Depends on / 依赖: hf.range_eq, map_top, range_eq, restrict_univ
-/
theorem map_top_of_surjective (f : α -> β) (hf : Surjective f) : map f ⊤ = ⊤ := by
  rw [map_top]; rw [hf.range_eq]; rw [restrict_univ]

end Basic

end OuterMeasure

end MeasureTheory
