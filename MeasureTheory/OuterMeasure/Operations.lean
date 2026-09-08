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

/-
**MeasureTheory.OuterMeasure.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：instZero : Zero (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (OuterMeasure α) :=
  ⟨{  measureOf _ := 0
      empty := rfl
      mono _ := le_rfl
      iUnion_nat _ _ := zero_le }⟩
/-
**MeasureTheory.OuterMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.OuterMeas
ure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (OuterMeasure α) (Set α) ℝ≥0∞ where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_zero := FunLike.coe_zero
/-
**MeasureTheory.OuterMeasure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：instInhabited : Inhabited (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (OuterMeasure α) :=
  ⟨0⟩
/-
**MeasureTheory.OuterMeasure.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：instAdd : Add (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (OuterMeasure α) :=
  ⟨fun m₁ m₂ =>
    { measureOf := fun s => m₁ s + m₂ s
      empty := show m₁ ∅ + m₂ ∅ = 0 by simp
      mono := fun {_ _} h => add_le_add (m₁.mono h) (m₂.mono h)
      iUnion_nat := fun s _ =>
        calc
          m₁ (⋃ i, s i) + m₂ (⋃ i, s i) ≤ (∑' i, m₁ (s i)) + ∑' i, m₂ (s i) :=
            add_le_add (measure_iUnion_le s) (measure_iUnion_le s)
          _ = _ := ENNReal.tsum_add.symm }⟩
/-
**MeasureTheory.OuterMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.OuterMeas
ure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (OuterMeasure α) (Set α) ℝ≥0∞ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-23")] protected alias add_apply := add_apply

section SMul

variable {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable {R' : Type*} [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

/-
**MeasureTheory.OuterMeasure.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：instSMul : SMul R (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul R (OuterMeasure α) :=
  ⟨fun c m =>
    { measureOf := fun s => c • m s
      empty := by simp only [measure_empty]; rw [← smul_one_mul c]; simp
      mono := fun {s t} h => by
        rw [← smul_one_mul c, ← smul_one_mul c (m t)]
        exact mul_right_mono (m.mono h)
      iUnion_nat := fun s _ => by
        simp_rw [← smul_one_mul c (m _), ENNReal.tsum_mul_left]
        exact mul_right_mono (measure_iUnion_le _) }⟩
/-
**MeasureTheory.OuterMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.OuterMeas
ure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R (OuterMeasure α) (Set α) ℝ≥0∞ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-23")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-23")] protected alias smul_apply := smul_apply
/-
**MeasureTheory.OuterMeasure.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：instSMulCommClass [SMulCommClass R R' Real>=0∞] : SMulCommClass R R' (Oute
rMeasure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.smulCommClass`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
-/
instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] : SMulCommClass R R' (OuterMeasure α) :=
  FunLike.smulCommClass
/-
**MeasureTheory.OuterMeasure.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：instIsScalarTower [SMul R R'] [IsScalarTower R R' Real>=0∞] : IsScalarTowe
r R R' (OuterMeasure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isScalarTower`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
-/
instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] :
    IsScalarTower R R' (OuterMeasure α) := FunLike.isScalarTower
/-
**MeasureTheory.OuterMeasure.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：instIsCentralScalar [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞] : Is
CentralScalar R (OuterMeasure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isCentralScalar`：∀ {M : Type u_1} {F : Type u_3} {α : Type u_4} 
{β : Type u_5} [i : FunLike F α β] [inst : SMul M F]   [inst_1 : SMul Mᵐᵒᵖ F] [i
nst_2 : SMul …
· 使用定理 `IsScalarTower.op_left`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [i
nst : SMul M α] [inst_1 : SMul Mᵐᵒᵖ α] [IsCentralScalar M α]   [inst_3 : SMul M 
N] [inst_4 …
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
-/
instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] :
    IsCentralScalar R (OuterMeasure α) := FunLike.isCentralScalar

end SMul

/-
**MeasureTheory.OuterMeasure.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：instMulAction {R : Type*} [Monoid R] [MulAction R Real>=0∞] [IsScalarTower
 R Real>=0∞ Real>=0∞] : MulAction R (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction {R : Type*} [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    MulAction R (OuterMeasure α) := fast_instance% FunLike.mulAction
/-
**MeasureTheory.OuterMeasure.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：addCommMonoid : AddCommMonoid (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (OuterMeasure α) := fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-23")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply
/-
**MeasureTheory.OuterMeasure.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.OuterMeasure`。
形式化陈述：instDistribMulAction {R : Type*} [Monoid R] [DistribMulAction R Real>=0∞] 
[IsScalarTower R Real>=0∞ Real>=0∞] : DistribMulAction R (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction {R : Type*} [Monoid R] [DistribMulAction R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    DistribMulAction R (OuterMeasure α) := fast_instance% FunLike.distribMulAction
/-
**MeasureTheory.OuterMeasure.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：instModule {R : Type*} [Semiring R] [Module R Real>=0∞] [IsScalarTower R R
eal>=0∞ Real>=0∞] : Module R (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule {R : Type*} [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] :
    Module R (OuterMeasure α) := fast_instance% FunLike.module
/-
**MeasureTheory.OuterMeasure.instBot** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：instBot : Bot (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBot : Bot (OuterMeasure α) :=
  ⟨0⟩

@[simp]
/-
**MeasureTheory.OuterMeasure.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：coe_bot : (⊥ : OuterMeasure α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : (⊥ : OuterMeasure α) = 0 :=
  rfl
/-
**MeasureTheory.OuterMeasure.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：instPartialOrder : PartialOrder (OuterMeasure α) where le m₁ m₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (OuterMeasure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ hab hbc s := le_trans (hab s) (hbc s)
  le_antisymm _ _ hab hba := ext fun s => le_antisymm (hab s) (hba s)
/-
**MeasureTheory.OuterMeasure.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `M
easureTheory.OuterMeasure`。
形式化陈述：instIsOrderedAddMonoid {α : Type*} : IsOrderedAddMonoid (OuterMeasure α) w
here add_le_add_left _ _ h _ s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
-/
instance instIsOrderedAddMonoid {α : Type*} : IsOrderedAddMonoid (OuterMeasure α) where
  add_le_add_left _ _ h _ s := add_le_add_left (h s) _
/-
**MeasureTheory.OuterMeasure.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：orderBot : OrderBot (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot : OrderBot (OuterMeasure α) :=
  { bot := 0,
    bot_le := fun a s => by simp only [zero_apply, zero_le] }
/-
**MeasureTheory.OuterMeasure.univ_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：univ_eq_zero_iff (m : OuterMeasure α) : m univ = 0 ↔ m = 0
参数：m : OuterMeasure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem univ_eq_zero_iff (m : OuterMeasure α) : m univ = 0 ↔ m = 0 :=
  ⟨fun h => bot_unique fun s => (measure_mono <| subset_univ s).trans_eq h, fun h => h.symm ▸ rfl⟩

section Supremum

/-
**MeasureTheory.OuterMeasure.instSupSet** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：instSupSet : SupSet (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSupSet : SupSet (OuterMeasure α) :=
  ⟨fun ms =>
    { measureOf := fun s => ⨆ m ∈ ms, (m : OuterMeasure α) s
      empty := nonpos_iff_eq_zero.1 <| iSup₂_le fun m _ => le_of_eq m.empty
      mono := fun {_ _} hs => iSup₂_mono fun m _ => m.mono hs
      iUnion_nat := fun f _ =>
        iSup₂_le fun m hm =>
          calc
            m (⋃ i, f i) ≤ ∑' i : ℕ, m (f i) := measure_iUnion_le _
            _ ≤ ∑' i, ⨆ m ∈ ms, (m : OuterMeasure α) (f i) :=
               ENNReal.tsum_le_tsum fun i => by apply le_iSup₂ m hm
             }⟩
/-
**MeasureTheory.OuterMeasure.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.OuterMeasure`。
形式化陈述：instCompleteLattice : CompleteLattice (OuterMeasure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLattice : CompleteLattice (OuterMeasure α) :=
  { OuterMeasure.orderBot,
    completeLatticeOfSup (OuterMeasure α) fun ms =>
      ⟨fun m hm s => by apply le_iSup₂ m hm, fun _ hm s => iSup₂_le fun _ hm' => hm hm' s⟩ with }

@[simp]
/-
**MeasureTheory.OuterMeasure.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：sSup_apply (ms : Set (OuterMeasure α)) (s : Set α) : (sSup ms) s = ⨆ m in 
ms, (m : OuterMeasure α) s
参数：ms : Set (OuterMeasure α)；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_apply (ms : Set (OuterMeasure α)) (s : Set α) :
    (sSup ms) s = ⨆ m ∈ ms, (m : OuterMeasure α) s :=
  rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.iSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：iSup_apply {ι} (f : ι -> OuterMeasure α) (s : Set α) : (⨆ i : ι, f i) s = 
⨆ i, f i s
参数：f : ι -> OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `MeasureTheory.OuterMeasure.sSup_apply`：sSup_apply (ms : Set (OuterMeasur
e α)) (s : Set α) : (sSup ms) s = ⨆ m in ms, (m : OuterMeasure α) s
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem iSup_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s := by
  rw [iSup, sSup_apply, iSup_range]

@[norm_cast]
/-
**MeasureTheory.OuterMeasure.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：coe_iSup {ι} (f : ι -> OuterMeasure α) : ⇑(⨆ i, f i) = ⨆ i, ⇑(f i)
参数：f : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iSup {ι} (f : ι → OuterMeasure α) : ⇑(⨆ i, f i) = ⨆ i, ⇑(f i) :=
  funext fun s => by simp

@[simp]
/-
**MeasureTheory.OuterMeasure.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：sup_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s
参数：m₁ m₂ : OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_bool_eq`：iSup_bool_eq {f : Bool -> α} : ⨆ b : Bool, f b = f true ⊔ 
f false
-/
theorem sup_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s := by
  have := iSup_apply (fun b => cond b m₁ m₂) s; rwa [iSup_bool_eq, iSup_bool_eq] at this
/-
**MeasureTheory.OuterMeasure.smul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：smul_iSup {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞
] {ι : Sort*} (f : ι -> OuterMeasure α) (c : R) : (c • ⨆ i, f i) = ⨆ i, c • f i
参数：f : ι -> OuterMeasure α；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用引理 `ENNReal.smul_iSup`：smul_iSup {R} [SMul R Real>=0∞] [IsScalarTower R Real
>=0∞ Real>=0∞] (f : ι -> Real>=0∞) (c : R) : c • ⨆ i, f i = ⨆ i, c • f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_iSup {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {ι : Sort*} (f : ι → OuterMeasure α) (c : R) :
    (c • ⨆ i, f i) = ⨆ i, c • f i :=
  ext fun s => by simp only [smul_apply, iSup_apply, ENNReal.smul_iSup]

end Supremum

@[mono, gcongr]
/-
**MeasureTheory.OuterMeasure.mono''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Out
erMeasure`。
形式化陈述：mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ <= m₂) (hs : s₁ s
ubseteq s₂) : m₁ s₁ <= m₂ s₂
参数：hm : m₁ <= m₂；hs : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
-/
theorem mono'' {m₁ m₂ : OuterMeasure α} {s₁ s₂ : Set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) :
    m₁ s₁ ≤ m₂ s₂ :=
  (hm s₁).trans (m₂.mono hs)

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
/-
**MeasureTheory.OuterMeasure.map** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.OuterM
easure`。
形式化陈述：map {β} (f : α -> β) : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure β where t
oFun m
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0

--- 原说明 ---
The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (
f ⁻¹' s)`.
-/
def map {β} (f : α → β) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β where
  toFun m :=
    { measureOf := fun s => m (f ⁻¹' s)
      empty := m.empty
      mono := fun {_ _} h => m.mono (preimage_mono h)
      iUnion_nat := fun s _ => by simpa using measure_iUnion_le fun i => f ⁻¹' s i }
  map_add' _ _ := coe_fn_injective rfl
  map_smul' _ _ := coe_fn_injective rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：map_apply {β} (f : α -> β) (m : OuterMeasure α) (s : Set β) : map f m s = 
m (f ⁻¹' s)
参数：f : α -> β；m : OuterMeasure α；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem map_apply {β} (f : α → β) (m : OuterMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s) :=
  rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.map_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Out
erMeasure`。
形式化陈述：map_id (m : OuterMeasure α) : map id m = m
参数：m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem map_id (m : OuterMeasure α) : map id m = m :=
  ext fun _ => rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：map_map {β γ} (f : α -> β) (g : β -> γ) (m : OuterMeasure α) : map g (map 
f m) = map (g ∘ f) m
参数：f : α -> β；g : β -> γ；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem map_map {β γ} (f : α → β) (g : β → γ) (m : OuterMeasure α) :
    map g (map f m) = map (g ∘ f) m :=
  ext fun _ => rfl

@[gcongr, mono]
/-
**MeasureTheory.OuterMeasure.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：map_mono {β} (f : α -> β) : Monotone (map f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mono {β} (f : α → β) : Monotone (map f) := fun _ _ h _ => h _

@[simp]
/-
**MeasureTheory.OuterMeasure.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：map_sup {β} (f : α -> β) (m m' : OuterMeasure α) : map f (m ⊔ m') = map f 
m ⊔ map f m'
参数：f : α -> β；m m' : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.sup_apply`：sup_apply (m₁ m₂ : OuterMeasure α)
 (s : Set α) : (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_sup {β} (f : α → β) (m m' : OuterMeasure α) : map f (m ⊔ m') = map f m ⊔ map f m' :=
  ext fun s => by simp only [map_apply, sup_apply]

@[simp]
/-
**MeasureTheory.OuterMeasure.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：map_iSup {β ι} (f : α -> β) (m : ι -> OuterMeasure α) : map f (⨆ i, m i) =
 ⨆ i, map f (m i)
参数：f : α -> β；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_iSup {β ι} (f : α → β) (m : ι → OuterMeasure α) : map f (⨆ i, m i) = ⨆ i, map f (m i) :=
  ext fun s => by simp only [map_apply, iSup_apply]
/-
**MeasureTheory.OuterMeasure.instFunctor** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：instFunctor : Functor OuterMeasure where map {_ _} f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunctor : Functor OuterMeasure where map {_ _} f := map f
/-
**MeasureTheory.OuterMeasure.instLawfulFunctor** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.OuterMeasure`。
形式化陈述：instLawfulFunctor : LawfulFunctor OuterMeasure
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLawfulFunctor : LawfulFunctor OuterMeasure := by constructor <;> intros <;> rfl

/-- The dirac outer measure. -/
/-
**MeasureTheory.OuterMeasure.dirac** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Oute
rMeasure`。
形式化陈述：dirac (a : α) : OuterMeasure α where measureOf s
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dirac outer measure.
-/
def dirac (a : α) : OuterMeasure α where
  measureOf s := indicator s (fun _ => 1) a
  empty := by simp
  mono {_ _} h := by grw [h]
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := ℝ≥0∞) rfl _ _ _
    _ ≤ ∑' n, indicator (s n) 1 a := iSup_le fun _ ↦ ENNReal.le_tsum _

@[simp]
/-
**MeasureTheory.OuterMeasure.dirac_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a :=
  rfl

/-- The sum of an (arbitrary) collection of outer measures. -/
/-
**MeasureTheory.OuterMeasure.sum** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.OuterM
easure`。
形式化陈述：sum {ι} (f : ι -> OuterMeasure α) : OuterMeasure α where measureOf s
参数：f : ι -> OuterMeasure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of an (arbitrary) collection of outer measures.
-/
def sum {ι} (f : ι → OuterMeasure α) : OuterMeasure α where
  measureOf s := ∑' i, f i s
  empty := by simp
  mono {_ _} h := ENNReal.tsum_le_tsum fun _ => measure_mono h
  iUnion_nat s _ := by
    rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun i => measure_iUnion_le _

@[simp]
/-
**MeasureTheory.OuterMeasure.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：sum_apply {ι} (f : ι -> OuterMeasure α) (s : Set α) : sum f s = ∑' i, f i 
s
参数：f : ι -> OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_apply {ι} (f : ι → OuterMeasure α) (s : Set α) : sum f s = ∑' i, f i s :=
  rfl
/-
**MeasureTheory.OuterMeasure.smul_dirac_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：smul_dirac_apply (a : Real>=0∞) (b : α) (s : Set α) : (a • dirac b) s = in
dicator s (fun _ => a) b
参数：a : Real>=0∞；b : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.indicator_mul_right`：indicator_mul_right (s : Set ι) (f g : ι -> M₀)
 : indicator s (fun j => f j * g j) i = f i * indicator s g i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_dirac_apply (a : ℝ≥0∞) (b : α) (s : Set α) :
    (a • dirac b) s = indicator s (fun _ => a) b := by
  simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ fun _ => a, mul_one]

/-- Pullback of an `OuterMeasure`: `comap f μ s = μ (f '' s)`. -/
/-
**MeasureTheory.OuterMeasure.comap** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Oute
rMeasure`。
形式化陈述：comap {β} (f : α -> β) : OuterMeasure β ->ₗ[Real>=0∞] OuterMeasure α where
 toFun m
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of an `OuterMeasure`: `comap f μ s = μ (f '' s)`.
-/
def comap {β} (f : α → β) : OuterMeasure β →ₗ[ℝ≥0∞] OuterMeasure α where
  toFun m :=
    { measureOf := fun s => m (f '' s)
      empty := by simp
      mono := fun {_ _} h => by gcongr
      iUnion_nat := fun s _ => by simpa only [image_iUnion] using measure_iUnion_le _ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**MeasureTheory.OuterMeasure.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.OuterMeasure`。
形式化陈述：comap_apply {β} (f : α -> β) (m : OuterMeasure β) (s : Set α) : comap f m 
s = m (f '' s)
参数：f : α -> β；m : OuterMeasure β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem comap_apply {β} (f : α → β) (m : OuterMeasure β) (s : Set α) : comap f m s = m (f '' s) :=
  rfl

@[gcongr, mono]
/-
**MeasureTheory.OuterMeasure.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：comap_mono {β} (f : α -> β) : Monotone (comap f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mono {β} (f : α → β) : Monotone (comap f) := fun _ _ h _ => h _

@[simp]
/-
**MeasureTheory.OuterMeasure.comap_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：comap_iSup {β ι} (f : α -> β) (m : ι -> OuterMeasure β) : comap f (⨆ i, m 
i) = ⨆ i, comap f (m i)
参数：f : α -> β；m : ι -> OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.iSup_apply`：iSup_apply {ι} (f : ι -> OuterMea
sure α) (s : Set α) : (⨆ i : ι, f i) s = ⨆ i, f i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_iSup {β ι} (f : α → β) (m : ι → OuterMeasure β) :
    comap f (⨆ i, m i) = ⨆ i, comap f (m i) :=
  ext fun s => by simp only [comap_apply, iSup_apply]

/-- Restrict an `OuterMeasure` to a set. -/
/-
**MeasureTheory.OuterMeasure.restrict** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.O
uterMeasure`。
形式化陈述：restrict (s : Set α) : OuterMeasure α ->ₗ[Real>=0∞] OuterMeasure α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an `OuterMeasure` to a set.
-/
def restrict (s : Set α) : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure α :=
  (map (↑)).comp (comap ((↑) : s → α))

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
@[simp]
/-
**MeasureTheory.OuterMeasure.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：restrict_apply (s t : Set α) (m : OuterMeasure α) : restrict s m t = m (t 
inter s)
参数：s t : Set α；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_apply (s t : Set α) (m : OuterMeasure α) : restrict s m t = m (t ∩ s) := by
  simp [restrict, inter_comm t]

@[mono]
/-
**MeasureTheory.OuterMeasure.restrict_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：restrict_mono {s t : Set α} (h : s subseteq t) {m m' : OuterMeasure α} (hm
 : m <= m') : restrict s m <= restrict t m'
参数：h : s subseteq t；hm : m <= m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
-/
theorem restrict_mono {s t : Set α} (h : s ⊆ t) {m m' : OuterMeasure α} (hm : m ≤ m') :
    restrict s m ≤ restrict t m' := fun u => by
  simp only [restrict_apply]
  exact (hm _).trans (m'.mono <| inter_subset_inter_right _ h)

@[simp]
/-
**MeasureTheory.OuterMeasure.restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：restrict_univ (m : OuterMeasure α) : restrict univ m = m
参数：m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_univ (m : OuterMeasure α) : restrict univ m = m :=
  ext fun s => by simp

@[simp]
/-
**MeasureTheory.OuterMeasure.restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.OuterMeasure`。
形式化陈述：restrict_empty (m : OuterMeasure α) : restrict ∅ m = 0
参数：m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsZeroApplySetENNReal`：∀ {α : Type u_1}, 
IsZeroApply (MeasureTheory.OuterMeasure α) (Set α) ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_empty (m : OuterMeasure α) : restrict ∅ m = 0 :=
  ext fun s => by simp

@[simp]
/-
**MeasureTheory.OuterMeasure.restrict_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.OuterMeasure`。
形式化陈述：restrict_iSup {ι} (s : Set α) (m : ι -> OuterMeasure α) : restrict s (⨆ i,
 m i) = ⨆ i, restrict s (m i)
参数：s : Set α；m : ι -> OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_iSup`：comap_iSup {β ι} (f : α -> β) (m 
: ι -> OuterMeasure β) : comap f (⨆ i, m i) = ⨆ i, comap f (m i)
· 使用定理 `MeasureTheory.OuterMeasure.map_iSup`：map_iSup {β ι} (f : α -> β) (m : ι 
-> OuterMeasure α) : map f (⨆ i, m i) = ⨆ i, map f (m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrict_iSup {ι} (s : Set α) (m : ι → OuterMeasure α) :
    restrict s (⨆ i, m i) = ⨆ i, restrict s (m i) := by simp [restrict]
/-
**MeasureTheory.OuterMeasure.map_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：map_comap {β} (f : α -> β) (m : OuterMeasure β) : map f (comap f m) = rest
rict (range f) m
参数：f : α -> β；m : OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comap {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) = restrict (range f) m :=
  ext fun s => congr_arg m <| by simp only [image_preimage_eq_inter_range, Subtype.range_coe]
/-
**MeasureTheory.OuterMeasure.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：map_comap_le {β} (f : α -> β) (m : OuterMeasure β) : map f (comap f m) <= 
m
参数：f : α -> β；m : OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem map_comap_le {β} (f : α → β) (m : OuterMeasure β) : map f (comap f m) ≤ m := fun _ =>
  m.mono <| image_preimage_subset _ _
/-
**MeasureTheory.OuterMeasure.restrict_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.OuterMeasure`。
形式化陈述：restrict_le_self (m : OuterMeasure α) (s : Set α) : restrict s m <= m
参数：m : OuterMeasure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.map_comap_le`：map_comap_le {β} (f : α -> β) (
m : OuterMeasure β) : map f (comap f m) <= m
-/
theorem restrict_le_self (m : OuterMeasure α) (s : Set α) : restrict s m ≤ m :=
  map_comap_le _ _

@[simp]
/-
**MeasureTheory.OuterMeasure.map_le_restrict_range** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：map_le_restrict_range {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f :
 α -> β} : map f ma <= restrict (range f) mb ↔ map f ma <= mb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.restrict_le_self`：restrict_le_self (m : Outer
Measure α) (s : Set α) : restrict s m <= m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem map_le_restrict_range {β} {ma : OuterMeasure α} {mb : OuterMeasure β} {f : α → β} :
    map f ma ≤ restrict (range f) mb ↔ map f ma ≤ mb :=
  ⟨fun h => h.trans (restrict_le_self _ _), fun h s => by simpa using h (s ∩ range f)⟩
/-
**MeasureTheory.OuterMeasure.map_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.OuterMeasure`。
形式化陈述：map_comap_of_surjective {β} {f : α -> β} (hf : Surjective f) (m : OuterMea
sure β) : map f (comap f m) = m
参数：hf : Surjective f；m : OuterMeasure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.map_apply`：map_apply {β} (f : α -> β) (m : Ou
terMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s)
· 使用定理 `MeasureTheory.OuterMeasure.comap_apply`：comap_apply {β} (f : α -> β) (m 
: OuterMeasure β) (s : Set α) : comap f m s = m (f '' s)
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
-/
theorem map_comap_of_surjective {β} {f : α → β} (hf : Surjective f) (m : OuterMeasure β) :
    map f (comap f m) = m :=
  ext fun s => by rw [map_apply, comap_apply, hf.image_preimage]
/-
**MeasureTheory.OuterMeasure.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.OuterMeasure`。
形式化陈述：le_comap_map {β} (f : α -> β) (m : OuterMeasure α) : m <= comap f (map f m
)
参数：f : α -> β；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem le_comap_map {β} (f : α → β) (m : OuterMeasure α) : m ≤ comap f (map f m) := fun _ =>
  m.mono <| subset_preimage_image _ _
/-
**MeasureTheory.OuterMeasure.comap_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：comap_map {β} {f : α -> β} (hf : Injective f) (m : OuterMeasure α) : comap
 f (map f m) = m
参数：hf : Injective f；m : OuterMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_apply`：comap_apply {β} (f : α -> β) (m 
: OuterMeasure β) (s : Set α) : comap f m s = m (f '' s)
· 使用定理 `MeasureTheory.OuterMeasure.map_apply`：map_apply {β} (f : α -> β) (m : Ou
terMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s)
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
-/
theorem comap_map {β} {f : α → β} (hf : Injective f) (m : OuterMeasure α) : comap f (map f m) = m :=
  ext fun s => by rw [comap_apply, map_apply, hf.preimage_image]

@[simp]
/-
**MeasureTheory.OuterMeasure.top_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：top_apply {s : Set α} (h : s.Nonempty) : (⊤ : OuterMeasure α) s = ∞
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsSMulApplySetENNReal`：∀ {α : Type u_1} {
R : Type u_3} [inst : SMul R ENNReal] [inst_1 : IsScalarTower R ENNReal ENNReal]
,   IsSMulApply R (MeasureTheory.OuterMeas…
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `trivial`：True
-/
theorem top_apply {s : Set α} (h : s.Nonempty) : (⊤ : OuterMeasure α) s = ∞ :=
  let ⟨a, as⟩ := h
  top_unique <| le_trans (by simp [as]) (le_iSup₂ (∞ • dirac a) trivial)
/-
**MeasureTheory.OuterMeasure.top_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.OuterMeasure`。
形式化陈述：top_apply' (s : Set α) : (⊤ : OuterMeasure α) s = ⨅ _ : s = ∅, 0
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `MeasureTheory.OuterMeasure.top_apply`：top_apply {s : Set α} (h : s.Nonem
pty) : (⊤ : OuterMeasure α) s = ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem top_apply' (s : Set α) : (⊤ : OuterMeasure α) s = ⨅ _ : s = ∅, 0 :=
  s.eq_empty_or_nonempty.elim (fun h => by simp [h]) fun h => by simp [h, h.ne_empty]

@[simp]
/-
**MeasureTheory.OuterMeasure.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：comap_top (f : α -> β) : comap f ⊤ = ⊤
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext_nonempty`：ext_nonempty {μ₁ μ₂ : OuterMeas
ure α} (h : forall s : Set α, s.Nonempty -> μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.comap_apply`：comap_apply {β} (f : α -> β) (m 
: OuterMeasure β) (s : Set α) : comap f m s = m (f '' s)
· 使用定理 `MeasureTheory.OuterMeasure.top_apply`：top_apply {s : Set α} (h : s.Nonem
pty) : (⊤ : OuterMeasure α) s = ∞
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem comap_top (f : α → β) : comap f ⊤ = ⊤ :=
  ext_nonempty fun s hs => by rw [comap_apply, top_apply hs, top_apply (hs.image _)]
/-
**MeasureTheory.OuterMeasure.map_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Ou
terMeasure`。
形式化陈述：map_top (f : α -> β) : map f ⊤ = restrict (range f) ⊤
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ext`：ext {μ₁ μ₂ : OuterMeasure α} (h : forall
 s, μ₁ s = μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.map_apply`：map_apply {β} (f : α -> β) (m : Ou
terMeasure α) (s : Set β) : map f m s = m (f ⁻¹' s)
· 使用定理 `MeasureTheory.OuterMeasure.restrict_apply`：restrict_apply (s t : Set α) 
(m : OuterMeasure α) : restrict s m t = m (t inter s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `MeasureTheory.OuterMeasure.top_apply'`：top_apply' (s : Set α) : (⊤ : Out
erMeasure α) s = ⨅ _ : s = ∅, 0
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
-/
theorem map_top (f : α → β) : map f ⊤ = restrict (range f) ⊤ :=
  ext fun s => by
    rw [map_apply, restrict_apply, ← image_preimage_eq_inter_range, top_apply', top_apply',
      Set.image_eq_empty]

@[simp]
/-
**MeasureTheory.OuterMeasure.map_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.OuterMeasure`。
形式化陈述：map_top_of_surjective (f : α -> β) (hf : Surjective f) : map f ⊤ = ⊤
参数：f : α -> β；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.map_top`：map_top (f : α -> β) : map f ⊤ = res
trict (range f) ⊤
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `MeasureTheory.OuterMeasure.restrict_univ`：restrict_univ (m : OuterMeasur
e α) : restrict univ m = m
-/
theorem map_top_of_surjective (f : α → β) (hf : Surjective f) : map f ⊤ = ⊤ := by
  rw [map_top, hf.range_eq, restrict_univ]

end Basic

end OuterMeasure

end MeasureTheory

