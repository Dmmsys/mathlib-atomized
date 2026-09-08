/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Rel

/-!
# Pseudometrics as bundled functions

This file defines a pseudometric as a bundled function.
This allows one to define a semilattice on them, and to construct families of pseudometrics.

## Implementation notes

The `PseudoMetric` definition is made as general as possible without any required axioms
for the codomain. The axioms come into play only in proofs and further constructions
like the `SemilatticeSup` instance. This allows one to talk about functions mapping into
something like `{ fuel: ℕ, time: ℕ }` even though there is no linear order.

In most cases, the codomain will be a linear ordered additive monoid like
`ℝ`, `ℝ≥0`, `ℝ≥0∞`, in which all of the axioms below are satisfied.

-/

public section

variable {X R : Type*}

variable (X R) in
/-- A pseudometric as a bundled function. -/
@[ext]
/-
**PseudoMetric** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → (R : Type u_2) → [Zero R] → [Add R] → [LE R] → Type (max u_1 u_
2)
参数：R : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudometric as a bundled function.
-/
structure PseudoMetric [Zero R] [Add R] [LE R] where
  /-- The underlying binary function mapping into a linearly ordered additive monoid. -/
  toFun : X → X → R
  /-- A pseudometric must take identical elements to 0. -/
  refl' x : toFun x x = 0
  /-- A pseudometric must be symmetric. -/
  symm' x y : toFun x y = toFun y x
  /-- A pseudometric must respect the triangle inequality. -/
  triangle' x y z : toFun x z ≤ toFun x y + toFun y z

namespace PseudoMetric

section Basic

variable [Zero R] [Add R] [LE R] (d : PseudoMetric X R)

/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (PseudoMetric X R) X (X → R) where
  coe := PseudoMetric.toFun
  coe_injective _ := by aesop

@[simp, norm_cast]
/-
**PseudoMetric.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：coe_mk (d : X -> X -> R) (refl symm triangle) : mk d refl symm triangle = 
d
参数：d : X -> X -> R；refl symm triangle。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (d : X → X → R) (refl symm triangle) : mk d refl symm triangle = d := rfl
/-
**PseudoMetric.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：mk_apply (d : X -> X -> R) (refl symm triangle) (x y : X) : mk d refl symm
 triangle x y = d x y
参数：d : X -> X -> R；refl symm triangle；x y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply (d : X → X → R) (refl symm triangle) (x y : X) :
    mk d refl symm triangle x y = d x y :=
  rfl

@[simp]
/-
**PseudoMetric.refl** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst_1 : Add R] [inst_2 :
 LE R] (d : PseudoMetric X R) (x : X),   d x x = 0
参数：d : PseudoMetric X R；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetric.refl'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [ins
t_1 : Add R] [inst_2 : LE R] (self : PseudoMetric X R) (x : X),   self.toFun x x
 = 0
-/
protected lemma refl (x : X) : d x x = 0 := d.refl' x
/-
**PseudoMetric.symm** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst_1 : Add R] [inst_2 :
 LE R] (d : PseudoMetric X R) (x y : X),   d x y = d y x
参数：d : PseudoMetric X R；x y : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetric.symm'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [ins
t_1 : Add R] [inst_2 : LE R] (self : PseudoMetric X R) (x y : X),   self.toFun x
 y = sel…
-/
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
/-
**PseudoMetric.triangle** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst_1 : Add R] [inst_2 :
 LE R] (d : PseudoMetric X R) (x y z : X),   d x z ≤ d x y + d y z
参数：d : PseudoMetric X R；x y z : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetric.triangle'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] 
[inst_1 : Add R] [inst_2 : LE R] (self : PseudoMetric X R) (x y z : X),   self.t
oFun x z ≤ s…
-/
protected lemma triangle (x y z : X) : d x z ≤ d x y + d y z := d.triangle' x y z
/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (PseudoMetric X R) := ⟨fun d d' ↦ ⇑d ≤ d'⟩

@[simp, norm_cast]
/-
**PseudoMetric.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst_1 : Add R] [inst_2 :
 LE R] {d d' : PseudoMetric X R},   ⇑d ≤ ⇑d' ↔ d ≤ d'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma coe_le_coe {d d' : PseudoMetric X R} :
    (d : X → X → R) ≤ d' ↔ d ≤ d' :=
  Iff.rfl

end Basic

/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [Add R] [PartialOrder R] : PartialOrder (PseudoMetric X R) :=
  .lift _ DFunLike.coe_injective
/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass R] [Preorder R] : Bot (PseudoMetric X R) where
  bot.toFun := 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]
/-
**PseudoMetric.coe_bot** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：coe_bot [AddZeroClass R] [Preorder R] : ⇑(⊥ : PseudoMetric X R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_bot [AddZeroClass R] [Preorder R] : ⇑(⊥ : PseudoMetric X R) = 0 := rfl

@[simp]
/-
**PseudoMetric.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : AddZeroClass R] [inst_1 : Preorder
 R] (x y : X), ⊥ x y = 0
参数：x y : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma bot_apply [AddZeroClass R] [Preorder R] (x y : X) :
    (⊥ : PseudoMetric X R) x y = 0 :=
  rfl
/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    Max (PseudoMetric X R) where
  max d d' := {
    toFun := fun x y ↦ (d x y) ⊔ (d' x y)
    refl' _ := by simp
    symm' x y := by simp [d.symm, d'.symm]
    triangle' := by
      intro x y z
      simp only [sup_le_iff]
      refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
      apply add_le_add <;> simp
  }

@[simp, push_cast]
/-
**PseudoMetric.coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：coe_sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono 
R] (d d' : PseudoMetric X R) : ((d ⊔ d' : PseudoMetric X R) : X -> X -> R) = (d 
: X -> X -> R) ⊔ d'
参数：d d' : PseudoMetric X R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) :
    ((d ⊔ d' : PseudoMetric X R) : X → X → R) = (d : X → X → R) ⊔ d' := rfl

@[simp]
/-
**PseudoMetric.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : AddZeroClass R] [inst_1 : Semilatt
iceSup R] [inst_2 : AddLeftMono R]   [inst_3 : AddRightMono R] (d d' : PseudoMet
ric X R) (x y : X), (d ⊔ d') x y = d x y ⊔ d' x y
参数：d d' : PseudoMetric X R；x y : X；d ⊔ d'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma sup_apply [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) (x y : X) :
    (d ⊔ d') x y = d x y ⊔ d' x y :=
  rfl
/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    SemilatticeSup (PseudoMetric X R) where
  sup := max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe]
  sup_le _ _ _ := fun h h' _ _ ↦ sup_le (h _ _) (h' _ _)

section OrderBot

variable [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]

/-
**PseudoMetric.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : AddCommMonoid R] [inst_1 : LinearO
rder R] [AddLeftStrictMono R]   (d : PseudoMetric X R) (x y : X), 0 ≤ d x y
参数：d : PseudoMetric X R；x y : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `PseudoMetric.triangle'`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] 
[inst_1 : Add R] [inst_2 : LE R] (self : PseudoMetric X R) (x y z : X),   self.t
oFun x z ≤ s…
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `PseudoMetric.symm`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst
_1 : Add R] [inst_2 : LE R] (d : PseudoMetric X R) (x y : X),   d x y = d y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `PseudoMetric.refl`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst
_1 : Add R] [inst_2 : LE R] (d : PseudoMetric X R) (x : X),   d x x = 0
-/
protected lemma nonneg (d : PseudoMetric X R) (x y : X) : 0 ≤ d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x ≤ d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.ne (d.refl x)
/-
**PseudoMetric.** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (PseudoMetric X R) where
  bot_le f _ _ := f.nonneg _ _

@[simp, push_cast]
/-
**PseudoMetric.coe_finsetSup** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：coe_finsetSup [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric X 
R} {s : Finset Y} (hs : s.Nonempty) : ⇑(s.sup f) = s.sup' hs (f ·)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
-/
lemma coe_finsetSup [IsOrderedAddMonoid R] {Y : Type*} {f : Y → PseudoMetric X R} {s : Finset Y}
    (hs : s.Nonempty) :
    ⇑(s.sup f) = s.sup' hs (f ·) := by
  simpa using (Finset.sup'_eq_sup hs (f ·)).symm
/-
**PseudoMetric.finsetSup_apply** 是 Mathlib 中的一个引理，位于命名空间 `PseudoMetric`。
形式化陈述：finsetSup_apply [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric 
X R} {s : Finset Y} (hs : s.Nonempty) (x y : X) : s.sup f x y = s.sup' hs fun i 
=> f i x y
参数：hs : s.Nonempty；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
lemma finsetSup_apply [IsOrderedAddMonoid R] {Y : Type*} {f : Y → PseudoMetric X R}
    {s : Finset Y} (hs : s.Nonempty) (x y : X) :
    s.sup f x y = s.sup' hs fun i ↦ f i x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

end OrderBot

section IsUltra

/-- A pseudometric can be nonarchimedean (or ultrametric), with a stronger triangle
inequality such that `d x z ≤ max (d x y) (d y z)`. -/
/-
**PseudoMetric.IsUltra** 是 Mathlib 中的一个归纳类型，位于命名空间 `PseudoMetric`。
形式化陈述：{X : Type u_1} →   {R : Type u_2} → [inst : Zero R] → [inst_1 : Add R] → [
inst_2 : LE R] → [Max R] → PseudoMetric X R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudometric can be nonarchimedean (or ultrametric), with a stronger triangle
inequality such that `d x z ≤ max (d x y) (d y z)`.
-/
class IsUltra [Zero R] [Add R] [LE R] [Max R] (d : PseudoMetric X R) : Prop where
  /-- Strong triangle inequality of an ultrametric. -/
  le_sup' : ∀ x y z, d x z ≤ d x y ⊔ d y z
/-
**PseudoMetric.IsUltra.le_sup** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric.IsUltra`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst_1 : Add R] [inst_2 :
 LE R] [inst_3 : Max R] {d : PseudoMetric X R}   [hd : d.IsUltra] {x y z : X}, d
 x z ≤ d x y ⊔ d y z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetric.IsUltra.le_sup'`：∀ {X : Type u_1} {R : Type u_2} {inst : Ze
ro R} {inst_1 : Add R} {inst_2 : LE R} {inst_3 : Max R} {d : PseudoMetric X R}  
 [self : d.IsUltra…
-/
lemma IsUltra.le_sup [Zero R] [Add R] [LE R] [Max R] {d : PseudoMetric X R} [hd : IsUltra d]
    {x y z : X} : d x z ≤ d x y ⊔ d y z :=
  hd.le_sup' x y z
/-
**PseudoMetric.IsUltra.bot** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric.IsUltra`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : AddZeroClass R] [inst_1 : Semilatt
iceSup R], ⊥.IsUltra
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance IsUltra.bot [AddZeroClass R] [SemilatticeSup R] :
    IsUltra (⊥ : PseudoMetric X R) where
  le_sup' := by simp
/-
**PseudoMetric.IsUltra.sup** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric.IsUltra`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : AddZeroClass R] [inst_1 : Semilatt
iceSup R] [inst_2 : AddLeftMono R]   [inst_3 : AddRightMono R] {d d' : PseudoMet
ric X R} [d.IsUltra] [d'.IsUltra], (d ⊔ d').IsUltra
参数：d ⊔ d'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `PseudoMetric.IsUltra.le_sup`：∀ {X : Type u_1} {R : Type u_2} [inst : Zer
o R] [inst_1 : Add R] [inst_2 : LE R] [inst_3 : Max R] {d : PseudoMetric X R}   
[hd : d.IsUltra] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
instance IsUltra.sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    {d d' : PseudoMetric X R} [IsUltra d] [IsUltra d'] : IsUltra (d ⊔ d') := by
  constructor
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z ≤ d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup le_sup le_sup
  _ ≤ d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_left_comm]
/-
**PseudoMetric.IsUltra.finsetSup** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric.IsUltra
`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} {Y : Type u_3} [inst : AddCommMonoid R] [i
nst_1 : LinearOrder R]   [inst_2 : AddLeftStrictMono R] [inst_3 : IsOrderedAddMo
noid R] {f : Y → PseudoMetric X R} {s : Finset Y},   (∀ d ∈ s, (f d).IsUltra) → 
(s.sup f).IsUltra
参数：∀ d ∈ s, (f d).IsUltra；s.sup f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `PseudoMetric.finsetSup_apply`：finsetSup_apply [IsOrderedAddMonoid R] {Y 
: Type*} {f : Y -> PseudoMetric X R} {s : Finset Y} (hs : s.Nonempty) (x y : X) 
: s.sup f x y = s.…
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PseudoMetric.IsUltra.le_sup'`：∀ {X : Type u_1} {R : Type u_2} {inst : Ze
ro R} {inst_1 : Add R} {inst_2 : LE R} {inst_3 : Max R} {d : PseudoMetric X R}  
 [self : d.IsUltra…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
-/
lemma IsUltra.finsetSup {Y : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]
    [IsOrderedAddMonoid R] {f : Y → PseudoMetric X R} {s : Finset Y} (h : ∀ d ∈ s, IsUltra (f d)) :
    IsUltra (s.sup f) := by
  constructor
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  have h := (h i hi).le_sup' x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

end IsUltra

section ball

/-
**PseudoMetric.isSymm_ball** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
形式化陈述：isSymm_ball [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R} :
 SetRel.IsSymm {xy | d xy.1 xy.2 < ε} where symm
参数：d : PseudoMetric X R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoMetric.symm`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst
_1 : Add R] [inst_2 : LE R] (d : PseudoMetric X R) (x y : X),   d x y = d y x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isSymm_ball [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R} :
    SetRel.IsSymm {xy | d xy.1 xy.2 < ε} where
  symm := by simp [d.symm]
/-
**PseudoMetric.isSymm_closedBall** 是 Mathlib 中的一个实例，位于命名空间 `PseudoMetric`。
形式化陈述：isSymm_closedBall [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R} :
 SetRel.IsSymm {xy | d xy.1 xy.2 <= ε} where symm
参数：d : PseudoMetric X R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoMetric.symm`：∀ {X : Type u_1} {R : Type u_2} [inst : Zero R] [inst
_1 : Add R] [inst_2 : LE R] (d : PseudoMetric X R) (x y : X),   d x y = d y x
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isSymm_closedBall [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R} :
    SetRel.IsSymm {xy | d xy.1 xy.2 ≤ ε} where
  symm := by simp [d.symm]
/-
**PseudoMetric.IsUltra.isTrans_ball** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetric.IsUl
tra`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Add R] [inst_1 : Zero R] [inst_2 :
 LinearOrder R] (d : PseudoMetric X R)   [d.IsUltra] {ε : R}, SetRel.IsTrans {xy
 | d xy.1 xy.2 < ε}
参数：d : PseudoMetric X R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `PseudoMetric.IsUltra.le_sup`：∀ {X : Type u_1} {R : Type u_2} [inst : Zer
o R] [inst_1 : Add R] [inst_2 : LE R] [inst_3 : Max R] {d : PseudoMetric X R}   
[hd : d.IsUltra] …
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
instance IsUltra.isTrans_ball [Add R] [Zero R] [LinearOrder R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
      SetRel.IsTrans {xy | d xy.1 xy.2 < ε} where
    trans _ _ _ hxy hyz := le_sup.trans_lt (max_lt hxy hyz)
/-
**PseudoMetric.IsUltra.isTrans_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetri
c.IsUltra`。
形式化陈述：∀ {X : Type u_1} {R : Type u_2} [inst : Add R] [inst_1 : Zero R] [inst_2 :
 SemilatticeSup R] (d : PseudoMetric X R)   [d.IsUltra] {ε : R}, SetRel.IsTrans 
{xy | d xy.1 xy.2 ≤ ε}
参数：d : PseudoMetric X R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PseudoMetric.IsUltra.le_sup`：∀ {X : Type u_1} {R : Type u_2} [inst : Zer
o R] [inst_1 : Add R] [inst_2 : LE R] [inst_3 : Max R] {d : PseudoMetric X R}   
[hd : d.IsUltra] …
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
instance IsUltra.isTrans_closedBall [Add R] [Zero R] [SemilatticeSup R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
    SetRel.IsTrans {xy | d xy.1 xy.2 ≤ ε} where
  trans _ _ _ hxy hyz := le_sup.trans (sup_le hxy hyz)

end ball

end PseudoMetric

