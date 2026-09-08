/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Limits of intervals along filters

This file contains some lemmas about how filters `Ixx` behave as the endpoints tend to `±∞`.

-/

public section

namespace Finset

open Filter

section Asymmetric

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α]

/-
**Finset.tendsto_Icc_atBot_prod_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Icc_atBot_prod_atTop : Tendsto (fun p : α × α => Icc p.1 p.2) (atB
ot ×ˢ atTop) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma tendsto_Icc_atBot_prod_atTop :
    Tendsto (fun p : α × α ↦ Icc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_le_atBot i).prod_mk (eventually_ge_atTop i)
/-
**Finset.tendsto_Ioc_atBot_prod_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioc_atBot_prod_atTop [NoBotOrder α] : Tendsto (fun p : α × α => Io
c p.1 p.2) (atBot ×ˢ atTop) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.eventually_lt_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotO
rder α] (a : α), ∀ᶠ (x : α) in Filter.atBot, x < a
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma tendsto_Ioc_atBot_prod_atTop [NoBotOrder α] :
    Tendsto (fun p : α × α ↦ Ioc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_lt_atBot i).prod_mk (eventually_ge_atTop i)
/-
**Finset.tendsto_Ico_atBot_prod_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ico_atBot_prod_atTop [NoTopOrder α] : Tendsto (fun p : α × α => Fi
nset.Ico p.1 p.2) (atBot ×ˢ atTop) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
-/
lemma tendsto_Ico_atBot_prod_atTop [NoTopOrder α] :
    Tendsto (fun p : α × α ↦ Finset.Ico p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_le_atBot i).prod_mk (eventually_gt_atTop i)
/-
**Finset.tendsto_Ioo_atBot_prod_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioo_atBot_prod_atTop [NoBotOrder α] [NoTopOrder α] : Tendsto (fun 
p : α × α => Finset.Ioo p.1 p.2) (atBot ×ˢ atTop) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.eventually_lt_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotO
rder α] (a : α), ∀ᶠ (x : α) in Filter.atBot, x < a
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
-/
lemma tendsto_Ioo_atBot_prod_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun p : α × α ↦ Finset.Ioo p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_lt_atBot i).prod_mk (eventually_gt_atTop i)

end Asymmetric

section Symmetric

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [LocallyFiniteOrder α]

/-
**Finset.tendsto_Icc_neg_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Icc_neg_atTop_atTop : Tendsto (fun a : α => Icc (-a) a) atTop atTo
p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Icc_atBot_prod_atTop`：tendsto_Icc_atBot_prod_atTop : Tend
sto (fun p : α × α => Icc p.1 p.2) (atBot ×ˢ atTop) atTop
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_Icc_neg_atTop_atTop :
    Tendsto (fun a : α ↦ Icc (-a) a) atTop atTop :=
  tendsto_Icc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)
/-
**Finset.tendsto_Ioc_neg_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioc_neg_atTop_atTop [NoBotOrder α] : Tendsto (fun a : α => Ioc (-a
) a) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ioc_atBot_prod_atTop`：tendsto_Ioc_atBot_prod_atTop [NoBot
Order α] : Tendsto (fun p : α × α => Ioc p.1 p.2) (atBot ×ˢ atTop) atTop
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_Ioc_neg_atTop_atTop [NoBotOrder α] :
    Tendsto (fun a : α ↦ Ioc (-a) a) atTop atTop :=
  tendsto_Ioc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)
/-
**Finset.tendsto_Ico_neg_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ico_neg_atTop_atTop [NoTopOrder α] : Tendsto (fun a : α => Ico (-a
) a) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ico_atBot_prod_atTop`：tendsto_Ico_atBot_prod_atTop [NoTop
Order α] : Tendsto (fun p : α × α => Finset.Ico p.1 p.2) (atBot ×ˢ atTop) atTop
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_Ico_neg_atTop_atTop [NoTopOrder α] :
    Tendsto (fun a : α ↦ Ico (-a) a) atTop atTop :=
  tendsto_Ico_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)
/-
**Finset.tendsto_Ioo_neg_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioo_neg_atTop_atTop [NoBotOrder α] [NoTopOrder α] : Tendsto (fun a
 : α => Ioo (-a) a) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ioo_atBot_prod_atTop`：tendsto_Ioo_atBot_prod_atTop [NoBot
Order α] [NoTopOrder α] : Tendsto (fun p : α × α => Finset.Ioo p.1 p.2) (atBot ×
ˢ atTop) atTop
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_Ioo_neg_atTop_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun a : α ↦ Ioo (-a) a) atTop atTop :=
  tendsto_Ioo_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

end Symmetric

section NatCast

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [LocallyFiniteOrder R]
  [Archimedean R]

/-
**Finset.tendsto_Icc_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Icc_neg : Tendsto (fun n : Nat => Icc (-n : R) n) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Icc_neg_atTop_atTop`：tendsto_Icc_neg_atTop_atTop : Tendst
o (fun a : α => Icc (-a) a) atTop atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
lemma tendsto_Icc_neg :
    Tendsto (fun n : ℕ ↦ Icc (-n : R) n) atTop atTop :=
  tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

variable [Nontrivial R]
/-
**Finset.tendsto_Ioc_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioc_neg : Tendsto (fun n : Nat => Ioc (-n : R) n) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ioc_neg_atTop_atTop`：tendsto_Ioc_neg_atTop_atTop [NoBotOr
der α] : Tendsto (fun a : α => Ioc (-a) a) atTop atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
lemma tendsto_Ioc_neg : Tendsto (fun n : ℕ ↦ Ioc (-n : R) n) atTop atTop :=
  tendsto_Ioc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop
/-
**Finset.tendsto_Ico_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ico_neg : Tendsto (fun n : Nat => Ico (-n : R) n) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ico_neg_atTop_atTop`：tendsto_Ico_neg_atTop_atTop [NoTopOr
der α] : Tendsto (fun a : α => Ico (-a) a) atTop atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
lemma tendsto_Ico_neg : Tendsto (fun n : ℕ ↦ Ico (-n : R) n) atTop atTop :=
  tendsto_Ico_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop
/-
**Finset.tendsto_Ioo_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：tendsto_Ioo_neg : Tendsto (fun n : Nat => Ioo (-n : R) n) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Finset.tendsto_Ioo_neg_atTop_atTop`：tendsto_Ioo_neg_atTop_atTop [NoBotOr
der α] [NoTopOrder α] : Tendsto (fun a : α => Ioo (-a) a) atTop atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
lemma tendsto_Ioo_neg : Tendsto (fun n : ℕ ↦ Ioo (-n : R) n) atTop atTop :=
  tendsto_Ioo_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

end NatCast

end Finset

