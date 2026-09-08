/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Support of a function in an order

This file relates the support of a function to order constructions.
-/

public section

assert_not_exists MonoidWithZero

open Set

variable {ι : Sort*} {α M : Type*}

namespace Function
variable [One M]

@[to_additive]
/-
**Function.mulSupport_sup** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_sup [SemilatticeSup M] (f g : α -> M) : mulSupport (fun x => f 
x ⊔ g x) subseteq mulSupport f union mulSupport g
参数：f g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
lemma mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g

@[to_additive]
/-
**Function.mulSupport_inf** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_inf [SemilatticeInf M] (f g : α -> M) : mulSupport (fun x => f 
x ⊓ g x) subseteq mulSupport f union mulSupport g
参数：f g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
lemma mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[to_additive]
/-
**Function.mulSupport_max** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_max [LinearOrder M] (f g : α -> M) : mulSupport (fun x => max (
f x) (g x)) subseteq mulSupport f union mulSupport g
参数：f g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_sup`：mulSupport_sup [SemilatticeSup M] (f g : α -> M
) : mulSupport (fun x => f x ⊔ g x) subseteq mulSupport f union mulSupport g
-/
lemma mulSupport_max [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_sup f g

@[to_additive]
/-
**Function.mulSupport_min** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_min [LinearOrder M] (f g : α -> M) : mulSupport (fun x => min (
f x) (g x)) subseteq mulSupport f union mulSupport g
参数：f g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_inf`：mulSupport_inf [SemilatticeInf M] (f g : α -> M
) : mulSupport (fun x => f x ⊓ g x) subseteq mulSupport f union mulSupport g
-/
lemma mulSupport_min [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := mulSupport_inf f g

@[to_additive]
/-
**Function.mulSupport_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α 
-> M) : mulSupport (fun x => ⨆ i, f i x) subseteq ⋃ i, mulSupport (f i)
参数：f : ι -> α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]
/-
**Function.mulSupport_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α 
-> M) : mulSupport (fun x => ⨅ i, f i x) subseteq ⋃ i, mulSupport (f i)
参数：f : ι -> α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_iSup`：mulSupport_iSup [ConditionallyCompleteLattice 
M] [Nonempty ι] (f : ι -> α -> M) : mulSupport (fun x => ⨆ i, f i x) subseteq ⋃ 
i, mulSupport …
-/
lemma mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) := mulSupport_iSup (M := Mᵒᵈ) f

end Function

namespace Set

section LE
variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive]
/-
**Set.mulIndicator_apply_le'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_le' (hfg : a in s -> f a <= y) (hg : a ∉ s -> 1 <= y) :
 mulIndicator s f a <= y
参数：hfg : a in s -> f a <= y；hg : a ∉ s -> 1 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]
/-
**Set.mulIndicator_le'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le' (hfg : forall a in s, f a <= g a) (hg : forall a, a ∉ s -
> 1 <= g a) : mulIndicator s f <= g
参数：hfg : forall a in s, f a <= g a；hg : forall a, a ∉ s -> 1 <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le'`：mulIndicator_apply_le' (hfg : a in s -> f a 
<= y) (hg : a ∉ s -> 1 <= y) : mulIndicator s f a <= y
-/
lemma mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a, a ∉ s → 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ ↦ mulIndicator_apply_le' (hfg _) (hg _)

@[to_additive]
/-
**Set.le_mulIndicator_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：le_mulIndicator_apply (hfg : a in s -> y <= g a) (hf : a ∉ s -> y <= 1) : 
y <= mulIndicator s g a
参数：hfg : a in s -> y <= g a；hf : a ∉ s -> y <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le'`：mulIndicator_apply_le' (hfg : a in s -> f a 
<= y) (hg : a ∉ s -> 1 <= y) : mulIndicator s f a <= y
-/
lemma le_mulIndicator_apply (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a := mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

@[to_additive]
/-
**Set.le_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：le_mulIndicator (hfg : forall a in s, f a <= g a) (hf : forall a ∉ s, f a 
<= 1) : f <= mulIndicator s g
参数：hfg : forall a in s, f a <= g a；hf : forall a ∉ s, f a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.le_mulIndicator_apply`：le_mulIndicator_apply (hfg : a in s -> y <= g
 a) (hf : a ∉ s -> y <= 1) : y <= mulIndicator s g a
-/
lemma le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ a ∉ s, f a ≤ 1) :
    f ≤ mulIndicator s g := fun _ ↦ le_mulIndicator_apply (hfg _) (hf _)

end LE

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive indicator_apply_nonneg]
/-
**Set.one_le_mulIndicator_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：one_le_mulIndicator_apply (h : a in s -> 1 <= f a) : 1 <= mulIndicator s f
 a
参数：h : a in s -> 1 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.le_mulIndicator_apply`：le_mulIndicator_apply (hfg : a in s -> y <= g
 a) (hf : a ∉ s -> y <= 1) : y <= mulIndicator s g a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ ↦ le_rfl

@[to_additive indicator_nonneg]
/-
**Set.one_le_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：one_le_mulIndicator (h : forall a in s, 1 <= f a) (a : α) : 1 <= mulIndica
tor s f a
参数：h : forall a in s, 1 <= f a；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.one_le_mulIndicator_apply`：one_le_mulIndicator_apply (h : a in s -> 
1 <= f a) : 1 <= mulIndicator s f a
-/
lemma one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)

@[to_additive]
/-
**Set.mulIndicator_apply_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_le_one (h : a in s -> f a <= 1) : mulIndicator s f a <=
 1
参数：h : a in s -> f a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le'`：mulIndicator_apply_le' (hfg : a in s -> f a 
<= y) (hg : a ∉ s -> 1 <= y) : mulIndicator s f a <= y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le' h fun _ ↦ le_rfl

@[to_additive]
/-
**Set.mulIndicator_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_one (h : forall a in s, f a <= 1) (a : α) : mulIndicator s
 f a <= 1
参数：h : forall a in s, f a <= 1；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le_one`：mulIndicator_apply_le_one (h : a in s -> 
f a <= 1) : mulIndicator s f a <= 1
-/
lemma mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le_one (h a)

@[to_additive]
/-
**Set.mulIndicator_le_mulIndicator'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_mulIndicator' (h : a in s -> f a <= g a) : mulIndicator s 
f a <= mulIndicator s g a
参数：h : a in s -> f a <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_rel_mulIndicator`：mulIndicator_rel_mulIndicator {r : M 
-> M -> Prop} (h1 : r 1 1) (ha : a in s -> r (f a) (g a)) : r (mulIndicator s f 
a) (mulIndicator s g a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mulIndicator_le_mulIndicator' (h : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl h

@[to_additive (attr := mono, gcongr only)]
/-
**Set.mulIndicator_le_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_mulIndicator (h : f a <= g a) : mulIndicator s f a <= mulI
ndicator s g a
参数：h : f a <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_rel_mulIndicator`：mulIndicator_rel_mulIndicator {r : M 
-> M -> Prop} (h1 : r 1 1) (ha : a in s -> r (f a) (g a)) : r (mulIndicator s f 
a) (mulIndicator s g a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ ↦ h

@[to_additive (attr := gcongr)]
/-
**Set.mulIndicator_mono** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_mono (h : f <= g) : s.mulIndicator f <= s.mulIndicator g
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_le_mulIndicator`：mulIndicator_le_mulIndicator (h : f a 
<= g a) : mulIndicator s f a <= mulIndicator s g a
-/
lemma mulIndicator_mono (h : f ≤ g) : s.mulIndicator f ≤ s.mulIndicator g :=
  fun _ ↦ mulIndicator_le_mulIndicator (h _)

@[to_additive (attr := gcongr)]
/-
**Set.mulIndicator_le_mulIndicator_apply_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Se
t`。
形式化陈述：mulIndicator_le_mulIndicator_apply_of_subset (h : s subseteq t) (hf : 1 <=
 f a) : mulIndicator s f a <= mulIndicator t f a
参数：h : s subseteq t；hf : 1 <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le'`：mulIndicator_apply_le' (hfg : a in s -> f a 
<= y) (hg : a ∉ s -> 1 <= y) : mulIndicator s f a <= y
· 使用引理 `Set.le_mulIndicator_apply`：le_mulIndicator_apply (hfg : a in s -> y <= g
 a) (hf : a ∉ s -> y <= 1) : y <= mulIndicator s g a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Set.one_le_mulIndicator_apply`：one_le_mulIndicator_apply (h : a in s -> 
1 <= f a) : 1 <= mulIndicator s f a
-/
lemma mulIndicator_le_mulIndicator_apply_of_subset (h : s ⊆ t) (hf : 1 ≤ f a) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha ↦ le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    one_le_mulIndicator_apply fun _ ↦ hf

@[to_additive (attr := gcongr)]
/-
**Set.mulIndicator_le_mulIndicator_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_mulIndicator_of_subset (h : s subseteq t) (hf : 1 <= f) : 
mulIndicator s f <= mulIndicator t f
参数：h : s subseteq t；hf : 1 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_le_mulIndicator_apply_of_subset`：mulIndicator_le_mulInd
icator_apply_of_subset (h : s subseteq t) (hf : 1 <= f a) : mulIndicator s f a <
= mulIndicator t f a
-/
lemma mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : 1 ≤ f) :
    mulIndicator s f ≤ mulIndicator t f :=
  fun _ ↦ mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

@[to_additive]
/-
**Set.mulIndicator_le_self'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_self' (hf : forall x ∉ s, 1 <= f x) : mulIndicator s f <= 
f
参数：hf : forall x ∉ s, 1 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_le'`：mulIndicator_le' (hfg : forall a in s, f a <= g a)
 (hg : forall a, a ∉ s -> 1 <= g a) : mulIndicator s f <= g
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mulIndicator_le_self' (hf : ∀ x ∉ s, 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ ↦ le_rfl) hf

end Preorder

section LinearOrder
variable [Zero M] [LinearOrder M]

/-
**Set.indicator_le_indicator_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_le_indicator_nonneg (s : Set α) (f : α -> M) : s.indicator f <= 
{a | 0 <= f a}.indicator f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma indicator_le_indicator_nonneg (s : Set α) (f : α → M) :
    s.indicator f ≤ {a | 0 ≤ f a}.indicator f := by
  intro a
  classical
  simp_rw [indicator_apply]
  split_ifs
  exacts [le_rfl, (not_le.1 ‹_›).le, ‹_›, le_rfl]
/-
**Set.indicator_nonpos_le_indicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_nonpos_le_indicator (s : Set α) (f : α -> M) : {a | f a <= 0}.in
dicator f <= s.indicator f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_le_indicator_nonneg`：indicator_le_indicator_nonneg (s : Se
t α) (f : α -> M) : s.indicator f <= {a | 0 <= f a}.indicator f
-/
lemma indicator_nonpos_le_indicator (s : Set α) (f : α → M) :
    {a | f a ≤ 0}.indicator f ≤ s.indicator f :=
  indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

end LinearOrder

section CompleteLattice
variable [CompleteLattice M] [One M]

@[to_additive]
/-
**Set.mulIndicator_iUnion_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M)
 (x : α) : mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x
参数：h1 : (⊥ : M) = 1；s : ι -> Set α；f : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `Set.mulIndicator_le_self'`：mulIndicator_le_self' (hf : forall x ∉ s, 1 <
= f x) : mulIndicator s f <= f
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i ↦ mulIndicator_le_self' (fun x _ ↦ h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]

variable [Nonempty ι]

@[to_additive]
/-
**Set.mulIndicator_iInter_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M)
 (x : α) : mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x
参数：h1 : (⊥ : M) = 1；s : ι -> Set α；f : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

@[to_additive]
/-
**Set.iSup_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f : ι -> α
 -> M} {s : ι -> Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
 ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i)
参数：h1 : (⊥ : M) = 1；hf : Monotone f；hs : Monotone s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Set.mulIndicator_mono`：mulIndicator_mono (h : f <= g) : s.mulIndicator f
 <= s.mulIndicator g
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用引理 `Set.mulIndicator_le_mulIndicator_of_subset`：mulIndicator_le_mulIndicator
_of_subset (h : s subseteq t) (hf : 1 <= f) : mulIndicator s f <= mulIndicator t
 f
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mulIndicator_of_mem`：mulIndicator_of_mem (h : a in s) (f : α -> M) :
 mulIndicator s f a = f a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Set.mulIndicator_of_notMem`：mulIndicator_of_notMem (h : a ∉ s) (f : α ->
 M) : mulIndicator s f a = 1
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f : ι → α → M}
    {s : ι → Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i ↦ ?_, fun a ↦ ?_⟩
  · grw [← le_iSup f i, ← subset_iUnion s i]
    intro; simp [← h1]
  by_cases ha : a ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ : ∃ i, a ∈ s i := by simpa using ha
    rw [mulIndicator_of_mem ha, iSup_apply, iSup_apply]
    refine iSup_le fun j ↦ ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine le_iSup_of_le k <| (hf hjk _).trans_eq ?_
    rw [mulIndicator_of_mem (hs hik hi)]
  · rw [mulIndicator_of_notMem ha, ← h1]
    exact bot_le

end CompleteLattice

section CanonicallyOrderedMul

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

@[to_additive]
/-
**Set.mulIndicator_le_self** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le_self (s : Set α) (f : α -> M) : mulIndicator s f <= f
参数：s : Set α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_le_self'`：mulIndicator_le_self' (hf : forall x ∉ s, 1 <
= f x) : mulIndicator s f <= f
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
lemma mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mulIndicator_le_self' fun _ _ ↦ one_le

@[to_additive]
/-
**Set.mulIndicator_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_apply_le {a : α} {s : Set α} {f g : α -> M} (hfg : a in s -> 
f a <= g a) : mulIndicator s f a <= g a
参数：hfg : a in s -> f a <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_apply_le'`：mulIndicator_apply_le' (hfg : a in s -> f a 
<= y) (hg : a ∉ s -> 1 <= y) : mulIndicator s f a <= y
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
lemma mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  mulIndicator_apply_le' hfg fun _ ↦ one_le

@[to_additive]
/-
**Set.mulIndicator_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mulIndicator_le {s : Set α} {f g : α -> M} (hfg : forall a in s, f a <= g 
a) : mulIndicator s f <= g
参数：hfg : forall a in s, f a <= g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mulIndicator_le'`：mulIndicator_le' (hfg : forall a in s, f a <= g a)
 (hg : forall a, a ∉ s -> 1 <= g a) : mulIndicator s f <= g
· 使用定理 `one_le`：one_le {a : α} : 1 <= a
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
lemma mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  mulIndicator_le' hfg fun _ _ ↦ one_le

end CanonicallyOrderedMul

section LatticeOrderedCommGroup
variable [CommGroup M] [Lattice M]

open scoped symmDiff

@[to_additive]
/-
**Set.mabs_mulIndicator_symmDiff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mabs_mulIndicator_symmDiff (s t : Set α) (f : α -> M) (x : α) : |mulIndica
tor (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ
参数：s t : Set α；f : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.apply_mulIndicator_symmDiff`：apply_mulIndicator_symmDiff {g : G -> β
} (hg : forall x, g x⁻¹ = g x) (s t : Set α) (f : α -> G) (x : α) : g (mulIndica
tor (s ∆ t) f x) = g …
· 使用定理 `mabs_inv`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] (a : α)
, |a⁻¹|ₘ = |a|ₘ
-/
lemma mabs_mulIndicator_symmDiff (s t : Set α) (f : α → M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ :=
  apply_mulIndicator_symmDiff mabs_inv s t f x

end LatticeOrderedCommGroup
end Set

