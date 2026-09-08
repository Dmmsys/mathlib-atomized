/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Violeta Hernández Palacios
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.SuccPred.Limit

/-!
# Order topologies of successor or predecessor orders

This file proves miscellaneous results under the assumption of `OrderTopology` plus either of
`SuccOrder` or `PredOrder`.
-/

public section

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {a : α} {s : Set α}

open Filter Order Set Topology

namespace SuccOrder
variable [SuccOrder α]

@[to_dual]
/-
**SuccOrder.isOpen_singleton_of_not_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `Su
ccOrder`。
形式化陈述：isOpen_singleton_of_not_isSuccPrelimit (ha : ¬ IsSuccPrelimit a) : IsOpen 
{a}
参数：ha : ¬ IsSuccPrelimit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.not_isSuccPrelimit_iff`：not_isSuccPrelimit_iff {a : α} : ¬IsSuccPr
elimit a ↔ exists b, b ⋖ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CovBy.Ioi_eq`：CovBy.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CovBy.Ioo_eq_Ioc`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ⋖
 a → ∀ (c : α), Set.Ioo c a = Set.Ioc c b
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
· 使用定理 `CovBy.Ioc_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ⋖ a 
→ Set.Ioc b a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
-/
theorem isOpen_singleton_of_not_isSuccPrelimit (ha : ¬ IsSuccPrelimit a) : IsOpen {a} := by
  obtain ⟨b, hb⟩ := not_isSuccPrelimit_iff.1 ha
  by_cases ha' : IsMax a
  · convert! isOpen_Ioi (a := b) using 1
    rw [hb.Ioi_eq]
    grind [IsMax]
  · convert! isOpen_Ioo (a := b) (b := Order.succ a) using 1
    simp [(covBy_succ_of_not_isMax ha').Ioo_eq_Ioc, hb.Ioc_eq]

variable [NoMaxOrder α]

@[to_dual]
/-
**SuccOrder.isOpen_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：isOpen_singleton_iff : IsOpen {a} ↔ ¬ IsSuccLimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `WellFoundedGT.toIsSuccArchimedean`：∀ {α : Type u_1} [inst : PartialOrder
 α] [h : WellFoundedGT α] [inst_1 : SuccOrder α], IsSuccArchimedean α
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff_exists_Ioo_subset'`：mem_nhds_iff_exists_Ioo_subset' {a : α}
 {s : Set α} (hl : exists l, l < a) (hu : exists u, a < u) : s in 𝓝 a ↔ exists l
 u, a in Ioo l u ∧ Io…
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_iff_covBy`：succ_eq_iff_covBy : succ a = b ↔ a ⋖ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder 
α] {a b : α}, a < b → Order.succ a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 39 条，此处仅展示前 30 条）
-/
theorem isOpen_singleton_iff : IsOpen {a} ↔ ¬ IsSuccLimit a := by
  nontriviality α
  refine ⟨fun h ha ↦ ?_, fun ha ↦ ?_⟩
  · obtain ⟨l, u, h₁, h₂⟩ := mem_nhds_iff_exists_Ioo_subset' (by simpa using ha.not_isMin)
      (by simpa only [not_isMax_iff] using not_isMax a) |>.mp (h.mem_nhds (mem_singleton a))
    refine ha.isSuccPrelimit l ?_
    rw [← succ_eq_iff_covBy]
    simp only [mem_Ioo, subset_singleton_iff] at h₁ h₂
    exact h₂ _ ⟨lt_succ l, h₁.1.succ_le.trans_lt h₁.2⟩
  · obtain (ha | ha) := not_isSuccLimit_iff.mp ha
    · convert! isOpen_Iio (a := Order.succ a) using 1
      simp [ha.Iic_eq]
    · exact isOpen_singleton_of_not_isSuccPrelimit ha

@[to_dual]
/-
**SuccOrder.nhds_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `SuccOrder.isOpen_singleton_iff`：isOpen_singleton_iff : IsOpen {a} ↔ ¬ Is
SuccLimit a
-/
theorem nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

@[to_dual]
/-
**SuccOrder.nhds_of_isMin** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pure a
参数：h : IsMin a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.nhds_eq_pure`：nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLi
mit a
· 使用定理 `Order.isSuccLimit_iff`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Ord
er.IsSuccLimit a ↔ ¬IsMin a ∧ Order.IsSuccPrelimit a
-/
theorem nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pure a := by
  rw [nhds_eq_pure, isSuccLimit_iff]
  tauto

@[to_dual (attr := simp)]
/-
**SuccOrder.nhds_bot** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：nhds_bot [OrderBot α] : 𝓝 (⊥ : α) = pure ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.nhds_of_isMin`：nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pur
e a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem nhds_bot [OrderBot α] : 𝓝 (⊥ : α) = pure ⊥ :=
  nhds_of_isMin isMin_bot

@[to_dual]
/-
**SuccOrder.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：isOpen_iff {s : Set α} : IsOpen s ↔ forall o in s, IsSuccLimit o -> exists
 a < o, Ioo a o subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `SuccOrder.hasBasis_nhds_Ioc_of_exists_lt`：SuccOrder.hasBasis_nhds_Ioc_of
_exists_lt [SuccOrder α] {a : α} (ha : exists l, l < a) : (𝓝 a).HasBasis (· < a)
 (Set.Ioc · a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SuccOrder.nhds_eq_pure`：nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLi
mit a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff {s : Set α} : IsOpen s ↔
    ∀ o ∈ s, IsSuccLimit o → ∃ a < o, Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho ↦ ?_
  by_cases ho' : IsSuccLimit o
  · rw [(hasBasis_nhds_Ioc_of_exists_lt (not_isMin_iff.1 ho'.not_isMin)).mem_iff]
    grind
  · simp [nhds_eq_pure.2 ho', ho, ho']

@[to_dual]
/-
**SuccOrder.accPt_principal** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：accPt_principal {a : α} {s : Set α} : AccPt a (𝓟 s) ↔ ¬ IsMin a ∧ forall b
 < a, (s inter Ioo b a).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_frequently`：accPt_iff_frequently {x : X} {C : Set X} : AccPt x
 (𝓟 C) ↔ existsᶠ y in 𝓝 x, y != x ∧ y in C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SuccOrder.nhds_of_isMin`：nhds_of_isMin {a : α} (h : IsMin a) : 𝓝 a = pur
e a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `SuccOrder.hasBasis_nhds_Ioc_of_exists_lt`：SuccOrder.hasBasis_nhds_Ioc_of
_exists_lt [SuccOrder α] {a : α} (ha : exists l, l < a) : (𝓝 a).HasBasis (· < a)
 (Set.Ioc · a)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem accPt_principal {a : α} {s : Set α} :
    AccPt a (𝓟 s) ↔ ¬ IsMin a ∧ ∀ b < a, (s ∩ Ioo b a).Nonempty := by
  rw [accPt_iff_frequently]
  by_cases ha : IsMin a
  · simp [nhds_of_isMin, ha]
  · rw [not_isMin_iff] at ha ⊢
    simp_rw [(hasBasis_nhds_Ioc_of_exists_lt ha).frequently_iff, Set.Nonempty, mem_inter_iff]
    grind

@[to_dual]
/-
**SuccOrder._root_.AccPt.not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AccPt.not_isMin {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : ¬ IsMin a :=
  (accPt_principal.1 h).1

@[to_dual]
/-
**SuccOrder._root_.AccPt.isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AccPt.isSuccLimit {a : α} {s : Set α} (h : AccPt a (𝓟 s)) : IsSuccLimit a := by
  rw [isSuccLimit_iff, IsSuccPrelimit]
  simp_rw [accPt_principal, Set.Nonempty] at h
  grind [covBy_iff_Ioo_eq]

@[to_dual]
/-
**SuccOrder.isSuccLimit_of_mem_frontier** 是 Mathlib 中的一个定理，位于命名空间 `SuccOrder`。
形式化陈述：isSuccLimit_of_mem_frontier {a : α} {s : Set α} (ha : a in frontier s) : I
sSuccLimit a
参数：ha : a in frontier s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `SuccOrder.isOpen_singleton_iff`：isOpen_singleton_iff : IsOpen {a} ↔ ¬ Is
SuccLimit a
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
-/
theorem isSuccLimit_of_mem_frontier {a : α} {s : Set α} (ha : a ∈ frontier s) : IsSuccLimit a := by
  rw [← isOpen_singleton_iff.not_left]
  rw [frontier_eq_closure_inter_closure] at ha
  grind [mem_closure_iff, Set.Nonempty]

end SuccOrder

