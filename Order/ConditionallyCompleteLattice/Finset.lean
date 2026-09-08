/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Conditionally complete lattices and finite sets.

-/

public section


open Set

variable {ι α β γ : Type*}

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/-
**Finset.Nonempty.csSup_eq_max'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.Nonempty.csSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = 
s.max' h
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `csSup_le_iff`：csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s 
<= a ↔ forall b in s, b <= a
· 使用定理 `Finset.bddAbove`：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (
s : Finset α), BddAbove ↑s
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.max'_le_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x
-/
theorem Finset.Nonempty.csSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun _ => (csSup_le_iff s.bddAbove h.to_set).trans (s.max'_le_iff h).symm
/-
**Finset.Nonempty.csInf_eq_min'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.Nonempty.csInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = 
s.min' h
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.csSup_eq_max'`：Finset.Nonempty.csSup_eq_max' {s : Finset
 α} (h : s.Nonempty) : sSup ↑s = s.max' h
-/
theorem Finset.Nonempty.csInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = s.min' h :=
  @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h
/-
**Finset.Nonempty.csSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.Nonempty.csSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set 
α) in s
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nonempty.csSup_eq_max'`：Finset.Nonempty.csSup_eq_max' {s : Finset
 α} (h : s.Nonempty) : sSup ↑s = s.max' h
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem Finset.Nonempty.csSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set α) ∈ s := by
  rw [h.csSup_eq_max']
  exact s.max'_mem _
/-
**Finset.Nonempty.csInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.Nonempty.csInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set 
α) in s
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.csSup_mem`：Finset.Nonempty.csSup_mem {s : Finset α} (h :
 s.Nonempty) : sSup (s : Set α) in s
-/
theorem Finset.Nonempty.csInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set α) ∈ s :=
  @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h
/-
**Set.Nonempty.csSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s in s
参数：h : s.Nonempty；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Finset.Nonempty.csSup_mem`：Finset.Nonempty.csSup_mem {s : Finset α} (h :
 s.Nonempty) : sSup (s : Set α) in s
-/
theorem Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s ∈ s := by
  lift s to Finset α using hs
  exact Finset.Nonempty.csSup_mem h
/-
**Set.Nonempty.csInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s in s
参数：h : s.Nonempty；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
-/
theorem Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s ∈ s :=
  @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs
/-
**Set.Finite.csSup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ fo
rall x in s, x < a
参数：hs : s.Finite；h : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
-/
theorem Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h _ hx => (le_csSup hs.bddAbove hx).trans_lt h, fun H => H _ <| h.csSup_mem hs⟩
/-
**Set.Finite.lt_csInf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.lt_csInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ fo
rall x in s, a < x
参数：hs : s.Finite；h : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.csSup_lt_iff`：Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.
Nonempty) : sSup s < a ↔ forall x in s, x < a
-/
theorem Set.Finite.lt_csInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α → β} (hmono : Monotone f)
include hmono

/-
**Set.Finite.map_sSup_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.map_sSup_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.F
inite) : f (sSup s) = sSup (f '' s)
参数：hne : s.Nonempty；hfin : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monotone.le_csSup_image`：le_csSup_image {s : Set α} {c : α} (hcs : c in 
s) (h_bdd : BddAbove s) : f c <= sSup (f '' s)
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Monotone.csSup_image_le_map_csSup`：csSup_image_le_map_csSup (hbdd : BddA
bove s
-/
theorem Set.Finite.map_sSup_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.Finite) :
    f (sSup s) = sSup (f '' s) :=
  le_antisymm (hmono.le_csSup_image (hne.csSup_mem hfin) hfin.bddAbove)
    (hmono.csSup_image_le_map_csSup hne hfin.bddAbove)
/-
**Set.Finite.map_sInf_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.map_sInf_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.F
inite) : f (sInf s) = sInf (f '' s)
参数：hne : s.Nonempty；hfin : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monotone.map_csInf_le_csInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst
 : ConditionallyCompleteLattice β] [inst_1 : ConditionallyCompleteLattice α]   {
f : α → β} {s : Set α},…
· 使用定理 `Set.Finite.bddBelow`：∀ {α : Type u} [inst : Preorder α] [IsCodirectedOrd
er α] [Nonempty α] {s : Set α}, s.Finite → BddBelow s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Monotone.csInf_image_le`：∀ {α : Type u_1} {β : Type u_2} [inst : Conditi
onallyCompleteLattice β] [inst_1 : Preorder α] {f : α → β},   Monotone f → ∀ {s 
: Set α} {c :…
· 使用定理 `Set.Nonempty.csInf_mem`：Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.
Finite) : sInf s in s
-/
theorem Set.Finite.map_sInf_of_monotone {s : Set α} (hne : s.Nonempty) (hfin : s.Finite) :
    f (sInf s) = sInf (f '' s) :=
  le_antisymm (hmono.map_csInf_le_csInf_image hne hfin.bddBelow)
    (hmono.csInf_image_le (hne.csInf_mem hfin) hfin.bddBelow)

end ConditionallyCompleteLattice

variable (f : ι → α)

/-
**Finset.ciSup_eq_max'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLinearOrder α
] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, sSup ∅ ≤ f x) →     ∀ (h' : autoParam 
(Finset.image f s).Nonempty Finset.ciSup_eq_max'_image._auto_1),       ⨆ i ∈ s, 
f i = (Finset.image f s).max' h'
参数：f : ι → α；∃ x ∈ s, sSup ∅ ≤ f x；h' : autoParam (Finset.image f s).Nonempty Fi
nset.ciSup_eq_max'_image._auto_1；Finset.image f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nonempty.csSup_eq_max'`：Finset.Nonempty.csSup_eq_max' {s : Finset
 α} (h : s.Nonempty) : sSup ↑s = s.max' h
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `csSup_eq_csSup_of_forall_exists_le`：csSup_eq_csSup_of_forall_exists_le {
s t : Set α} (hs : forall x in s, exists y in t, x <= y) (ht : forall y in t, ex
ists x in s, y <= x) : s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ciSup_eq_ite`：ciSup_eq_ite {p : Prop} [Decidable p] {f : p -> α} : (⨆ h 
: p, f h) = if h : p then f h else sSup (∅ : Set α)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem Finset.ciSup_eq_max'_image {s : Finset ι} (h : ∃ x ∈ s, sSup ∅ ≤ f x)
    (h' : (s.image f).Nonempty := by exact image_nonempty.mpr (h.imp fun _ ↦ And.left)) :
    ⨆ i ∈ s, f i = (s.image f).max' h' := by
  classical
  rw [iSup, ← h'.csSup_eq_max', coe_image]
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [ciSup_eq_ite, dite_eq_ite, Set.mem_range, Set.mem_image, mem_coe,
      exists_exists_and_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    split_ifs
    · exact ⟨_, by assumption, le_rfl⟩
    · assumption
  · simp only [Set.mem_image, mem_coe, ciSup_eq_ite, dite_eq_ite, Set.mem_range,
      exists_exists_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro i hi
    refine ⟨i, ?_⟩
    simp [hi]
/-
**Finset.ciInf_eq_min'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLinearOrder α
] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, f x ≤ sInf ∅) →     ∀ (h' : autoParam 
(Finset.image f s).Nonempty Finset.ciInf_eq_min'_image._auto_1),       ⨅ i ∈ s, 
f i = (Finset.image f s).min' h'
参数：f : ι → α；∃ x ∈ s, f x ≤ sInf ∅；h' : autoParam (Finset.image f s).Nonempty Fi
nset.ciInf_eq_min'_image._auto_1；Finset.image f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderDual.toDual_inj`：toDual_inj {a b : α} : toDual a = toDual b ↔ a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.toDual_min'`：toDual_min' {s : Finset α} (hs : s.Nonempty) : toDua
l (min' s hs) = max' (s.image toDual) (hs.image _)
· 使用定理 `toDual_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] (f : ι → 
α), OrderDual.toDual (⨅ i, f i) = ⨆ i, OrderDual.toDual (f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.ciSup_eq_max'_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLinearOrder α] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, sSup ∅ ≤
 f x) →     ∀ (h…
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Finset.max'.congr_simp`：∀ {α : Type u_2} [inst : LinearOrder α] (s s_1 :
 Finset α) (e_s : s = s_1) (H : s.Nonempty), s.max' H = s_1.max' ⋯
-/
theorem Finset.ciInf_eq_min'_image {s : Finset ι} (h : ∃ x ∈ s, f x ≤ sInf ∅)
    (h' : (s.image f).Nonempty := by exact image_nonempty.mpr (h.imp fun _ ↦ And.left)) :
    ⨅ i ∈ s, f i = (s.image f).min' h' := by
  rw [← OrderDual.toDual_inj, toDual_min', toDual_iInf]
  simp only [toDual_iInf]
  rw [ciSup_eq_max'_image _ h]
  simp only [image_image]
  congr
/-
**Finset.ciSup_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.ciSup_mem_image {s : Finset ι} (h : exists x in s, sSup ∅ <= f x) :
 ⨆ i in s, f i in s.image f
参数：h : exists x in s, sSup ∅ <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.ciSup_eq_max'_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLinearOrder α] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, sSup ∅ ≤
 f x) →     ∀ (h…
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
-/
theorem Finset.ciSup_mem_image {s : Finset ι} (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i ∈ s.image f := by
  rw [ciSup_eq_max'_image _ h]
  exact max'_mem (image f s) _
/-
**Finset.ciInf_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.ciInf_mem_image {s : Finset ι} (h : exists x in s, f x <= sInf ∅) :
 ⨅ i in s, f i in s.image f
参数：h : exists x in s, f x <= sInf ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.ciInf_eq_min'_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLinearOrder α] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, f x ≤ sI
nf ∅) →     ∀ (h…
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
-/
theorem Finset.ciInf_mem_image {s : Finset ι} (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ i ∈ s, f i ∈ s.image f := by
  rw [ciInf_eq_min'_image _ h]
  exact min'_mem (image f s) _
/-
**Set.Finite.ciSup_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.ciSup_mem_image {s : Set ι} (hs : s.Finite) (h : exists x in s,
 sSup ∅ <= f x) : ⨆ i in s, f i in f '' s
参数：hs : s.Finite；h : exists x in s, sSup ∅ <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciSup_mem_image`：Finset.ciSup_mem_image {s : Finset ι} (h : exist
s x in s, sSup ∅ <= f x) : ⨆ i in s, f i in s.image f
-/
theorem Set.Finite.ciSup_mem_image {s : Set ι} (hs : s.Finite) (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i ∈ f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciSup_mem_image f h
/-
**Set.Finite.ciInf_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.ciInf_mem_image {s : Set ι} (hs : s.Finite) (h : exists x in s,
 f x <= sInf ∅) : ⨅ i in s, f i in f '' s
参数：hs : s.Finite；h : exists x in s, f x <= sInf ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciInf_mem_image`：Finset.ciInf_mem_image {s : Finset ι} (h : exist
s x in s, f x <= sInf ∅) : ⨅ i in s, f i in s.image f
-/
theorem Set.Finite.ciInf_mem_image {s : Set ι} (hs : s.Finite) (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ i ∈ s, f i ∈ f '' s := by
  lift s to Finset ι using hs
  simp only [Finset.mem_coe] at h
  simpa using Finset.ciInf_mem_image f h
/-
**Set.Finite.ciSup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.ciSup_lt_iff {s : Set ι} {f : ι -> α} (hs : s.Finite) (h : exis
ts x in s, sSup ∅ <= f x) : ⨆ i in s, f i < a ↔ forall x in s, f x < a
参数：hs : s.Finite；h : exists x in s, sSup ∅ <= f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ciSup_eq_ite`：ciSup_eq_ite {p : Prop} [Decidable p] {f : p -> α} : (⨆ h 
: p, f h) = if h : p then f h else sSup (∅ : Set α)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.ciSup_mem_image`：Set.Finite.ciSup_mem_image {s : Set ι} (hs :
 s.Finite) (h : exists x in s, sSup ∅ <= f x) : ⨆ i in s, f i in f '' s
-/
theorem Set.Finite.ciSup_lt_iff {s : Set ι} {f : ι → α} (hs : s.Finite)
    (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ i ∈ s, f i < a ↔ ∀ x ∈ s, f x < a := by
  constructor
  · intro h x hx
    refine h.trans_le' (le_csSup ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sSup ∅))).subset ?_).bddAbove
      intro
      simp only [ciSup_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      grind
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · have := hs.ciSup_mem_image _ h
    grind
/-
**Set.Finite.lt_ciInf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.lt_ciInf_iff {s : Set ι} {f : ι -> α} (hs : s.Finite) (h : exis
ts x in s, f x <= sInf ∅) : a < ⨅ i in s, f i ↔ forall x in s, a < f x
参数：hs : s.Finite；h : exists x in s, f x <= sInf ∅。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `Set.Finite.bddBelow`：∀ {α : Type u} [inst : Preorder α] [IsCodirectedOrd
er α] [Nonempty α] {s : Set α}, s.Finite → BddBelow s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciInf_eq_ite`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrder
Inf α] {p : Prop} [inst_1 : Decidable p] {f : p → α},   ⨅ (h : p), f h = if h : 
p …
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ciInf_unique`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyCompl
etePartialOrderInf α] [inst_1 : Unique ι] {s : ι → α},   ⨅ i, s i = s default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.ciInf_mem_image`：Set.Finite.ciInf_mem_image {s : Set ι} (hs :
 s.Finite) (h : exists x in s, f x <= sInf ∅) : ⨅ i in s, f i in f '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Set.Finite.lt_ciInf_iff {s : Set ι} {f : ι → α} (hs : s.Finite)
    (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := by
  constructor
  · intro h x hx
    refine h.trans_le (csInf_le ?_ ?_)
    · classical
      refine (((hs.image f).union (finite_singleton (sInf ∅))).subset ?_).bddBelow
      intro
      simp only [ciInf_eq_ite, dite_eq_ite, mem_range, union_singleton, mem_insert_iff, mem_image,
        forall_exists_index]
      grind
    · simp only [mem_range]
      refine ⟨x, ?_⟩
      simp [hx]
  · intro H
    have := hs.ciInf_mem_image _ h
    simp only [mem_image] at this
    obtain ⟨_, hmem, hx⟩ := this
    rw [← hx]
    exact H _ hmem

section ListMultiset

/-
**List.iSup_mem_map_of_exists_sSup_empty_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：List.iSup_mem_map_of_exists_sSup_empty_le {l : List ι} (f : ι -> α) (h : e
xists x in l, sSup ∅ <= f x) : ⨆ x in l, f x in l.map f
参数：f : ι -> α；h : exists x in l, sSup ∅ <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciSup_mem_image`：Finset.ciSup_mem_image {s : Finset ι} (h : exist
s x in s, sSup ∅ <= f x) : ⨆ i in s, f i in s.image f
-/
lemma List.iSup_mem_map_of_exists_sSup_empty_le {l : List ι} (f : ι → α)
    (h : ∃ x ∈ l, sSup ∅ ≤ f x) :
    ⨆ x ∈ l, f x ∈ l.map f := by
  classical
  simpa using l.toFinset.ciSup_mem_image f (by simpa using h)
/-
**List.iInf_mem_map_of_exists_le_sInf_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：List.iInf_mem_map_of_exists_le_sInf_empty {l : List ι} (f : ι -> α) (h : e
xists x in l, f x <= sInf ∅) : ⨅ x in l, f x in l.map f
参数：f : ι -> α；h : exists x in l, f x <= sInf ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciInf_mem_image`：Finset.ciInf_mem_image {s : Finset ι} (h : exist
s x in s, f x <= sInf ∅) : ⨅ i in s, f i in s.image f
-/
lemma List.iInf_mem_map_of_exists_le_sInf_empty {l : List ι} (f : ι → α)
    (h : ∃ x ∈ l, f x ≤ sInf ∅) :
    ⨅ x ∈ l, f x ∈ l.map f := by
  classical
  simpa using l.toFinset.ciInf_mem_image f (by simpa using h)
/-
**Multiset.iSup_mem_map_of_exists_sSup_empty_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.iSup_mem_map_of_exists_sSup_empty_le {s : Multiset ι} (f : ι -> α
) (h : exists x in s, sSup ∅ <= f x) : ⨆ x in s, f x in s.map f
参数：f : ι -> α；h : exists x in s, sSup ∅ <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciSup_mem_image`：Finset.ciSup_mem_image {s : Finset ι} (h : exist
s x in s, sSup ∅ <= f x) : ⨆ i in s, f i in s.image f
-/
lemma Multiset.iSup_mem_map_of_exists_sSup_empty_le {s : Multiset ι} (f : ι → α)
    (h : ∃ x ∈ s, sSup ∅ ≤ f x) :
    ⨆ x ∈ s, f x ∈ s.map f := by
  classical
  simpa using s.toFinset.ciSup_mem_image f (by simpa using h)
/-
**Multiset.iInf_mem_map_of_exists_le_sInf_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.iInf_mem_map_of_exists_le_sInf_empty {s : Multiset ι} (f : ι -> α
) (h : exists x in s, f x <= sInf ∅) : ⨅ x in s, f x in s.map f
参数：f : ι -> α；h : exists x in s, f x <= sInf ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.ciInf_mem_image`：Finset.ciInf_mem_image {s : Finset ι} (h : exist
s x in s, f x <= sInf ∅) : ⨅ i in s, f i in s.image f
-/
lemma Multiset.iInf_mem_map_of_exists_le_sInf_empty {s : Multiset ι} (f : ι → α)
    (h : ∃ x ∈ s, f x ≤ sInf ∅) :
    ⨅ x ∈ s, f x ∈ s.map f := by
  classical
  simpa using s.toFinset.ciInf_mem_image f (by simpa using h)
/-
**exists_eq_ciSup_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_ciSup_of_finite [Nonempty ι] [Finite ι] {f : ι -> α} : exists i,
 f i = ⨆ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
theorem exists_eq_ciSup_of_finite [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨆ i, f i :=
  Nonempty.csSup_mem (range_nonempty f) (finite_range f)
/-
**exists_eq_ciInf_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_ciInf_of_finite [Nonempty ι] [Finite ι] {f : ι -> α} : exists i,
 f i = ⨅ i, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.csInf_mem`：Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.
Finite) : sInf s in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
theorem exists_eq_ciInf_of_finite [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨅ i, f i :=
  Nonempty.csInf_mem (range_nonempty f) (finite_range f)

end ListMultiset

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable {α : Type*} [CompleteLinearOrder α] {ι : Sort*}

/-
**sSup_ne_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊥) (hm
em : a ∉ s) : sSup s != a
参数：hfin : s.Finite；hne : a != ⊥；hmem : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
-/
theorem sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a ≠ ⊥) (hmem : a ∉ s) :
    sSup s ≠ a := by
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp [eq_comm, hne]
  exact (hmem <| · ▸ hnonempty.csSup_mem hfin)
/-
**sInf_ne_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a != ⊤) (hm
em : a ∉ s) : sInf s != a
参数：hfin : s.Finite；hne : a != ⊤；hmem : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_ne_of_notMem`：sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : 
α} (hne : a != ⊥) (hmem : a ∉ s) : sSup s != a
-/
theorem sInf_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : α} (hne : a ≠ ⊤) (hmem : a ∉ s) :
    sInf s ≠ a :=
  sSup_ne_of_notMem (α := αᵒᵈ) hfin hne hmem
/-
**sSup_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_ne_top [Nontrivial α] {s : Set α} (hfin : s.Finite) (htop : ⊤ ∉ s) : 
sSup s != ⊤
参数：hfin : s.Finite；htop : ⊤ ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_ne_of_notMem`：sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : 
α} (hne : a != ⊥) (hmem : a ∉ s) : sSup s != a
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
-/
theorem sSup_ne_top [Nontrivial α] {s : Set α} (hfin : s.Finite) (htop : ⊤ ∉ s) : sSup s ≠ ⊤ :=
  sSup_ne_of_notMem hfin top_ne_bot htop
/-
**sInf_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_ne_bot [Nontrivial α] {s : Set α} (hfin : s.Finite) (hbot : ⊥ ∉ s) : 
sInf s != ⊥
参数：hfin : s.Finite；hbot : ⊥ ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_ne_top`：sSup_ne_top [Nontrivial α] {s : Set α} (hfin : s.Finite) (h
top : ⊤ ∉ s) : sSup s != ⊤
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ
-/
theorem sInf_ne_bot [Nontrivial α] {s : Set α} (hfin : s.Finite) (hbot : ⊥ ∉ s) : sInf s ≠ ⊥ :=
  sSup_ne_top (α := αᵒᵈ) hfin hbot
/-
**iSup_ne_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊥) (h : fora
ll x, f x != a) : iSup f != a
参数：hne : a != ⊥；h : forall x, f x != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_ne_of_notMem`：sSup_ne_of_notMem {s : Set α} (hfin : s.Finite) {a : 
α} (hne : a != ⊥) (hmem : a ∉ s) : sSup s != a
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
theorem iSup_ne_of_notMem [Finite ι] {f : ι → α} {a : α} (hne : a ≠ ⊥) (h : ∀ x, f x ≠ a) :
    iSup f ≠ a :=
  sSup_ne_of_notMem (Set.finite_range f) hne <| by grind
/-
**iInf_ne_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hne : a != ⊤) (h : fora
ll x, f x != a) : iInf f != a
参数：hne : a != ⊤；h : forall x, f x != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_ne_of_notMem`：iSup_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hn
e : a != ⊥) (h : forall x, f x != a) : iSup f != a
-/
theorem iInf_ne_of_notMem [Finite ι] {f : ι → α} {a : α} (hne : a ≠ ⊤) (h : ∀ x, f x ≠ a) :
    iInf f ≠ a :=
  iSup_ne_of_notMem (α := αᵒᵈ) hne h
/-
**iSup_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_ne_top [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊤
) : iSup f != ⊤
参数：h : forall x, f x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_ne_of_notMem`：iSup_ne_of_notMem [Finite ι] {f : ι -> α} {a : α} (hn
e : a != ⊥) (h : forall x, f x != a) : iSup f != a
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
-/
theorem iSup_ne_top [Finite ι] [Nontrivial α] {f : ι → α} (h : ∀ x, f x ≠ ⊤) : iSup f ≠ ⊤ :=
  iSup_ne_of_notMem top_ne_bot h
/-
**iInf_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInf_ne_bot [Finite ι] [Nontrivial α] {f : ι -> α} (h : forall x, f x != ⊥
) : iInf f != ⊥
参数：h : forall x, f x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_ne_top`：iSup_ne_top [Finite ι] [Nontrivial α] {f : ι -> α} (h : for
all x, f x != ⊤) : iSup f != ⊤
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ
-/
theorem iInf_ne_bot [Finite ι] [Nontrivial α] {f : ι → α} (h : ∀ x, f x ≠ ⊥) : iInf f ≠ ⊥ :=
  iSup_ne_top (α := αᵒᵈ) h

end CompleteLinearOrder

/-!
### Relation between `sSup` / `sInf` and `Finset.sup'` / `Finset.inf'`

Like the `Sup` of a `ConditionallyCompleteLattice`, `Finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/

namespace Finset

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α]

/-
**Finset.sup'_eq_csSup_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLattice α] (s
 : Finset ι) (H : s.Nonempty) (f : ι → α),   s.sup' H f = sSup (f '' ↑s)
参数：s : Finset ι；H : s.Nonempty；f : ι → α；f '' ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_le_iff`：csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s 
<= a ↔ forall b in s, b <= a
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup'_eq_csSup_image (s : Finset ι) (H : s.Nonempty) (f : ι → α) :
    s.sup' H f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_toSet.image f).bddAbove (H.to_set.image f)]
/-
**Finset.inf'_eq_csInf_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLattice α] (s
 : Finset ι) (H : s.Nonempty) (f : ι → α),   s.inf' H f = sInf (f '' ↑s)
参数：s : Finset ι；H : s.Nonempty；f : ι → α；f '' ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_eq_csSup_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.sup
' H f = sSup (f …
-/
theorem inf'_eq_csInf_image (s : Finset ι) (H : s.Nonempty) (f : ι → α) :
    s.inf' H f = sInf (f '' s) :=
  sup'_eq_csSup_image (α := αᵒᵈ) _ H _
/-
**Finset.sup'_id_eq_csSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : ConditionallyCompleteLattice α] (s : Finset α) (h
s : s.Nonempty), s.sup' hs id = sSup ↑s
参数：s : Finset α；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_csSup_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.sup
' H f = sSup (f …
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem sup'_id_eq_csSup (s : Finset α) (hs) : s.sup' hs id = sSup s := by
  rw [sup'_eq_csSup_image s hs, Set.image_id]
/-
**Finset.inf'_id_eq_csInf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : ConditionallyCompleteLattice α] (s : Finset α) (h
s : s.Nonempty), s.inf' hs id = sInf ↑s
参数：s : Finset α；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_id_eq_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteL
attice α] (s : Finset α) (hs : s.Nonempty), s.sup' hs id = sSup ↑s
-/
theorem inf'_id_eq_csInf (s : Finset α) (hs) : s.inf' hs id = sInf s :=
  sup'_id_eq_csSup (α := αᵒᵈ) _ hs

variable [Fintype ι] [Nonempty ι]
/-
**Finset.sup'_univ_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLattice α] [i
nst_1 : Fintype ι] [inst_2 : Nonempty ι]   (f : ι → α), Finset.univ.sup' ⋯ f = ⨆
 i, f i
参数：f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_csSup_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.sup
' H f = sSup (f …
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sup'_univ_eq_ciSup (f : ι → α) : univ.sup' univ_nonempty f = ⨆ i, f i := by
  simp [sup'_eq_csSup_image, iSup]

@[to_dual existing]
/-
**Finset.inf'_univ_eq_ciInf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLattice α] [i
nst_1 : Fintype ι] [inst_2 : Nonempty ι]   (f : ι → α), Finset.univ.inf' ⋯ f = ⨅
 i, f i
参数：f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf'_eq_csInf_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.inf
' H f = sInf (f …
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inf'_univ_eq_ciInf (f : ι → α) : univ.inf' univ_nonempty f = ⨅ i, f i := by
  simp [inf'_eq_csInf_image, iInf]

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α]

/-
**Finset.sup_univ_eq_ciSup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_univ_eq_ciSup [Fintype ι] (f : ι -> α) : univ.sup f = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma sup_univ_eq_ciSup [Fintype ι] (f : ι → α) : univ.sup f = ⨆ i, f i :=
  le_antisymm
    (Finset.sup_le fun _ _ => le_ciSup (finite_range _).bddAbove _)
    (ciSup_le' fun _ => Finset.le_sup (mem_univ _))
/-
**Finset.ciSup_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ciSup_union [DecidableEq ι] {f : ι -> α} {s t : Finset ι} : (⨆ x in s unio
n t, f x) = (⨆ x in s, f x) ⊔ (⨆ x in t, f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ciSup_or'`：ciSup_or' (p q : Prop) (f : p ∨ q -> α) : ⨆ (h : p ∨ q), f h 
= (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h)
· 使用定理 `ciSup_sup_eq`：ciSup_sup_eq {f g : ι -> α} (Hf : BddAbove <| range f) (Hg
 : BddAbove <| range g) : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ciSup_union [DecidableEq ι] {f : ι → α} {s t : Finset ι} :
    (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ (⨆ x ∈ t, f x) := by
  suffices ∀ st : Finset ι, BddAbove <| .range fun x ↦ ⨆ (_ : x ∈ st), f x by
    simp [ciSup_or', ciSup_sup_eq, this]
  refine fun st ↦ ⟨st.sup f, fun a ⟨i, ha⟩ ↦ ha ▸ ?_⟩
  by_cases h : i ∈ st <;>
    simp [h, le_sup]

end ConditionallyCompleteLinearOrderBot

end Finset

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] (f : ι → α)

/-
**Finset.Nonempty.ciSup_eq_max'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty
`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : ConditionallyCompleteLinearOrderBo
t α] (f : ι → α) {s : Finset ι}   (h : s.Nonempty) (h' : optParam (Finset.image 
f s).Nonempty ⋯), ⨆ i ∈ s, f i = (Finset.image f s).max' h'
参数：f : ι → α；h : s.Nonempty；h' : optParam (Finset.image f s).Nonempty ⋯；Finset.i
mage f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ciSup_eq_max'_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLinearOrder α] (f : ι → α) {s : Finset ι},   (∃ x ∈ s, sSup ∅ ≤
 f x) →     ∀ (h…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finset.Nonempty.ciSup_eq_max'_image {s : Finset ι} (h : s.Nonempty)
    (h' : (s.image f).Nonempty := h.image f) :
    ⨆ i ∈ s, f i = (s.image f).max' h' :=
  s.ciSup_eq_max'_image _ (h.imp (by simp)) _
/-
**Finset.Nonempty.ciSup_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.Nonempty.ciSup_mem_image {s : Finset ι} (h : s.Nonempty) : ⨆ i in s
, f i in s.image f
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ciSup_mem_image`：Finset.ciSup_mem_image {s : Finset ι} (h : exist
s x in s, sSup ∅ <= f x) : ⨆ i in s, f i in s.image f
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finset.Nonempty.ciSup_mem_image {s : Finset ι} (h : s.Nonempty) :
    ⨆ i ∈ s, f i ∈ s.image f :=
  s.ciSup_mem_image _ (h.imp (by simp))
/-
**Set.Nonempty.ciSup_mem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Nonempty.ciSup_mem_image {s : Set ι} (h : s.Nonempty) (hs : s.Finite) 
: ⨆ i in s, f i in f '' s
参数：h : s.Nonempty；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.ciSup_mem_image`：Set.Finite.ciSup_mem_image {s : Set ι} (hs :
 s.Finite) (h : exists x in s, sSup ∅ <= f x) : ⨆ i in s, f i in f '' s
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Set.Nonempty.ciSup_mem_image {s : Set ι} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i ∈ s, f i ∈ f '' s :=
  hs.ciSup_mem_image _ (h.imp (by simp))
/-
**Set.Nonempty.ciSup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Nonempty.ciSup_lt_iff {s : Set ι} {a : α} {f : ι -> α} (h : s.Nonempty
) (hs : s.Finite) : ⨆ i in s, f i < a ↔ forall x in s, f x < a
参数：h : s.Nonempty；hs : s.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.ciSup_lt_iff`：Set.Finite.ciSup_lt_iff {s : Set ι} {f : ι -> α
} (hs : s.Finite) (h : exists x in s, sSup ∅ <= f x) : ⨆ i in s, f i < a ↔ foral
l x in s, f x…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Set.Nonempty.ciSup_lt_iff {s : Set ι} {a : α} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) :
    ⨆ i ∈ s, f i < a ↔ ∀ x ∈ s, f x < a :=
  hs.ciSup_lt_iff (h.imp (by simp))

section ListMultiset

/-
**List.iSup_mem_map_of_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：List.iSup_mem_map_of_ne_nil {l : List ι} (f : ι -> α) (h : l != []) : ⨆ x 
in l, f x in l.map f
参数：f : ι -> α；h : l != []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.iSup_mem_map_of_exists_sSup_empty_le`：List.iSup_mem_map_of_exists_s
Sup_empty_le {l : List ι} (f : ι -> α) (h : exists x in l, sSup ∅ <= f x) : ⨆ x 
in l, f x in l.map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `List.exists_mem_of_ne_nil`：∀ {α : Type u_1} (l : List α), l ≠ [] → ∃ x, 
x ∈ l
-/
lemma List.iSup_mem_map_of_ne_nil {l : List ι} (f : ι → α) (h : l ≠ []) :
    ⨆ x ∈ l, f x ∈ l.map f :=
  l.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_nil _ h)
/-
**Multiset.iSup_mem_map_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.iSup_mem_map_of_ne_zero {s : Multiset ι} (f : ι -> α) (h : s != 0
) : ⨆ x in s, f x in s.map f
参数：f : ι -> α；h : s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.iSup_mem_map_of_exists_sSup_empty_le`：Multiset.iSup_mem_map_of_
exists_sSup_empty_le {s : Multiset ι} (f : ι -> α) (h : exists x in s, sSup ∅ <=
 f x) : ⨆ x in s, f x in s.map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
-/
lemma Multiset.iSup_mem_map_of_ne_zero {s : Multiset ι} (f : ι → α) (h : s ≠ 0) :
    ⨆ x ∈ s, f x ∈ s.map f :=
  s.iSup_mem_map_of_exists_sSup_empty_le _ (by simpa using exists_mem_of_ne_zero h)

end ListMultiset

end ConditionallyCompleteLinearOrderBot

