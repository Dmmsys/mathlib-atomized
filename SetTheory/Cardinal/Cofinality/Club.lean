/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Enum

/-!
# Club sets and stationary sets

A subset of a well-ordered type `α` is called a **club set** when it is closed in the order topology
and cofinal. If `α` has no maximum, then an equivalent condition is that `α` is closed and
unbounded; hence the name.

A **stationary set** is a set which intersects all club sets.

## Implementation notes

To avoid importing topology in the ordinals, we spell out the closure property using `DirSupClosed`.
For any type equipped with the Scott-Hausdorff topology (which includes well-orders with the order
topology), `DirSupClosed s` and `IsClosed s` are equivalent predicates.
-/

public section

universe u v

open Cardinal Order Set

variable {α : Type v} {s t : Set α} {x : α} [LinearOrder α]

/-- A club set is a set that is closed under suprema and that is cofinal. -/
@[mk_iff]
/-
**IsClub** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [LinearOrder α] → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A club set is a set that is closed under suprema and that is cofinal.
-/
structure IsClub {α : Type*} [LinearOrder α] (s : Set α) where
  /-- Club sets are closed under suprema. If `α` is a well-order with the order topology, this
  condition is equivalent to `IsClosed s`. -/
  dirSupClosed : DirSupClosed s
  /-- Club sets are cofinal. If `α` has no maximum, this condition is equivalent to `¬ BddAbove s`.
  See `not_bddAbove_iff_isCofinal`. -/
  isCofinal : IsCofinal s

namespace IsClub

@[simp]
/-
**IsClub.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：of_isEmpty [IsEmpty α] {s : Set α} : IsClub s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.of_isEmpty`：∀ {α : Type u_1} [inst : Preorder α] [IsEmpty α
] {s : Set α}, DirSupClosed s
· 使用定理 `IsCofinal.of_isEmpty`：IsCofinal.of_isEmpty [IsEmpty α] {s : Set α} : IsC
ofinal s
-/
theorem of_isEmpty [IsEmpty α] {s : Set α} : IsClub s :=
  ⟨.of_isEmpty, .of_isEmpty⟩

@[simp]
/-
**IsClub.univ** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} [inst : LinearOrder α], IsClub Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.univ`：∀ {α : Type u_1} [inst : Preorder α], DirSupClosed Se
t.univ
· 使用定理 `IsCofinal.univ`：IsCofinal.univ : IsCofinal (@univ α)
-/
protected theorem univ : IsClub (α := α) .univ :=
  ⟨.univ, .univ⟩
/-
**IsClub.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} {s : Set α} [inst : LinearOrder α] [Nonempty α], IsClub s →
 s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinal.nonempty`：IsCofinal.nonempty [Nonempty α] {s : Set α} (hs : Is
Cofinal s) : s.Nonempty
· 使用定理 `IsClub.isCofinal`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}, I
sClub s → IsCofinal s
-/
protected theorem nonempty [Nonempty α] (hs : IsClub s) : s.Nonempty :=
  hs.isCofinal.nonempty
/-
**IsClub._root_.isClub_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isClub_empty_iff : IsClub (α := α) ∅ ↔ IsEmpty α :=
  ⟨fun h ↦ isCofinal_empty_iff.1 h.isCofinal, fun _ ↦ .of_isEmpty⟩
/-
**IsClub.union** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} {s t : Set α} [inst : LinearOrder α], IsClub s → IsClub t →
 IsClub (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.union`：DirSupClosed.union (hs : DirSupClosed s) (ht : DirSu
pClosed t) : DirSupClosed (s union t)
· 使用定理 `IsClub.dirSupClosed`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}
, IsClub s → DirSupClosed s
· 使用定理 `IsCofinal.mono`：IsCofinal.mono {s t : Set α} (h : s subseteq t) (hs : Is
Cofinal s) : IsCofinal t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `IsClub.isCofinal`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}, I
sClub s → IsCofinal s
-/
protected theorem union (hs : IsClub s) (ht : IsClub t) : IsClub (s ∪ t) :=
  ⟨hs.dirSupClosed.union ht.dirSupClosed, hs.isCofinal.mono Set.subset_union_left⟩
/-
**IsClub.isLUB_mem** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：isLUB_mem (hs : IsClub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (hx : IsL
UB t x) : x in s
参数：hs : IsClub s；ht : t subseteq s；ht₀ : t.Nonempty；hx : IsLUB t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClub.dirSupClosed`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}
, IsClub s → DirSupClosed s
· 使用定理 `DirectedOn.of_linearOrder`：DirectedOn.of_linearOrder [LinearOrder α] (s 
: Set α) : DirectedOn (· <= ·) s
-/
theorem isLUB_mem (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (hx : IsLUB t x) : x ∈ s :=
  hs.dirSupClosed ht ht₀ (.of_linearOrder _) hx
/-
**IsClub.csSup_mem** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α} (hs : IsC
lub s) (ht : t subseteq s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t in s
参数：hs : IsClub s；ht : t subseteq s；ht₀ : t.Nonempty；ht₁ : BddAbove t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClub.isLUB_mem`：isLUB_mem (hs : IsClub s) (ht : t subseteq s) (ht₀ : t
.Nonempty) (hx : IsLUB t x) : x in s
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem csSup_mem {α} [ConditionallyCompleteLinearOrder α] {s t : Set α}
    (hs : IsClub s) (ht : t ⊆ s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup t ∈ s :=
  hs.isLUB_mem ht ht₀ (isLUB_csSup ht₀ ht₁)
/-
**IsClub.sInter_of_orderTop** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：sInter_of_orderTop {s : Set (Set α)} [OrderTop α] (hs : forall x in s, IsC
lub x) : IsClub (⋂₀ s)
参数：Set α；hs : forall x in s, IsClub x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosed.sInter`：DirSupClosed.sInter {s : Set (Set α)} (hs : forall 
x in s, DirSupClosed x) : DirSupClosed (⋂₀ s)
· 使用定理 `IsClub.dirSupClosed`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}
, IsClub s → DirSupClosed s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCofinal_iff_top_mem`：isCofinal_iff_top_mem [OrderTop α] {s : Set α} : 
IsCofinal s ↔ ⊤ in s
· 使用定理 `Set.mem_sInter`：mem_sInter {x : α} {S : Set (Set α)} : x in ⋂₀ S ↔ foral
l t in S, x in t
· 使用定理 `IsCofinal.top_mem`：IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCo
final s) : ⊤ in s
· 使用定理 `IsClub.isCofinal`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}, I
sClub s → IsCofinal s
-/
theorem sInter_of_orderTop {s : Set (Set α)} [OrderTop α] (hs : ∀ x ∈ s, IsClub x) :
    IsClub (⋂₀ s) := by
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, ?_⟩
  rw [isCofinal_iff_top_mem, mem_sInter]
  exact fun x hx ↦ (hs x hx).isCofinal.top_mem
/-
**IsClub.iInter_of_orderTop** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：iInter_of_orderTop {ι : Type*} {f : ι -> Set α} [OrderTop α] (hs : forall 
i, IsClub (f i)) : IsClub (⋂ i, f i)
参数：hs : forall i, IsClub (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `IsClub.sInter_of_orderTop`：sInter_of_orderTop {s : Set (Set α)} [OrderTo
p α] (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem iInter_of_orderTop {ι : Type*} {f : ι → Set α} [OrderTop α] (hs : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_orderTop (by simpa)
/-
**IsClub.sInter_of_cof_le_one** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：sInter_of_cof_le_one {s : Set (Set α)} (hα : cof α <= 1) (hs : forall x in
 s, IsClub x) : IsClub (⋂₀ s)
参数：Set α；hα : cof α <= 1；hs : forall x in s, IsClub x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsClub.sInter_of_orderTop`：sInter_of_orderTop {s : Set (Set α)} [OrderTo
p α] (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Order.one_lt_cof`：one_lt_cof [Nonempty α] [h : NoTopOrder α] : 1 < cof α
-/
theorem sInter_of_cof_le_one {s : Set (Set α)} (hα : cof α ≤ 1) (hs : ∀ x ∈ s, IsClub x) :
    IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  cases topOrderOrNoTopOrder α
  · exact .sInter_of_orderTop hs
  · cases one_lt_cof.not_ge hα
/-
**IsClub.iInter_of_cof_le_one** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：iInter_of_cof_le_one {ι : Type*} {f : ι -> Set α} (hα : cof α <= 1) (hs : 
forall i, IsClub (f i)) : IsClub (⋂ i, f i)
参数：hα : cof α <= 1；hs : forall i, IsClub (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `IsClub.sInter_of_cof_le_one`：sInter_of_cof_le_one {s : Set (Set α)} (hα 
: cof α <= 1) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem iInter_of_cof_le_one {ι : Type*} {f : ι → Set α} (hα : cof α ≤ 1) (hs : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  exact .sInter_of_cof_le_one hα (by simpa)

section WellFoundedLT
variable [WellFoundedLT α]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot

/-
**IsClub.sInter** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} [inst : LinearOrder α] [WellFoundedLT α] {s : Set (Set α)},
   Order.cof α ≠ Cardinal.aleph0 → Cardinal.mk ↑s < Order.cof α → (∀ x ∈ s, IsCl
ub x) → IsClub (⋂₀ s)
参数：Set α；∀ x ∈ s, IsClub x；⋂₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `IsClub.sInter_of_cof_le_one`：sInter_of_cof_le_one {s : Set (Set α)} (hα 
: cof α <= 1) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.cof_lt_aleph0_iff`：cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1
· 使用定理 `DirSupClosed.sInter`：DirSupClosed.sInter {s : Set (Set α)} (hs : forall 
x in s, DirSupClosed x) : DirSupClosed (⋂₀ s)
· 使用定理 `IsClub.dirSupClosed`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}
, IsClub s → DirSupClosed s
· 使用定理 `BddAbove.of_not_isCofinal`：BddAbove.of_not_isCofinal {s : Set α} (h : ¬ 
IsCofinal s) : BddAbove s
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Order.cof_le`：cof_le {s : Set α} (h : IsCofinal s) : cof α <= #s
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `IsClub.isLUB_mem`：isLUB_mem (hs : IsClub s) (ht : t subseteq s) (ht₀ : t
.Nonempty) (hx : IsLUB t x) : x in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
（共 34 条，此处仅展示前 30 条）
-/
protected theorem sInter {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : #s < cof α)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  cases isEmpty_or_nonempty α; · simp
  obtain hα | hα := hα.lt_or_gt
  · exact .sInter_of_cof_le_one (cof_lt_aleph0_iff.1 hα) hs
  refine ⟨.sInter fun x hx ↦ (hs x hx).dirSupClosed, fun a ↦ ?_⟩
  choose f hf using fun x : s ↦ (hs _ x.2).isCofinal
  let g : ℕ → α := Nat.rec a fun _ IH ↦ sSup (.range (f · IH))
  have hg : BddAbove (.range g) := by
    refine .of_not_isCofinal fun hg ↦ (cof_le hg).not_gt (hα.trans_le' ?_)
    simpa using mk_range_le_lift (f := g)
  refine ⟨_, fun t ht ↦ ?_, le_csSup hg ⟨0, rfl⟩⟩
  apply (hs t ht).isLUB_mem (t := .range fun n ↦ f ⟨t, ht⟩ (g n)) _ (range_nonempty _)
  · refine ⟨?_, fun b hb ↦ csSup_le' ?_⟩ <;> rintro _ ⟨n, rfl⟩
    · apply (le_csSup (.of_not_isCofinal _) _).trans (le_csSup hg ⟨n + 1, rfl⟩)
      · exact fun hg' ↦ (cof_le hg').not_gt (mk_range_le.trans_lt hsα)
      · use ⟨t, ht⟩
    · exact (hf ⟨t, ht⟩ _).2.trans <| hb ⟨_, rfl⟩
  · grind
/-
**IsClub.iInter** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} [inst : LinearOrder α] [WellFoundedLT α] {ι : Type u} {f : 
ι → Set α},   Order.cof α ≠ Cardinal.aleph0 →     Cardinal.lift.{v, u} (Cardinal
.mk ι) < Cardinal.lift.{u, v} (Order.cof α) →       (∀ (i : ι), IsClub (f i)) → 
IsClub (⋂ i, f i)
参数：Cardinal.mk ι；Order.cof α；∀ (i : ι), IsClub (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `IsClub.sInter`：∀ {α : Type v} [inst : LinearOrder α] [WellFoundedLT α] {
s : Set (Set α)},   Order.cof α ≠ Cardinal.aleph0 → Cardinal.mk ↑s < Order.cof α
 → …
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem iInter {ι : Type u} {f : ι → Set α} (hα : cof α ≠ ℵ₀)
    (hι : Cardinal.lift.{v} #ι < Cardinal.lift.{u} (cof α)) (hf : ∀ i, IsClub (f i)) :
    IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  refine IsClub.sInter hα ?_ (by simpa)
  rw [← Cardinal.lift_lt]
  exact mk_range_le_lift.trans_lt hι
/-
**IsClub.sInter_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：sInter_of_countable {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countabl
e) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
参数：Set α；hα : cof α != ℵ₀；hsα : s.Countable；hs : forall x in s, IsClub x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `IsClub.sInter_of_cof_le_one`：sInter_of_cof_le_one {s : Set (Set α)} (hα 
: cof α <= 1) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.cof_lt_aleph0_iff`：cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1
· 使用定理 `IsClub.sInter`：∀ {α : Type v} [inst : LinearOrder α] [WellFoundedLT α] {
s : Set (Set α)},   Order.cof α ≠ Cardinal.aleph0 → Cardinal.mk ↑s < Order.cof α
 → …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
-/
theorem sInter_of_countable {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : s.Countable)
    (hs : ∀ x ∈ s, IsClub x) : IsClub (⋂₀ s) := by
  obtain hα | hα := hα.lt_or_gt
  · apply IsClub.sInter_of_cof_le_one _ hs
    rwa [← cof_lt_aleph0_iff]
  · apply IsClub.sInter hα.ne' (hα.trans_le' _) hs
    rwa [le_aleph0_iff_set_countable]
/-
**IsClub.iInter_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：iInter_of_countable {ι : Sort*} {f : ι -> Set α} [Countable ι] (hα : cof α
 != ℵ₀) (hf : forall i, IsClub (f i)) : IsClub (⋂ i, f i)
参数：hα : cof α != ℵ₀；hf : forall i, IsClub (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `IsClub.sInter_of_countable`：sInter_of_countable {s : Set (Set α)} (hα : 
cof α != ℵ₀) (hsα : s.Countable) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem iInter_of_countable {ι : Sort*} {f : ι → Set α} [Countable ι] (hα : cof α ≠ ℵ₀)
    (hf : ∀ i, IsClub (f i)) : IsClub (⋂ i, f i) := by
  rw [← sInter_range]
  apply IsClub.sInter_of_countable hα (countable_range f)
  simpa
/-
**IsClub.inter** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：∀ {α : Type v} {s t : Set α} [inst : LinearOrder α] [WellFoundedLT α],   O
rder.cof α ≠ Cardinal.aleph0 → IsClub s → IsClub t → IsClub (s ∩ t)
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsClub.sInter_of_countable`：sInter_of_countable {s : Set (Set α)} (hα : 
cof α != ℵ₀) (hsα : s.Countable) (hs : forall x in s, IsClub x) : IsClub (⋂₀ s)
-/
protected theorem inter (hα : cof α ≠ ℵ₀) (hs : IsClub s) (ht : IsClub t) : IsClub (s ∩ t) := by
  simpa [hs, ht] using IsClub.sInter_of_countable (s := {s, t}) hα
/-
**IsClub._root_.Order.IsNormal.isClub_range** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.IsNormal.isClub_range {f : α → α} (hf : IsNormal f) : IsClub (.range f) :=
  ⟨hf.dirSupClosed_range, fun x ↦ ⟨_, ⟨x, rfl⟩, hf.strictMono.le_apply⟩⟩
/-
**IsClub._root_.Order.IsNormal.isClub_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `IsC
lub`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Order.IsNormal.isClub_fixedPoints {f : α → α} (hα : cof α ≠ ℵ₀) (hf : IsNormal f) :
    IsClub f.fixedPoints := by
  cases isEmpty_or_nonempty α; · simp
  refine ⟨fun s hs hs₀ _ a ha ↦ (hf.map_isLUB ha hs₀).unique ?_, fun a ↦ ?_⟩
  · rwa [image_congr hs, image_id']
  · cases topOrderOrNoTopOrder α with
    | inl => use ⊤; simpa using! hf.strictMono.id_le ⊤
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder] at h
      suffices BddAbove (.range fun n ↦ f^[n] a) from
        ⟨_, hf.iSup_iterate_mem_fixedPoints a this, le_csSup this ⟨0, rfl⟩⟩
      refine .of_not_isCofinal fun h ↦ (cof_le h).not_gt
        ((aleph0_le_cof.lt_of_ne' hα).trans_le' ?_)
      simpa using mk_range_le_lift (f := fun n : ℕ ↦ f^[n] a)

/-- Club sets in regular cardinals correspond one to one with normal functions. -/
/-
**IsClub._root_.Order.isNormal_enum_iff_isClub** 是 Mathlib 中的一个定理，位于命名空间 `IsClub
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Club sets in regular cardinals correspond one to one with normal functions.
-/
theorem _root_.Order.isNormal_enum_iff_isClub [IsRegularCardinalOrder α]
    {s : Set α} {hs : IsCofinal s} : IsNormal (Subtype.val ∘ enum s hs) ↔ IsClub s := by
  simp_rw [isClub_iff, hs, and_true, isNormal_enum_iff_dirSupClosed]
/-
**IsClub.isNormal_enum** 是 Mathlib 中的一个定理，位于命名空间 `IsClub`。
形式化陈述：isNormal_enum [IsRegularCardinalOrder α] {s : Set α} (hs : IsClub s) : IsN
ormal (Subtype.val ∘ enum s hs.isCofinal)
参数：hs : IsClub s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClub.isCofinal`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}, I
sClub s → IsCofinal s
· 使用定理 `Order.isNormal_enum_iff_isClub`：∀ {α : Type v} [inst : LinearOrder α] [i
nst_1 : WellFoundedLT α] [inst_2 : IsRegularCardinalOrder α] {s : Set α}   {hs :
 IsCofinal s}, Order…
-/
theorem isNormal_enum [IsRegularCardinalOrder α] {s : Set α} (hs : IsClub s) :
    IsNormal (Subtype.val ∘ enum s hs.isCofinal) :=
  isNormal_enum_iff_isClub.2 hs

end WellFoundedLT
end IsClub

/-! ### Stationary sets -/

/-- A set is called stationary when it intersects all club sets. -/
@[expose]
/-
**IsStationary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsStationary (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is called stationary when it intersects all club sets.
-/
def IsStationary (s : Set α) : Prop :=
  ∀ ⦃t⦄, IsClub t → (s ∩ t).Nonempty
/-
**not_isStationary_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isStationary_iff : ¬ IsStationary s ↔ exists t, IsClub t ∧ Disjoint s 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_isStationary_iff : ¬ IsStationary s ↔ ∃ t, IsClub t ∧ Disjoint s t := by
  simp [IsStationary, disjoint_iff, not_nonempty_iff_eq_empty]

@[gcongr]
/-
**IsStationary.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStationary.mono (hs : IsStationary s) (h : s subseteq t) : IsStationary 
t
参数：hs : IsStationary s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
-/
theorem IsStationary.mono (hs : IsStationary s) (h : s ⊆ t) : IsStationary t :=
  fun _u hu ↦ (hs hu).mono (inter_subset_inter_left _ h)
/-
**IsStationary.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStationary.nonempty (hs : IsStationary s) : s.Nonempty
参数：hs : IsStationary s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsClub.univ`：∀ {α : Type v} [inst : LinearOrder α], IsClub Set.univ
-/
theorem IsStationary.nonempty (hs : IsStationary s) : s.Nonempty := by
  simpa using hs .univ
/-
**isStationary_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_univ_iff : IsStationary (.univ (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStationary_univ_iff : IsStationary (.univ (α := α)) ↔ Nonempty α := by
  simp [IsStationary, ← not_imp_not (b := IsClub _), not_nonempty_iff_eq_empty,
    isClub_empty_iff]

@[simp]
/-
**IsStationary.univ** 是 Mathlib 中的一个定理，位于命名空间 `IsStationary`。
形式化陈述：∀ {α : Type v} [inst : LinearOrder α] [Nonempty α], IsStationary Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isStationary_univ_iff`：isStationary_univ_iff : IsStationary (.univ (α
-/
protected theorem IsStationary.univ [Nonempty α] : IsStationary (.univ (α := α)) :=
  isStationary_univ_iff.2 ‹_›

@[simp]
/-
**not_isStationary_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isStationary_empty : ¬ IsStationary (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsClub.univ`：∀ {α : Type v} [inst : LinearOrder α], IsClub Set.univ
-/
theorem not_isStationary_empty : ¬ IsStationary (∅ : Set α) := by
  intro h
  simpa using h .univ

@[simp]
/-
**not_isStationary_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isStationary_of_isEmpty [IsEmpty α] : ¬ IsStationary s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isStationary_empty`：not_isStationary_empty : ¬ IsStationary (∅ : Set
 α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
theorem not_isStationary_of_isEmpty [IsEmpty α] : ¬ IsStationary s :=
  s.eq_empty_of_isEmpty ▸ not_isStationary_empty
/-
**IsStationary.of_not_isCofinal_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal sᶜ) : IsStationary s
参数：hs : ¬ IsCofinal sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isCofinal_iff`：not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ exist
s x, forall y in s, y < x
· 使用定理 `IsClub.isCofinal`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α}, I
sClub s → IsCofinal s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem IsStationary.of_not_isCofinal_compl (hs : ¬ IsCofinal sᶜ) : IsStationary s := by
  intro t ht
  obtain ⟨a, ha⟩ := not_isCofinal_iff.1 hs
  obtain ⟨b, hb, hb'⟩ := ht.isCofinal a
  refine ⟨b, ?_, hb⟩
  contrapose! ha
  exact ⟨b, ha, hb'⟩
/-
**isStationary_sUnion_iff_of_cof_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_sUnion_iff_of_cof_le_one {s : Set (Set α)} (hα : cof α <= 1) 
: IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x where mp h
参数：Set α；hα : cof α <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsClub.iInter_of_cof_le_one`：iInter_of_cof_le_one {ι : Type*} {f : ι -> 
Set α} (hα : cof α <= 1) (hs : forall i, IsClub (f i)) : IsClub (⋂ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_sUnion_left`：disjoint_sUnion_left {S : Set (Set α)} {t : Se
t α} : Disjoint (⋃₀ S) t ↔ forall s in S, Disjoint s t
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsStationary.mono`：IsStationary.mono (hs : IsStationary s) (h : s subset
eq t) : IsStationary t
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem isStationary_sUnion_iff_of_cof_le_one {s : Set (Set α)} (hα : cof α ≤ 1) :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter_of_cof_le_one hα
      simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx ↦ (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ ↦ hx.mono (subset_sUnion_of_mem hxs)
/-
**isStationary_iUnion_iff_of_cof_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_iUnion_iff_of_cof_le_one {ι : Sort*} {f : ι -> Set α} (hα : c
of α <= 1) : IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i)
参数：hα : cof α <= 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `isStationary_sUnion_iff_of_cof_le_one`：isStationary_sUnion_iff_of_cof_le
_one {s : Set (Set α)} (hα : cof α <= 1) : IsStationary (⋃₀ s) ↔ exists x in s, 
IsStationary x where mp h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStationary_iUnion_iff_of_cof_le_one {ι : Sort*} {f : ι → Set α} (hα : cof α ≤ 1) :
    IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff_of_cof_le_one hα]
  simp
/-
**isStationary_sUnion_iff_of_orderTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_sUnion_iff_of_orderTop [OrderTop α] {s : Set (Set α)} : IsSta
tionary (⋃₀ s) ↔ exists x in s, IsStationary x
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isStationary_sUnion_iff_of_cof_le_one`：isStationary_sUnion_iff_of_cof_le
_one {s : Set (Set α)} (hα : cof α <= 1) : IsStationary (⋃₀ s) ↔ exists x in s, 
IsStationary x where mp h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_one`：cof_eq_one [OrderTop α] : cof α = 1
-/
theorem isStationary_sUnion_iff_of_orderTop [OrderTop α] {s : Set (Set α)} :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x :=
  isStationary_sUnion_iff_of_cof_le_one (by simp)
/-
**isStationary_iUnion_iff_of_orderTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_iUnion_iff_of_orderTop [OrderTop α] {ι : Sort*} {f : ι -> Set
 α} : IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isStationary_iUnion_iff_of_cof_le_one`：isStationary_iUnion_iff_of_cof_le
_one {ι : Sort*} {f : ι -> Set α} (hα : cof α <= 1) : IsStationary (⋃ i, f i) ↔ 
exists i, IsStationary (f i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.cof_eq_one`：cof_eq_one [OrderTop α] : cof α = 1
-/
theorem isStationary_iUnion_iff_of_orderTop [OrderTop α] {ι : Sort*} {f : ι → Set α} :
    IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) :=
  isStationary_iUnion_iff_of_cof_le_one (by simp)

section WellFoundedLT
variable [WellFoundedLT α]

/-
**IsClub.isStationary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClub.isStationary [Nonempty α] (hα : cof α != ℵ₀) (hs : IsClub s) : IsSt
ationary s
参数：hα : cof α != ℵ₀；hs : IsClub s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClub.nonempty`：∀ {α : Type v} {s : Set α} [inst : LinearOrder α] [None
mpty α], IsClub s → s.Nonempty
· 使用定理 `IsClub.inter`：∀ {α : Type v} {s t : Set α} [inst : LinearOrder α] [WellF
oundedLT α],   Order.cof α ≠ Cardinal.aleph0 → IsClub s → IsClub t → IsClub (s ∩
 t…
-/
theorem IsClub.isStationary [Nonempty α] (hα : cof α ≠ ℵ₀) (hs : IsClub s) : IsStationary s :=
  fun _ ht ↦ (hs.inter hα ht).nonempty
/-
**isStationary_sUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_sUnion_iff {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : #s < c
of α) : IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x where mp h
参数：Set α；hα : cof α != ℵ₀；hsα : #s < cof α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsClub.iInter`：∀ {α : Type v} [inst : LinearOrder α] [WellFoundedLT α] {
ι : Type u} {f : ι → Set α},   Order.cof α ≠ Cardinal.aleph0 →     Cardinal.lift
.{v…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.disjoint_sUnion_left`：disjoint_sUnion_left {S : Set (Set α)} {t : Se
t α} : Disjoint (⋃₀ S) t ↔ forall s in S, Disjoint s t
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsStationary.mono`：IsStationary.mono (hs : IsStationary s) (h : s subset
eq t) : IsStationary t
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
-/
theorem isStationary_sUnion_iff {s : Set (Set α)} (hα : cof α ≠ ℵ₀) (hsα : #s < cof α) :
    IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x where
  mp h := by
    contrapose! h
    simp_rw [not_isStationary_iff] at h ⊢
    choose f hf hxf using h
    refine ⟨⋂ x : s, f _ x.2, ?_, ?_⟩
    · apply IsClub.iInter hα <;> simpa
    · rw [disjoint_sUnion_left]
      exact fun x hx ↦ (hxf _ hx).mono_right (iInter_subset _ ⟨x, hx⟩)
  mpr := fun ⟨x, hxs, hx⟩ ↦ hx.mono (subset_sUnion_of_mem hxs)
/-
**isStationary_iUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_iUnion_iff {ι : Type u} {f : ι -> Set α} (hα : cof α != ℵ₀) (
hι : lift.{v} #ι < lift.{u} (cof α)) : IsStationary (⋃ i, f i) ↔ exists i, IsSta
tionary (f i)
参数：hα : cof α != ℵ₀；hι : lift.{v} #ι < lift.{u} (cof α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `isStationary_sUnion_iff`：isStationary_sUnion_iff {s : Set (Set α)} (hα :
 cof α != ℵ₀) (hsα : #s < cof α) : IsStationary (⋃₀ s) ↔ exists x in s, IsStatio
nary x where …
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStationary_iUnion_iff {ι : Type u} {f : ι → Set α} (hα : cof α ≠ ℵ₀)
    (hι : lift.{v} #ι < lift.{u} (cof α)) : IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff hα]
  · simp
  · rw [← Cardinal.lift_lt]
    exact mk_range_le_lift.trans_lt hι
/-
**isStationary_sUnion_iff_of_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_sUnion_iff_of_countable {s : Set (Set α)} (hα : cof α != ℵ₀) 
(hsα : s.Countable) : IsStationary (⋃₀ s) ↔ exists x in s, IsStationary x
参数：Set α；hα : cof α != ℵ₀；hsα : s.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `isStationary_sUnion_iff_of_cof_le_one`：isStationary_sUnion_iff_of_cof_le
_one {s : Set (Set α)} (hα : cof α <= 1) : IsStationary (⋃₀ s) ↔ exists x in s, 
IsStationary x where mp h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.cof_lt_aleph0_iff`：cof_lt_aleph0_iff : cof α < ℵ₀ ↔ cof α <= 1
· 使用定理 `isStationary_sUnion_iff`：isStationary_sUnion_iff {s : Set (Set α)} (hα :
 cof α != ℵ₀) (hsα : #s < cof α) : IsStationary (⋃₀ s) ↔ exists x in s, IsStatio
nary x where …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
-/
theorem isStationary_sUnion_iff_of_countable {s : Set (Set α)} (hα : cof α ≠ ℵ₀)
    (hsα : s.Countable) : IsStationary (⋃₀ s) ↔ ∃ x ∈ s, IsStationary x := by
  obtain hα | hα := hα.lt_or_gt
  · apply isStationary_sUnion_iff_of_cof_le_one
    rwa [← cof_lt_aleph0_iff]
  · apply isStationary_sUnion_iff hα.ne' (hα.trans_le' _)
    rwa [le_aleph0_iff_set_countable]
/-
**isStationary_iUnion_iff_of_countable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_iUnion_iff_of_countable {ι : Sort*} {f : ι -> Set α} [Countab
le ι] (hα : cof α != ℵ₀) : IsStationary (⋃ i, f i) ↔ exists i, IsStationary (f i
)
参数：hα : cof α != ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `isStationary_sUnion_iff_of_countable`：isStationary_sUnion_iff_of_countab
le {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countable) : IsStationary (⋃₀ s
) ↔ exists x in s, IsStati…
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStationary_iUnion_iff_of_countable {ι : Sort*} {f : ι → Set α} [Countable ι]
    (hα : cof α ≠ ℵ₀) : IsStationary (⋃ i, f i) ↔ ∃ i, IsStationary (f i) := by
  rw [← sUnion_range, isStationary_sUnion_iff_of_countable hα (countable_range f)]
  simp
/-
**isStationary_union_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStationary_union_iff (hα : cof α != ℵ₀) : IsStationary (s union t) ↔ IsS
tationary s ∨ IsStationary t
参数：hα : cof α != ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isStationary_sUnion_iff_of_countable`：isStationary_sUnion_iff_of_countab
le {s : Set (Set α)} (hα : cof α != ℵ₀) (hsα : s.Countable) : IsStationary (⋃₀ s
) ↔ exists x in s, IsStati…
-/
theorem isStationary_union_iff (hα : cof α ≠ ℵ₀) :
    IsStationary (s ∪ t) ↔ IsStationary s ∨ IsStationary t := by
  simpa using isStationary_sUnion_iff_of_countable (s := {s, t}) hα

end WellFoundedLT

