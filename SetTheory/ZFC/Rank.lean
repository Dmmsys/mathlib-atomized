/-
Copyright (c) 2024 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Ordinal ranks of PSet and ZFSet

In this file, we define the ordinal ranks of `PSet` and `ZFSet`. These ranks are the same as
`IsWellFounded.rank` over `∈`, but are defined in a way that the universe levels of ranks are the
same as the indexing types.

## Definitions

* `PSet.rank`: Ordinal rank of a pre-set.
* `ZFSet.rank`: Ordinal rank of a ZFC set.
-/

@[expose] public section

universe u v

open Ordinal Order

/-! ### PSet rank -/

namespace PSet

/-- The ordinal rank of a pre-set -/
/-
**PSet.rank** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u} → Ordinal.{u}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal rank of a pre-set
-/
noncomputable def rank : PSet.{u} → Ordinal.{u}
  | ⟨_, A⟩ => ⨆ a, succ (rank (A a))
/-
**PSet.rank_congr** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_congr : forall {x y : PSet}, Equiv x y -> rank x = rank y | ⟨_, _⟩, ⟨
_, _⟩, ⟨αβ, βα⟩ => by apply congr_arg sSup ext constructor <;> simp only [Set.me
m_range, forall_exists_index] <;> intro a h · obtain ⟨b, h'⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rank_congr : ∀ {x y : PSet}, Equiv x y → rank x = rank y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by
    apply congr_arg sSup
    ext
    constructor <;> simp only [Set.mem_range, forall_exists_index] <;> intro a h
    · obtain ⟨b, h'⟩ := αβ a
      exists b
      rw [← h, rank_congr h']
    · obtain ⟨b, h'⟩ := βα a
      exists b
      rw [← h, rank_congr h']
/-
**PSet.rank_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.rank_congr`：rank_congr : forall {x y : PSet}, Equiv x y -> rank x =
 rank y | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by apply congr_arg sSup ext constructor <;
> sim…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem rank_lt_of_mem : ∀ {x y : PSet}, y ∈ x → rank y < rank x
  | ⟨_, _⟩, _, ⟨_, h⟩ => by
    rw [rank_congr h, ← succ_le_iff]
    apply Ordinal.le_iSup
/-
**PSet.rank_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {o : Ordinal.{u_1}} {x : PSet.{u_1}}, x.rank ≤ o ↔ ∀ ⦃y : PSet.{u_1}⦄, y
 ∈ x → y.rank < o
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
-/
theorem rank_le_iff {o : Ordinal} : ∀ {x : PSet}, rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o
  | ⟨_, A⟩ => by
    refine ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h, fun h ↦ Ordinal.iSup_le fun a ↦ ?_⟩
    rw [succ_le_iff]
    exact h (Mem.mk A a)
/-
**PSet.lt_rank_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ exists y in x, o <= ra
nk y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PSet.rank_le_iff`：∀ {o : Ordinal.{u_1}} {x : PSet.{u_1}}, x.rank ≤ o ↔ ∀
 ⦃y : PSet.{u_1}⦄, y ∈ x → y.rank < o
-/
theorem lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by
  contrapose!; exact rank_le_iff

variable {x y : PSet.{u}}
/-
**PSet.rank_mono** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {x y : PSet.{u}}, x ⊆ y → x.rank ≤ y.rank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.rank_le_iff`：∀ {o : Ordinal.{u_1}} {x : PSet.{u_1}}, x.rank ≤ o ↔ ∀
 ⦃y : PSet.{u_1}⦄, y ∈ x → y.rank < o
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
· 使用定理 `PSet.mem_of_subset`：∀ {x y z : PSet.{u_1}}, x ⊆ y → z ∈ x → z ∈ y
-/
@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (mem_of_subset h h₁)

@[simp]
/-
**PSet.rank_empty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_empty : rank ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.empty_def`：empty_def : (∅ : PSet) = ⟨_, PEmpty.elim⟩
· 使用定理 `PSet.rank.eq_1`：∀ (α : Type u) (A : α → PSet.{u}), (PSet.mk α A).rank = 
⨆ a, Order.succ (A a).rank
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_empty : rank ∅ = 0 := by simp [empty_def, rank]

@[simp]
/-
**PSet.rank_insert** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_insert (x y : PSet) : rank (insert x y) = max (succ (rank x)) (rank y
)
参数：x y : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.rank_congr`：rank_congr : forall {x y : PSet}, Equiv x y -> rank x =
 rank y | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by apply congr_arg sSup ext constructor <;
> sim…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `LT.lt.succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder 
α] {a b : α}, a < b → Order.succ a ≤ b
· 使用定理 `PSet.mem_insert`：mem_insert (x y : PSet) : x in insert x y
· 使用定理 `PSet.rank_mono`：∀ {x y : PSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.subset_iff`：subset_iff {x y : PSet} : x subseteq y ↔ forall ⦃z⦄, z 
in x -> z in y
· 使用定理 `PSet.mem_insert_of_mem`：mem_insert_of_mem {y z : PSet} (x) (h : z in y) 
: z in insert x y
-/
theorem rank_insert (x y : PSet) : rank (insert x y) = max (succ (rank x)) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_insert_iff]
    rintro _ (h | h)
    · simp [rank_congr h]
    · simp [rank_lt_of_mem h]
  · apply max_le
    · exact (rank_lt_of_mem (mem_insert x y)).succ_le
    · exact rank_mono (subset_iff.2 fun z => mem_insert_of_mem x)

@[simp]
/-
**PSet.rank_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_singleton (x : PSet) : rank {x} = succ (rank x)
参数：x : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PSet.rank_insert`：rank_insert (x y : PSet) : rank (insert x y) = max (su
cc (rank x)) (rank y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `PSet.rank_empty`：rank_empty : rank ∅ = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_singleton (x : PSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)
/-
**PSet.rank_pair** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_pair (x y : PSet) : rank {x, y} = max (succ (rank x)) (succ (rank y))
参数：x y : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.rank_insert`：rank_insert (x y : PSet) : rank (insert x y) = max (su
cc (rank x)) (rank y)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `PSet.rank_singleton`：rank_singleton (x : PSet) : rank {x} = succ (rank x
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_pair (x y : PSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
/-
**PSet.rank_powerset** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_powerset (x : PSet) : rank (powerset x) = succ (rank x)
参数：x : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `PSet.rank_mono`：∀ {x y : PSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem rank_powerset (x : PSet) : rank (powerset x) = succ (rank x) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_powerset, lt_succ_iff]
    intro
    exact rank_mono
  · rw [succ_le_iff]
    apply rank_lt_of_mem
    simp

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
/-
**PSet.rank_sUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_sUnion_le (x : PSet) : rank (⋃₀ x) <= rank x
参数：x : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank

--- 原说明 ---
For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`.
-/
theorem rank_sUnion_le (x : PSet) : rank (⋃₀ x) ≤ rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption
/-
**PSet.le_succ_rank_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：le_succ_rank_sUnion (x : PSet) : rank x <= succ (rank (⋃₀ x))
参数：x : PSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PSet.rank_powerset`：rank_powerset (x : PSet) : rank (powerset x) = succ 
(rank x)
· 使用定理 `PSet.rank_mono`：∀ {x y : PSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `PSet.subset_iff`：subset_iff {x y : PSet} : x subseteq y ↔ forall ⦃z⦄, z 
in x -> z in y
· 使用定理 `PSet.mem_powerset`：mem_powerset : forall {x y : PSet}, y in powerset x ↔
 y subseteq x | ⟨_, A⟩, ⟨_, B⟩ => ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a,
 _⟩ => …
· 使用定理 `PSet.mem_sUnion`：mem_sUnion : forall {x y : PSet.{u}}, y in ⋃₀ x ↔ exist
s z in x, y in z | ⟨α, A⟩, y => ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ => h
ave :…
-/
theorem le_succ_rank_sUnion (x : PSet) : rank x ≤ succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  rw [subset_iff]
  intro z _
  rw [mem_powerset, subset_iff]
  intro _ _
  rw [mem_sUnion]
  exists z

/-- `PSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
/-
**PSet.rank_eq_wfRank** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用定理 `PSet.mem_wf`：mem_wf : @WellFounded PSet (· in ·)
· 使用定理 `PSet.instIsWellFoundedMem`：IsWellFounded PSet.{u_1} fun x1 x2 => x1 ∈ x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsWellFounded.rank_eq`：rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }
, Order.succ (rank r b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Ordinal.lt_lift_iff`：lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v
}} : b < lift.{v} a ↔ exists a' < a, lift.{v} a' = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.lt_rank_iff`：lt_rank_iff {o : Ordinal} {x : PSet} : o < rank x ↔ ex
ists y in x, o <= rank y
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank

--- 原说明 ---
`PSet.rank` is equal to the `IsWellFounded.rank` over `∈`.
-/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := PSet) (· ∈ ·) x := by
  induction x using mem_wf.induction with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y ∈ x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end PSet

/-! ### ZFSet rank -/

namespace ZFSet

variable {x y : ZFSet.{u}}

/-- The ordinal rank of a ZFC set -/
/-
**ZFSet.rank** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：rank : ZFSet.{u} -> Ordinal.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.rank_congr`：rank_congr : forall {x y : PSet}, Equiv x y -> rank x =
 rank y | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ => by apply congr_arg sSup ext constructor <;
> sim…

--- 原说明 ---
The ordinal rank of a ZFC set
-/
noncomputable def rank : ZFSet.{u} → Ordinal.{u} :=
  Quotient.lift _ fun _ _ => PSet.rank_congr

@[simp]
/-
**ZFSet.rank_mk** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_mk (x : PSet) : rank (.mk x) = x.rank
参数：x : PSet。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rank_mk (x : PSet) : rank (.mk x) = x.rank :=
  rfl
/-
**ZFSet.rank_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_lt_of_mem : y in x -> rank y < rank x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `PSet.rank_lt_of_mem`：∀ {x y : PSet.{u_1}}, y ∈ x → y.rank < x.rank
-/
theorem rank_lt_of_mem : y ∈ x → rank y < rank x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.rank_lt_of_mem
/-
**ZFSet.rank_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_le_iff {o : Ordinal} : rank x <= o ↔ forall ⦃y⦄, y in x -> rank y < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.rank_le_iff`：∀ {o : Ordinal.{u_1}} {x : PSet.{u_1}}, x.rank ≤ o ↔ ∀
 ⦃y : PSet.{u_1}⦄, y ∈ x → y.rank < o
-/
theorem rank_le_iff {o : Ordinal} : rank x ≤ o ↔ ∀ ⦃y⦄, y ∈ x → rank y < o :=
  ⟨fun h _ h' => (rank_lt_of_mem h').trans_le h,
    Quotient.inductionOn x fun _ h =>
      PSet.rank_le_iff.2 fun y h' => @h ⟦y⟧ h'⟩
/-
**ZFSet.lt_rank_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：lt_rank_iff {o : Ordinal} : o < rank x ↔ exists y in x, o <= rank y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ZFSet.rank_le_iff`：rank_le_iff {o : Ordinal} : rank x <= o ↔ forall ⦃y⦄,
 y in x -> rank y < o
-/
theorem lt_rank_iff {o : Ordinal} : o < rank x ↔ ∃ y ∈ x, o ≤ rank y := by
  contrapose!; exact rank_le_iff
/-
**ZFSet.rank_mono** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.rank_le_iff`：rank_le_iff {o : Ordinal} : rank x <= o ↔ forall ⦃y⦄,
 y in x -> rank y < o
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
-/
@[gcongr] theorem rank_mono (h : x ⊆ y) : rank x ≤ rank y :=
  rank_le_iff.2 fun _ h₁ => rank_lt_of_mem (h h₁)

@[simp]
/-
**ZFSet.rank_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_empty : rank ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.rank_empty`：rank_empty : rank ∅ = 0
-/
theorem rank_empty : rank ∅ = 0 := PSet.rank_empty

@[simp]
/-
**ZFSet.rank_insert** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_insert (x y : ZFSet) : rank (insert x y) = max (succ (rank x)) (rank 
y)
参数：x y : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `PSet.rank_insert`：rank_insert (x y : PSet) : rank (insert x y) = max (su
cc (rank x)) (rank y)
-/
theorem rank_insert (x y : ZFSet) : rank (insert x y) = max (succ (rank x)) (rank y) :=
  Quotient.inductionOn₂ x y PSet.rank_insert

@[simp]
/-
**ZFSet.rank_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_singleton (x : ZFSet) : rank {x} = succ (rank x)
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZFSet.rank_insert`：rank_insert (x y : ZFSet) : rank (insert x y) = max (
succ (rank x)) (rank y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `ZFSet.rank_empty`：rank_empty : rank ∅ = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_singleton (x : ZFSet) : rank {x} = succ (rank x) :=
  (rank_insert _ _).trans (by simp)
/-
**ZFSet.rank_pair** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_pair (x y : ZFSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)
)
参数：x y : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.rank_insert`：rank_insert (x y : ZFSet) : rank (insert x y) = max (
succ (rank x)) (rank y)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `ZFSet.rank_singleton`：rank_singleton (x : ZFSet) : rank {x} = succ (rank
 x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_pair (x y : ZFSet) : rank {x, y} = max (succ (rank x)) (succ (rank y)) := by
  simp

@[simp]
/-
**ZFSet.rank_union** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_union (x y : ZFSet) : rank (x union y) = max (rank x) (rank y)
参数：x y : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `ZFSet.rank_mono`：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem rank_union (x y : ZFSet) : rank (x ∪ y) = max (rank x) (rank y) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_union, lt_max_iff]
    intro
    apply Or.imp <;> apply rank_lt_of_mem
  · apply max_le <;> apply rank_mono <;> intro _ h <;> simp [h]

@[simp]
/-
**ZFSet.rank_powerset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_powerset (x : ZFSet) : rank (powerset x) = succ (rank x)
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `PSet.rank_powerset`：rank_powerset (x : PSet) : rank (powerset x) = succ 
(rank x)
-/
theorem rank_powerset (x : ZFSet) : rank (powerset x) = succ (rank x) :=
  Quotient.inductionOn x PSet.rank_powerset

/-- For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`. -/
/-
**ZFSet.rank_sUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_sUnion_le (x : ZFSet) : rank (⋃₀ x) <= rank x
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x

--- 原说明 ---
For the rank of `⋃₀ x`, we only have `rank (⋃₀ x) ≤ rank x ≤ rank (⋃₀ x) + 1`.

This inequality is split into `rank_sUnion_le` and `le_succ_rank_sUnion`.
-/
theorem rank_sUnion_le (x : ZFSet) : rank (⋃₀ x) ≤ rank x := by
  simp_rw [rank_le_iff, mem_sUnion]
  intro _ ⟨_, _, _⟩
  trans <;> apply rank_lt_of_mem <;> assumption
/-
**ZFSet.le_succ_rank_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：le_succ_rank_sUnion (x : ZFSet) : rank x <= succ (rank (⋃₀ x))
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.rank_powerset`：rank_powerset (x : ZFSet) : rank (powerset x) = suc
c (rank x)
· 使用定理 `ZFSet.rank_mono`：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `ZFSet.mem_powerset`：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y
 subseteq x
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
-/
theorem le_succ_rank_sUnion (x : ZFSet) : rank x ≤ succ (rank (⋃₀ x)) := by
  rw [← rank_powerset]
  apply rank_mono
  intro z _
  rw [mem_powerset]
  intro _ _
  rw [mem_sUnion]
  exists z

@[simp]
/-
**ZFSet.rank_range** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_range {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u}) : rank (range f)
 = ⨆ i, succ (rank (f i))
参数：f : α -> ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
-/
theorem rank_range {α : Type*} [Small.{u} α] (f : α → ZFSet.{u}) :
    rank (range f) = ⨆ i, succ (rank (f i)) := by
  apply (Ordinal.iSup_le _).antisymm'
  · simpa [rank_le_iff, ← add_one_le_iff] using Ordinal.le_iSup _
  · simp [rank_lt_of_mem]

@[simp]
/-
**ZFSet.rank_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_iUnion {α : Type*} [Small.{u} α] (f : α -> ZFSet.{u}) : rank (⋃ i, f 
i) = ⨆ i, rank (f i)
参数：f : α -> ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `ZFSet.rank_mono`：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `ZFSet.subset_iUnion`：subset_iUnion (f : α -> ZFSet.{u}) (i : α) : f i su
bseteq ⋃ i, f i
-/
theorem rank_iUnion {α : Type*} [Small.{u} α] (f : α → ZFSet.{u}) :
    rank (⋃ i, f i) = ⨆ i, rank (f i) := by
  apply le_antisymm
  · simp_rw [rank_le_iff, mem_iUnion]
    intro y ⟨i, hy⟩
    exact (rank_lt_of_mem hy).trans_le (Ordinal.le_iSup _ _)
  · exact Ordinal.iSup_le fun i => rank_mono (subset_iUnion f i)

/-- `ZFSet.rank` is equal to the `IsWellFounded.rank` over `∈`. -/
/-
**ZFSet.rank_eq_wfRank** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.inductionOn`：inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (f
orall y in x, p y) -> p x) : p x
· 使用定理 `ZFSet.instIsWellFoundedMem`：IsWellFounded ZFSet.{u_1} fun x1 x2 => x1 ∈ 
x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsWellFounded.rank_eq`：rank_eq (a : α) : rank r a = ⨆ b : { b // r b a }
, Order.succ (rank r b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Ordinal.lt_lift_iff`：lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v
}} : b < lift.{v} a ↔ exists a' < a, lift.{v} a' = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.lt_rank_iff`：lt_rank_iff {o : Ordinal} : o < rank x ↔ exists y in 
x, o <= rank y
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x

--- 原说明 ---
`ZFSet.rank` is equal to the `IsWellFounded.rank` over `∈`.
-/
theorem rank_eq_wfRank : lift.{u + 1, u} (rank x) = IsWellFounded.rank (α := ZFSet) (· ∈ ·) x := by
  induction x using inductionOn with | _ x ih
  rw [IsWellFounded.rank_eq]
  simp_rw [← fun y : { y // y ∈ x } => ih y y.2]
  apply (le_of_forall_lt _).antisymm (Ordinal.iSup_le _) <;> intro h
  · rw [lt_lift_iff]
    rintro ⟨o, h, rfl⟩
    simpa [Ordinal.lt_iSup_iff] using lt_rank_iff.1 h
  · simpa using rank_lt_of_mem h.2

end ZFSet

