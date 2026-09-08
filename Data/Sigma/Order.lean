/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sigma.Lex
public import Mathlib.Util.Notation3
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `_root_.Lex (Sigma α)`: Sigma type equipped with the lexicographic order.
  Type synonym of `Σ i, α i`.

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `Equiv.sigma_congr_left`, `Equiv.sigma_congr`, `Equiv.sigma_assoc`,
`Equiv.sigma_prod_of_equiv`, `Equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/

@[expose] public section


namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders on `Sigma` -/

/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
/-
**Sigma.LE** 是 Mathlib 中的一个归纳类型，位于命名空间 `Sigma`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → [(i : ι) → LE (α i)] → (i : ι) × α i
 → (i : ι) × α i → Prop
参数：i : ι；α i；i : ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`.
-/
protected inductive LE [∀ i, LE (α i)] : ∀ _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a ≤ b → Sigma.LE ⟨i, a⟩ ⟨i, b⟩

/-- Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`. -/
/-
**Sigma.LT** 是 Mathlib 中的一个归纳类型，位于命名空间 `Sigma`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → [(i : ι) → LT (α i)] → (i : ι) × α i
 → (i : ι) × α i → Prop
参数：i : ι；α i；i : ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`.
-/
protected inductive LT [∀ i, LT (α i)] : ∀ _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a < b → Sigma.LT ⟨i, a⟩ ⟨i, b⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance [∀ i, LE (α i)] : LE (Σ i, α i) where
  le := Sigma.LE
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance [∀ i, LT (α i)] : LT (Σ i, α i) where
  lt := Sigma.LT

@[simp]
/-
**Sigma.mk_le_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：mk_le_mk_iff [forall i, LE (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α)
 <= ⟨i, b⟩ ↔ a <= b
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_le_mk_iff [∀ i, LE (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LE.fiber _ _ _⟩

@[simp]
/-
**Sigma.mk_lt_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：mk_lt_mk_iff [forall i, LT (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α)
 < ⟨i, b⟩ ↔ a < b
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_lt_mk_iff [∀ i, LT (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LT.fiber _ _ _⟩
/-
**Sigma.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：le_def [forall i, LE (α i)] {a b : Σ i, α i} : a <= b ↔ exists h : a.1 = b
.1, h.rec a.2 <= b.2
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_def [∀ i, LE (α i)] {a b : Σ i, α i} : a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 := by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LE.fiber _ _ _ h
/-
**Sigma.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：lt_def [forall i, LT (α i)] {a b : Σ i, α i} : a < b ↔ exists h : a.1 = b.
1, h.rec a.2 < b.2
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_def [∀ i, LT (α i)] {a b : Σ i, α i} : a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2 := by
  constructor
  · rintro ⟨i, a, b, h⟩
    exact ⟨rfl, h⟩
  · obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    rintro ⟨rfl : i = j, h⟩
    exact LT.fiber _ _ _ h
/-
**Sigma.preorder** 是 Mathlib 中的一个定义，位于命名空间 `Sigma`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → [(i : ι) → Preorder (α i)] → Preorde
r ((i : ι) × α i)
参数：i : ι；α i；(i : ι) × α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance preorder [∀ i, Preorder (α i)] : Preorder (Σ i, α i) :=
  { le_refl := fun ⟨i, a⟩ => Sigma.LE.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      exact LE.fiber i a c (hab.trans hbc),
    lt_iff_le_not_ge := fun _ _ => by
      constructor
      · rintro ⟨i, a, b, hab⟩
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_iff_le_not_ge]
      · rintro ⟨⟨i, a, b, hab⟩, h⟩
        rw [mk_le_mk_iff] at h
        exact mk_lt_mk_iff.2 (hab.lt_of_not_ge h) }
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, PartialOrder (α i)] : PartialOrder (Σ i, α i) :=
  { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
      exact congr_arg (Sigma.mk _ ·) <| hab.antisymm hba }
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    obtain ⟨c, ha, hb⟩ := exists_between h
    exact ⟨⟨i, c⟩, LT.fiber i a c ha, LT.fiber i c b hb⟩

/-! ### Lexicographical order on `Sigma` -/


namespace Lex
/-- The notation `Σₗ i, α i` refers to a sigma type equipped with the lexicographic order. -/
notation3 "Σₗ " (...) ", " r:(scoped p => _root_.Lex (Sigma p)) => r

/-- The lexicographical `≤` on a sigma type. -/
/-
**Sigma.Lex.LE** 是 Mathlib 中的一个定义，位于命名空间 `Sigma.Lex`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → [LT ι] → [(i : ι) → LE (α i)] → LE (
Σₗ (i : ι), α i)
参数：i : ι；α i；Σₗ (i : ι), α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical `≤` on a sigma type.
-/
protected instance LE [LT ι] [∀ i, LE (α i)] : LE (Σₗ i, α i) where
  le := Lex (· < ·) fun _ => (· ≤ ·)

/-- The lexicographical `<` on a sigma type. -/
/-
**Sigma.Lex.LT** 是 Mathlib 中的一个定义，位于命名空间 `Sigma.Lex`。
形式化陈述：{ι : Type u_1} → {α : ι → Type u_2} → [LT ι] → [(i : ι) → LT (α i)] → LT (
Σₗ (i : ι), α i)
参数：i : ι；α i；Σₗ (i : ι), α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical `<` on a sigma type.
-/
protected instance LT [LT ι] [∀ i, LT (α i)] : LT (Σₗ i, α i) where
  lt := Lex (· < ·) fun _ => (· < ·)
/-
**Sigma.Lex.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.Lex`。
形式化陈述：le_def [LT ι] [forall i, LE (α i)] {a b : Σₗ i, α i} : a <= b ↔ a.1 < b.1 
∨ exists h : a.1 = b.1, h.rec a.2 <= b.2
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.lex_iff`：lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1,
 s b.1 (h.rec a.2) b.2
-/
theorem le_def [LT ι] [∀ i, LE (α i)] {a b : Σₗ i, α i} :
    a ≤ b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
  Sigma.lex_iff
/-
**Sigma.Lex.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.Lex`。
形式化陈述：lt_def [LT ι] [forall i, LT (α i)] {a b : Σₗ i, α i} : a < b ↔ a.1 < b.1 ∨
 exists h : a.1 = b.1, h.rec a.2 < b.2
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.lex_iff`：lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1,
 s b.1 (h.rec a.2) b.2
-/
theorem lt_def [LT ι] [∀ i, LT (α i)] {a b : Σₗ i, α i} :
    a < b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
  Sigma.lex_iff

/-- The lexicographical preorder on a sigma type. -/
/-
**Sigma.Lex.preorder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：preorder [Preorder ι] [forall i, Preorder (α i)] : Preorder (Σₗ i, α i)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical preorder on a sigma type.
-/
instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ i, α i) :=
  { Sigma.Lex.LE, Sigma.Lex.LT with
    le_refl := fun ⟨_, a⟩ => Lex.right a a le_rfl,
    le_trans := fun _ _ _ => trans_of ((Lex (· < ·)) fun _ => (· ≤ ·)),
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨b, a, hji⟩ | ⟨b, a, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, _, hab⟩ := hab
        · exact hij.not_gt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_ge hba
      · rintro ⟨⟨a, b, hij⟩ | ⟨a, b, hab⟩, hba⟩
        · exact Sigma.Lex.left _ _ hij
        · exact Sigma.Lex.right _ _ (hab.lt_of_not_ge fun h => hba <| Sigma.Lex.right _ _ h) }

/-- The lexicographical partial order on a sigma type. -/
/-
**Sigma.Lex.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：partialOrder [Preorder ι] [forall i, PartialOrder (α i)] : PartialOrder (Σ
ₗ i, α i)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical partial order on a sigma type.
-/
instance partialOrder [Preorder ι] [∀ i, PartialOrder (α i)] :
    PartialOrder (Σₗ i, α i) :=
  { Lex.preorder with
    le_antisymm := fun _ _ => antisymm_of ((Lex (· < ·)) fun _ => (· ≤ ·)) }



/-- The lexicographical linear order on a sigma type. -/
/-
**Sigma.Lex.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：linearOrder [LinearOrder ι] [forall i, LinearOrder (α i)] : LinearOrder (Σ
ₗ i, α i)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical linear order on a sigma type.
-/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] :
    LinearOrder (Σₗ i, α i) :=
  { Lex.partialOrder with
    le_total := total_of ((Lex (· < ·)) fun _ => (· ≤ ·)),
    toDecidableEq := Sigma.instDecidableEqSigma
    toDecidableLE := Lex.decidable _ _
    toDecidableLT := Lex.decidable _ _ }

/-- The lexicographical linear order on a sigma type. -/
/-
**Sigma.Lex.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：orderBot [PartialOrder ι] [OrderBot ι] [forall i, Preorder (α i)] [OrderBo
t (α ⊥)] : OrderBot (Σₗ i, α i) where bot
参数：α i；α ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical linear order on a sigma type.
-/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ _ bot_le
    · exact Lex.left _ _ ha

/-- The lexicographical linear order on a sigma type. -/
/-
**Sigma.Lex.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：orderTop [PartialOrder ι] [OrderTop ι] [forall i, Preorder (α i)] [OrderTo
p (α ⊤)] : OrderTop (Σₗ i, α i) where top
参数：α i；α ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical linear order on a sigma type.
-/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ _ le_top
    · exact Lex.left _ _ ha

/-- The lexicographical linear order on a sigma type. -/
/-
**Sigma.Lex.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：boundedOrder [PartialOrder ι] [BoundedOrder ι] [forall i, Preorder (α i)] 
[OrderBot (α ⊥)] [OrderTop (α ⊤)] : BoundedOrder (Σₗ i, α i)
参数：α i；α ⊥；α ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical linear order on a sigma type.
-/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ i, α i) :=
  { Lex.orderBot, Lex.orderTop with }
/-
**Sigma.Lex.denselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：denselyOrdered [Preorder ι] [DenselyOrdered ι] [forall i, Nonempty (α i)] 
[forall i, Preorder (α i)] [forall i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ
 i, α i) where dense
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
/-
**Sigma.Lex.denselyOrdered_of_noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：denselyOrdered_of_noMaxOrder [Preorder ι] [forall i, Preorder (α i)] [fora
ll i, DenselyOrdered (α i)] [forall i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ i,
 α i) where dense
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance denselyOrdered_of_noMaxOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMaxOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
/-
**Sigma.Lex.denselyOrdered_of_noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：denselyOrdered_of_noMinOrder [Preorder ι] [forall i, Preorder (α i)] [fora
ll i, DenselyOrdered (α i)] [forall i, NoMinOrder (α i)] : DenselyOrdered (Σₗ i,
 α i) where dense
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance denselyOrdered_of_noMinOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMinOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
/-
**Sigma.Lex.noMaxOrder_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：noMaxOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMaxOrder
 ι] [forall i, Nonempty (α i)] : NoMaxOrder (Σₗ i, α i) where exists_gt
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
instance noMaxOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩
/-
**Sigma.Lex.noMinOrder_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：noMinOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMinOrder
 ι] [forall i, Nonempty (α i)] : NoMinOrder (Σₗ i, α i) where exists_lt
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
instance noMinOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMinOrder ι]
    [∀ i, Nonempty (α i)] : NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩
/-
**Sigma.Lex.noMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：noMaxOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMaxOrder (
α i)] : NoMaxOrder (Σₗ i, α i) where exists_gt
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
instance noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ _ h⟩
/-
**Sigma.Lex.noMinOrder** 是 Mathlib 中的一个实例，位于命名空间 `Sigma.Lex`。
形式化陈述：noMinOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMinOrder (
α i)] : NoMinOrder (Σₗ i, α i) where exists_lt
参数：α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
instance noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ _ h⟩

end Lex

end Sigma

