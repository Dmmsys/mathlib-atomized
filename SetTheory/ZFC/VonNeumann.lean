/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.ZFC.Class

/-!
# Von Neumann hierarchy

This file defines the von Neumann hierarchy of sets `V_ o` for ordinal `o`, which is recursively
defined so that `V_ a = ⋃ b < a, powerset (V_ b)`. This stratifies the universal class, in the sense
that `⋃ o, V_ o = univ`.

## Notation

- `V_ o` is notation for `vonNeumann o`. It is scoped in the `ZFSet` namespace.
-/

@[expose] public section

universe u

open Order

namespace ZFSet

/-- The von Neumann hierarchy is defined so that `V_ o` is the union of the powersets of all
`V_ a` for `a < o`. It satisfies the following properties:

- `vonNeumann_zero`: `V_ 0 = ∅`
- `vonNeumann_add_one`: `V_ (a + 1) = powerset (V_ a)`
- `vonNeumann_of_isSuccPrelimit`: `IsSuccPrelimit a → V_ a = ⋃ b < a, V_ b`
-/
/-
**ZFSet.vonNeumann** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann (o : Ordinal.{u}) : ZFSet.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The von Neumann hierarchy is defined so that `V_ o` is the union of the powerset
s of all
`V_ a` for `a < o`. It satisfies the following properties:

- `vonNeumann_zero`: `V_ 0 = ∅`
- `vonNeumann_add_one`: `V_ (a + 1) = powerset (V_ a)`
- `vonNeumann_of_isSuccPrelimit`: `IsSuccPrelimit a → V_ a = ⋃ b < a, V_ b`
-/
noncomputable def vonNeumann (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃ a : Set.Iio o, powerset (vonNeumann a)
termination_by o
decreasing_by exact a.2

@[inherit_doc]
scoped notation "V_ " => vonNeumann

variable {a b o : Ordinal.{u}} {x : ZFSet.{u}}
/-
**ZFSet.mem_vonNeumann'** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：mem_vonNeumann' : x in V_ o ↔ exists a < o, x subseteq V_ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.vonNeumann.eq_1`：∀ (o : Ordinal.{u}), ZFSet.vonNeumann o = ZFSet.i
Union fun a => (ZFSet.vonNeumann ↑a).powerset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_vonNeumann' : x ∈ V_ o ↔ ∃ a < o, x ⊆ V_ a := by rw [vonNeumann]; simp
/-
**ZFSet.isTransitive_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o)
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.vonNeumann.eq_1`：∀ (o : Ordinal.{u}), ZFSet.vonNeumann o = ZFSet.i
Union fun a => (ZFSet.vonNeumann ↑a).powerset
· 使用定理 `ZFSet.IsTransitive.iUnion`：∀ {α : Type u_1} [inst : Small.{u, u_1} α] {f
 : α → ZFSet.{u}},   (∀ (i : α), (f i).IsTransitive) → (ZFSet.iUnion fun i => f 
i).IsTransitive
· 使用定理 `ZFSet.IsTransitive.powerset`：∀ {x : ZFSet.{u}}, x.IsTransitive → x.power
set.IsTransitive
-/
theorem isTransitive_vonNeumann (o : Ordinal) : IsTransitive (V_ o) := by
  rw [vonNeumann]
  exact .iUnion fun ⟨a, _⟩ => (isTransitive_vonNeumann a).powerset
termination_by o
/-
**ZFSet.vonNeumann_mem_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {a b : Ordinal.{u}}, a < b → ZFSet.vonNeumann a ∈ ZFSet.vonNeumann b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.vonNeumann.eq_1`：∀ (o : Ordinal.{u}), ZFSet.vonNeumann o = ZFSet.i
Union fun a => (ZFSet.vonNeumann ↑a).powerset
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[gcongr] theorem vonNeumann_mem_of_lt (h : a < b) : V_ a ∈ V_ b := by
  rw [vonNeumann]; aesop
/-
**ZFSet.vonNeumann_subset_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {a b : Ordinal.{u}}, a ≤ b → ZFSet.vonNeumann a ⊆ ZFSet.vonNeumann b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.instReflLe`：Std.Refl fun x1 x2 => x1 ⊆ x2
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ZFSet.isTransitive_vonNeumann`：isTransitive_vonNeumann (o : Ordinal) : I
sTransitive (V_ o)
· 使用定理 `ZFSet.vonNeumann_mem_of_lt`：∀ {a b : Ordinal.{u}}, a < b → ZFSet.vonNeum
ann a ∈ ZFSet.vonNeumann b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
-/
@[gcongr] theorem vonNeumann_subset_of_le (h : a ≤ b) : V_ a ⊆ V_ b :=
  h.eq_or_lt.rec (by simp_all) fun h ↦ isTransitive_vonNeumann _ _ <| vonNeumann_mem_of_lt h
/-
**ZFSet.subset_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：subset_vonNeumann {o : Ordinal} {x : ZFSet} : x subseteq V_ o ↔ rank x <= 
o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.subset_vonNeumann._unary`：∀ (_x : (_ : Ordinal.{u_1}) ×' ZFSet.{u_
1}), _x.2 ⊆ ZFSet.vonNeumann _x.1 ↔ _x.2.rank ≤ _x.1
-/
theorem subset_vonNeumann {o : Ordinal} {x : ZFSet} : x ⊆ V_ o ↔ rank x ≤ o := by
  rw [rank_le_iff]
  constructor <;> intro hx y hy
  · apply (rank_lt_of_mem (hx hy)).trans_le
    simp_rw [rank_le_iff, mem_vonNeumann']
    rintro z ⟨a, ha, hz⟩
    exact (subset_vonNeumann.1 hz).trans_lt ha
  · rw [mem_vonNeumann']
    have := hx hy
    exact ⟨_, this, subset_vonNeumann.2 le_rfl⟩
termination_by o
/-
**ZFSet.subset_vonNeumann_self** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：subset_vonNeumann_self (x : ZFSet) : x subseteq V_ (rank x)
参数：x : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem subset_vonNeumann_self (x : ZFSet) : x ⊆ V_ (rank x) := by
  simp [subset_vonNeumann]
/-
**ZFSet.mem_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_vonNeumann : x in V_ o ↔ rank x < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mem_vonNeumann : x ∈ V_ o ↔ rank x < o := by
  simp_rw [mem_vonNeumann', subset_vonNeumann]
  exact ⟨fun ⟨a, h₁, h₂⟩ ↦ h₂.trans_lt h₁, by aesop⟩
/-
**ZFSet.mem_vonNeumann_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_vonNeumann_succ (x : ZFSet) : x in V_ (succ (rank x))
参数：x : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_vonNeumann_succ (x : ZFSet) : x ∈ V_ (succ (rank x)) := by
  simp [mem_vonNeumann]

/-- Every set is in some element of the von Neumann hierarchy. -/
/-
**ZFSet.exists_mem_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：exists_mem_vonNeumann (x : ZFSet) : exists o, x in V_ o
参数：x : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_vonNeumann_succ`：mem_vonNeumann_succ (x : ZFSet) : x in V_ (su
cc (rank x))

--- 原说明 ---
Every set is in some element of the von Neumann hierarchy.
-/
theorem exists_mem_vonNeumann (x : ZFSet) : ∃ o, x ∈ V_ o :=
  ⟨_, mem_vonNeumann_succ x⟩

@[simp]
/-
**ZFSet.rank_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：rank_vonNeumann (o : Ordinal) : rank (V_ o) = o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.subset_vonNeumann`：subset_vonNeumann {o : Ordinal} {x : ZFSet} : x
 subseteq V_ o ↔ rank x <= o
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
· 使用定理 `ZFSet.vonNeumann_mem_of_lt`：∀ {a b : Ordinal.{u}}, a < b → ZFSet.vonNeum
ann a ∈ ZFSet.vonNeumann b
-/
theorem rank_vonNeumann (o : Ordinal) : rank (V_ o) = o :=
  le_antisymm (by rw [← subset_vonNeumann]) <| le_of_forall_lt fun a ha ↦
    rank_vonNeumann a ▸ rank_lt_of_mem (vonNeumann_mem_of_lt ha)
termination_by o

@[simp]
/-
**ZFSet.vonNeumann_mem_vonNeumann_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_mem_vonNeumann_iff : V_ a in V_ b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.rank_vonNeumann`：rank_vonNeumann (o : Ordinal) : rank (V_ o) = o
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem vonNeumann_mem_vonNeumann_iff : V_ a ∈ V_ b ↔ a < b := by
  simp [mem_vonNeumann]

@[simp]
/-
**ZFSet.vonNeumann_subset_vonNeumann_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_subset_vonNeumann_iff : V_ a subseteq V_ b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.rank_vonNeumann`：rank_vonNeumann (o : Ordinal) : rank (V_ o) = o
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem vonNeumann_subset_vonNeumann_iff : V_ a ⊆ V_ b ↔ a ≤ b := by
  simp [subset_vonNeumann]
/-
**ZFSet.mem_vonNeumann_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_vonNeumann_of_subset {y : ZFSet} (h : x subseteq y) (hy : y in V_ o) :
 x in V_ o
参数：h : x subseteq y；hy : y in V_ o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_vonNeumann`：mem_vonNeumann : x in V_ o ↔ rank x < o
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ZFSet.rank_mono`：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
-/
theorem mem_vonNeumann_of_subset {y : ZFSet} (h : x ⊆ y) (hy : y ∈ V_ o) : x ∈ V_ o := by
  rw [mem_vonNeumann] at *
  exact (rank_mono h).trans_lt hy
/-
**ZFSet.vonNeumann_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_strictMono : StrictMono vonNeumann
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem vonNeumann_strictMono : StrictMono vonNeumann :=
  strictMono_of_le_iff_le (by simp)
/-
**ZFSet.vonNeumann_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_injective : Function.Injective vonNeumann
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ZFSet.vonNeumann_strictMono`：vonNeumann_strictMono : StrictMono vonNeuma
nn
-/
theorem vonNeumann_injective : Function.Injective vonNeumann :=
  vonNeumann_strictMono.injective

@[simp]
/-
**ZFSet.vonNeumann_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_inj : V_ a = V_ b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ZFSet.vonNeumann_injective`：vonNeumann_injective : Function.Injective vo
nNeumann
-/
theorem vonNeumann_inj : V_ a = V_ b ↔ a = b :=
  vonNeumann_injective.eq_iff

@[simp]
/-
**ZFSet.vonNeumann_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_zero : V_ 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.eq_empty`：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u},
 y ∉ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem vonNeumann_zero : V_ 0 = ∅ :=
  (eq_empty _).2 (by simp [mem_vonNeumann])

@[simp]
/-
**ZFSet.vonNeumann_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_add_one (o : Ordinal) : V_ (o + 1) = powerset (V_ o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_vonNeumann`：mem_vonNeumann : x in V_ o ↔ rank x < o
· 使用定理 `ZFSet.mem_powerset`：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y
 subseteq x
· 使用定理 `ZFSet.subset_vonNeumann`：subset_vonNeumann {o : Ordinal} {x : ZFSet} : x
 subseteq V_ o ↔ rank x <= o
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vonNeumann_add_one (o : Ordinal) : V_ (o + 1) = powerset (V_ o) :=
  ext fun z ↦ by rw [mem_vonNeumann, mem_powerset, subset_vonNeumann, lt_add_one_iff]

@[deprecated vonNeumann_add_one (since := "2026-05-25")]
/-
**ZFSet.vonNeumann_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_succ (o : Ordinal) : V_ (succ o) = powerset (V_ o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.vonNeumann_add_one`：vonNeumann_add_one (o : Ordinal) : V_ (o + 1) 
= powerset (V_ o)
-/
theorem vonNeumann_succ (o : Ordinal) : V_ (succ o) = powerset (V_ o) :=
  vonNeumann_add_one o
/-
**ZFSet.vonNeumann_of_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：vonNeumann_of_isSuccPrelimit (h : IsSuccPrelimit o) : V_ o = ⋃ a : Set.Iio
 o, vonNeumann a
参数：h : IsSuccPrelimit o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Order.IsSuccPrelimit.lt_iff_exists_lt`：∀ {α : Type u_1} {a b : α} [inst 
: LinearOrder α], Order.IsSuccPrelimit b → (a < b ↔ ∃ c < b, a < c)
-/
theorem vonNeumann_of_isSuccPrelimit (h : IsSuccPrelimit o) :
    V_ o = ⋃ a : Set.Iio o, vonNeumann a :=
  ext fun z ↦ by simpa [mem_vonNeumann] using h.lt_iff_exists_lt
/-
**ZFSet.iUnion_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.eq_univ_of_forall`：eq_univ_of_forall {A : Class.{u}} : (forall x :
 ZFSet, A x) -> A = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `ZFSet.exists_mem_vonNeumann`：exists_mem_vonNeumann (x : ZFSet) : exists 
o, x in V_ o
-/
theorem iUnion_vonNeumann : ⋃ o, (V_ o : Class) = Class.univ :=
  Class.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 <| exists_mem_vonNeumann x
/-
**ZFSet._root_.Ordinal.toZFSet_subset_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSe
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.toZFSet_subset_vonNeumann (o : Ordinal) : o.toZFSet ⊆ V_ o := by
  simp [subset_vonNeumann]
/-
**ZFSet._root_.Ordinal.card_le_card_vonNeumann** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Ordinal.card_le_card_vonNeumann (o : Ordinal) : o.card ≤ card (V_ o) := by
  simpa using card_mono o.toZFSet_subset_vonNeumann

open Cardinal in
/-
**ZFSet.card_vonNeumann** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：card_vonNeumann (o : Ordinal.{u}) : card (V_ o) = preBeth o
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.vonNeumann_zero`：vonNeumann_zero : V_ 0 = ∅
· 使用定理 `ZFSet.card_empty`：card_empty : card ∅ = 0
· 使用定理 `Cardinal.preBeth_zero`：preBeth_zero : preBeth 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZFSet.vonNeumann_add_one`：vonNeumann_add_one (o : Ordinal) : V_ (o + 1) 
= powerset (V_ o)
· 使用定理 `ZFSet.card_powerset`：card_powerset (x : ZFSet.{u}) : card (powerset x) =
 2 ^ card x
· 使用定理 `Cardinal.preBeth_add_one`：preBeth_add_one (o : Ordinal) : preBeth (o + 1
) = 2 ^ preBeth o
· 使用定理 `Cardinal.preBeth_limit`：preBeth_limit {o : Ordinal} (ho : IsSuccPrelimit
 o) : preBeth o = ⨆ a : Iio o, preBeth a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZFSet.vonNeumann_of_isSuccPrelimit`：vonNeumann_of_isSuccPrelimit (h : Is
SuccPrelimit o) : V_ o = ⋃ a : Set.Iio o, vonNeumann a
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `ZFSet.iSup_card_le_card_iUnion`：iSup_card_le_card_iUnion {α} [Small.{v, 
u} α] {f : α -> ZFSet.{v}} : ⨆ i, card (f i) <= card (⋃ i, f i)
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ZFSet.lift_card_iUnion_le_sum_card`：lift_card_iUnion_le_sum_card {α} [Sm
all.{v, u} α] {f : α -> ZFSet.{v}} : lift (card (⋃ i, f i)) <= sum fun i => card
 (f i)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.sum_eq_lift_iSup_of_lift_mk_le_lift_iSup`：sum_eq_lift_iSup_of_l
ift_mk_le_lift_iSup [Small.{v} ι] {f : ι -> Cardinal.{v}} (hι : ℵ₀ <= #ι) (h : l
ift.{v} #ι <= lift.{u} (⨆ i, f i)) : su…
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Ordinal.aleph0_le_card`：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
（共 45 条，此处仅展示前 30 条）
-/
theorem card_vonNeumann (o : Ordinal.{u}) : card (V_ o) = preBeth o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp
  | add_one o ih => simp [ih]
  | limit o ho ih =>
    simp_rw [preBeth_limit ho.isSuccPrelimit, ← fun i : Set.Iio o => ih i i.2,
      vonNeumann_of_isSuccPrelimit ho.isSuccPrelimit]
    apply iSup_card_le_card_iUnion.antisymm'
    rw [← lift_le.{u + 1}]
    apply lift_card_iUnion_le_sum_card.trans
    refine (sum_eq_lift_iSup_of_lift_mk_le_lift_iSup ?_ ?_).le
    · rw [mk_Iio_ordinal, ← lift_aleph0.{u + 1, u}, lift_le, Ordinal.aleph0_le_card]
      exact Ordinal.omega0_le_of_isSuccLimit ho
    · rw [mk_Iio_ordinal, lift_lift, lift_le]
      by_contra! h
      refine (⨆ i : Set.Iio o, (V_ ↑i).card).card_ord.not_lt <|
        (Ordinal.card_le_card_vonNeumann _).trans_lt <| (cantor _).trans_le ?_
      rw [← card_powerset, ← vonNeumann_add_one]
      refine le_ciSup bddAbove_of_small (⟨_, ho.succ_lt ?_⟩ : Set.Iio o)
      exact (ord_card_le _).trans_lt' (ord_strictMono h)

end ZFSet

