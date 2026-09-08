/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.WithBot

/-!
# Pivots of a matrix

`Matrix.IsPivotedBy A l` defines a map-based representation `l` for the pivot, stating that
`l i` is the pivot column of each row `i` of `A`, with `⊤` for a zero row.

## Main definitions

- `Matrix.IsPivotedBy`: `l i : WithTop n` is the pivot column of each row `i` of `A`.

## Main results

- `Matrix.IsPivotedBy.rank_eq`: the rank of a matrix is its number of pivots.
- `Matrix.IsPivotedBy.unique`: the pivot of a matrix is unique if the column indices have a
  linear order.
- `Matrix.isPivotedBy_iff`: the map-structural characterisation of pivots.

## Tags

matrix, echelon form, pivot
-/

@[expose] public section

namespace Matrix

open Finset

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-- `A` is in row echelon form and `l i` is the leading position of each row `i`,
with `⊤` for a zero row. -/
/-
**Matrix.IsPivotedBy** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_1} → {n : Type u_2} → {R : Type u_3} → [Zero R] → [LT m] → [LT
 n] → Matrix m n R → (m → WithTop n) → Prop
参数：m → WithTop n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A` is in row echelon form and `l i` is the leading position of each row `i`,
with `⊤` for a zero row.
-/
structure IsPivotedBy [LT m] [LT n] (A : Matrix m n R) (l : m → WithTop n) : Prop where
  isRowEchelon : A.IsRowEchelon
  isPivotEntry (i : m) :
    (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0

namespace IsPivotedBy

/-
**Matrix.IsPivotedBy.isLeadingEntry** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedB
y`。
形式化陈述：isLeadingEntry [LT m] [LT n] {i : m} {c : n} (hA : A.IsPivotedBy l) (hc : 
l i = c) : A.IsLeadingEntry i c
参数：hA : A.IsPivotedBy l；hc : l i = c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.IsPivotedBy.isPivotEntry`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isLeadingEntry [LT m] [LT n] {i : m} {c : n} (hA : A.IsPivotedBy l) (hc : l i = c) :
    A.IsLeadingEntry i c := by
  refine ⟨fun j hj => (hA.isPivotEntry i).1 j ?_, (hA.isPivotEntry i).2 c hc⟩
  rw [hc]
  exact_mod_cast hj
/-
**Matrix.IsPivotedBy.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedBy`。
形式化陈述：eq_top_iff [LT m] [LT n] {i : m} (hA : A.IsPivotedBy l) : l i = ⊤ ↔ A i = 
0
参数：hA : A.IsPivotedBy l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.IsPivotedBy.isPivotEntry`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem eq_top_iff [LT m] [LT n] {i : m} (hA : A.IsPivotedBy l) :
    l i = ⊤ ↔ A i = 0 := by
  cases hc : l i with
  | top =>
    have h := (hA.isPivotEntry i).1
    rw [hc] at h
    simpa [funext_iff] using fun j => h j (WithTop.coe_lt_top j)
  | coe c => simpa using fun h0 => (hA.isPivotEntry i).2 c hc (congrFun h0 c)

variable [LinearOrder n]
/-
**Matrix.IsPivotedBy.lt_of_lt_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivo
tedBy`。
形式化陈述：lt_of_lt_of_ne_top [LT m] {i₁ i₂ : m} (hA : A.IsPivotedBy l) (hlt : i₁ < i
₂) (h₁ : l i₁ != ⊤) : l i₁ < l i₂
参数：hA : A.IsPivotedBy l；hlt : i₁ < i₂；h₁ : l i₁ != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.IsPivotedBy.isPivotEntry`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsPivotedBy.isRowEchelon`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem lt_of_lt_of_ne_top [LT m] {i₁ i₂ : m}
    (hA : A.IsPivotedBy l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  by_contra! hle
  obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp (hle.trans_lt h₁.lt_top).ne
  refine (hA.isPivotEntry i₂).2 c₂ hc₂.symm (hA.isRowEchelon hlt fun j₁ hj₁ => ?_)
  exact (hA.isPivotEntry i₁).1 j₁ ((WithTop.coe_lt_coe.mpr hj₁).trans_le (hc₂.le.trans hle))

/-- The pivots of a matrix are unique. -/
/-
**Matrix.IsPivotedBy.unique** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedBy`。
形式化陈述：unique [LT m] {l' : m -> WithTop n} (hl : A.IsPivotedBy l) (hl' : A.IsPivo
tedBy l') : l = l'
参数：hl : A.IsPivotedBy l；hl' : A.IsPivotedBy l'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsPivotedBy.eq_top_iff`：eq_top_iff [LT m] [LT n] {i : m} (hA : A.
IsPivotedBy l) : l i = ⊤ ↔ A i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.IsPivotedBy.isLeadingEntry`：isLeadingEntry [LT m] [LT n] {i : m} 
{c : n} (hA : A.IsPivotedBy l) (hc : l i = c) : A.IsLeadingEntry i c
· 使用定理 `Matrix.IsLeadingEntry.unique`：∀ {m : Type u_1} {n : Type u_2} {R : Type 
v} {A : Matrix m n R} [inst : Zero R] [inst_1 : LinearOrder n] {i : m}   {c₁ c₂ 
: n}, A.IsLeadingE…

--- 原说明 ---
The pivots of a matrix are unique.
-/
theorem unique [LT m] {l' : m → WithTop n}
    (hl : A.IsPivotedBy l) (hl' : A.IsPivotedBy l') : l = l' := by
  funext i
  cases hc' : l' i with
  | top =>
    rw [hl.eq_top_iff, ← hl'.eq_top_iff]
    exact hc'
  | coe c' =>
    cases hc : l i with
    | top =>
      rw [hl.eq_top_iff] at hc
      exact absurd (congrFun hc c') (hl'.isLeadingEntry hc').2
    | coe c => exact_mod_cast (hl.isLeadingEntry hc).unique (hl'.isLeadingEntry hc')
/-
**Matrix.IsPivotedBy.strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedBy`
。
形式化陈述：strictMonoOn [Preorder m] (hA : A.IsPivotedBy l) : StrictMonoOn l {i | l i
 != ⊤}
参数：hA : A.IsPivotedBy l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsPivotedBy.lt_of_lt_of_ne_top`：lt_of_lt_of_ne_top [LT m] {i₁ i₂ 
: m} (hA : A.IsPivotedBy l) (hlt : i₁ < i₂) (h₁ : l i₁ != ⊤) : l i₁ < l i₂
-/
theorem strictMonoOn [Preorder m] (hA : A.IsPivotedBy l) :
    StrictMonoOn l {i | l i ≠ ⊤} :=
  fun _ h₁ _ _ hlt => hA.lt_of_lt_of_ne_top hlt h₁

variable [PartialOrder m]
/-
**Matrix.IsPivotedBy.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedBy`。
形式化陈述：monotone (hA : A.IsPivotedBy l) : Monotone l
参数：hA : A.IsPivotedBy l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsPivotedBy.eq_top_iff`：eq_top_iff [LT m] [LT n] {i : m} (hA : A.
IsPivotedBy l) : l i = ⊤ ↔ A i = 0
· 使用定理 `Matrix.IsRowEchelon.row_eq_zero_of_lt`：∀ {m : Type u_1} {n : Type u_2} {
R : Type v} {A : Matrix m n R} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n]  
 {i₁ i₂ : m}, A.IsRowEchelo…
· 使用定理 `Matrix.IsPivotedBy.isRowEchelon`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Matrix.IsPivotedBy.lt_of_lt_of_ne_top`：lt_of_lt_of_ne_top [LT m] {i₁ i₂ 
: m} (hA : A.IsPivotedBy l) (hlt : i₁ < i₂) (h₁ : l i₁ != ⊤) : l i₁ < l i₂
-/
theorem monotone (hA : A.IsPivotedBy l) :
    Monotone l := by
  refine monotone_iff_forall_lt.mpr ?_
  intro i₁ i₂ hlt
  by_cases h₁ : l i₁ = ⊤
  · simp [hA.eq_top_iff.mpr (hA.isRowEchelon.row_eq_zero_of_lt hlt (hA.eq_top_iff.mp h₁))]
  · exact (hA.lt_of_lt_of_ne_top hlt h₁).le

end IsPivotedBy

/-- The map-structural characterisation of pivots. This is useful for proving that
a matrix is in row echelon form. -/
/-
**Matrix.isPivotedBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isPivotedBy_iff [PartialOrder m] [LinearOrder n] : A.IsPivotedBy l ↔ Monot
one l ∧ StrictMonoOn l {i | l i != ⊤} ∧ forall i : m, (forall j : n, (j : WithTo
p n) < l i -> A i j = 0) ∧ forall c : n, l i = c -> A i c != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsPivotedBy.monotone`：monotone (hA : A.IsPivotedBy l) : Monotone 
l
· 使用定理 `Matrix.IsPivotedBy.strictMonoOn`：strictMonoOn [Preorder m] (hA : A.IsPiv
otedBy l) : StrictMonoOn l {i | l i != ⊤}
· 使用定理 `Matrix.IsPivotedBy.isPivotEntry`：∀ {m : Type u_1} {n : Type u_2} {R : Ty
pe u_3} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] {A : Matrix m n R}   {l 
: m → WithTop n}, A.I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c

--- 原说明 ---
The map-structural characterisation of pivots. This is useful for proving that
a matrix is in row echelon form.
-/
theorem isPivotedBy_iff [PartialOrder m] [LinearOrder n] :
    A.IsPivotedBy l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m,
        (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0 := by
  refine ⟨fun hA => ⟨hA.monotone, hA.strictMonoOn, hA.isPivotEntry⟩, ?_⟩
  refine fun ⟨hmono, hstrict, hlead⟩ ↦ ⟨fun i₁ i₂ hlt j₂ hz ↦ (hlead i₂).1 j₂ ?_, hlead⟩
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · rw [h₂]
    exact WithTop.coe_lt_top j₂
  · have h₁ : l i₁ ≠ ⊤ := fun ht => h₂ (top_le_iff.mp (ht.symm.le.trans (hmono hlt.le)))
    obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
    have hj : (j₂ : WithTop n) ≤ c₁ :=
      WithTop.coe_le_coe.mpr <| le_of_not_gt fun hgt => (hlead i₁).2 c₁ hc₁.symm (hz c₁ hgt)
    exact lt_of_le_of_lt (hj.trans hc₁.le) (hstrict h₁ h₂ hlt)

/-- A variant of `isPivotedBy_iff` phrased with `Matrix.IsLeadingEntry`. -/
/-
**Matrix.isPivotedBy_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isPivotedBy_iff' [PartialOrder m] [LinearOrder n] : A.IsPivotedBy l ↔ Mono
tone l ∧ StrictMonoOn l {i | l i != ⊤} ∧ forall i : m, (l i = ⊤ ∧ A i = 0) ∨ (ex
ists c : n, l i = c ∧ A.IsLeadingEntry i c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isPivotedBy_iff`：isPivotedBy_iff [PartialOrder m] [LinearOrder n]
 : A.IsPivotedBy l ↔ Monotone l ∧ StrictMonoOn l {i | l i != ⊤} ∧ forall i : m, 
(forall j : …
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
A variant of `isPivotedBy_iff` phrased with `Matrix.IsLeadingEntry`.
-/
theorem isPivotedBy_iff' [PartialOrder m] [LinearOrder n] :
    A.IsPivotedBy l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧
        ∀ i : m, (l i = ⊤ ∧ A i = 0) ∨ (∃ c : n, l i = c ∧ A.IsLeadingEntry i c) := by
  rw [isPivotedBy_iff]
  refine and_congr_right' <| and_congr_right' <| forall_congr' fun i => ?_
  cases l i <;> simp [IsLeadingEntry, funext_iff]

end Zero

section Rank

variable [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]
  {A : Matrix m n R} {l : m → WithTop n}

namespace IsPivotedBy

/-
**Matrix.IsPivotedBy.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPivotedBy`。
形式化陈述：rank_eq (hA : A.IsPivotedBy l) : A.rank = #{i | l i != ⊤}
参数：hA : A.IsPivotedBy l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Matrix.rank_le_card_of_support_subset`：rank_le_card_of_support_subset [C
ommSemiring R] [StrongRankCondition R] (A : Matrix m n R) (s : Finset m) (hz : F
unction.support A.row subse…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.IsPivotedBy.eq_top_iff`：eq_top_iff [LT m] [LT n] {i : m} (hA : A.
IsPivotedBy l) : l i = ⊤ ↔ A i = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Matrix.IsPivotedBy.isLeadingEntry`：isLeadingEntry [LT m] [LT n] {i : m} 
{c : n} (hA : A.IsPivotedBy l) (hc : l i = c) : A.IsLeadingEntry i c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `WithTop.untop_lt_untop_iff`：∀ {α : Type u_1} [inst : LT α] {x y : WithTo
p α} (hy : y ≠ ⊤) (hx : x ≠ ⊤), y.untop hy < x.untop hx ↔ y < x
· 使用定理 `Matrix.IsPivotedBy.strictMonoOn`：strictMonoOn [Preorder m] (hA : A.IsPiv
otedBy l) : StrictMonoOn l {i | l i != ⊤}
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.rank_of_det_ne_zero`：rank_of_det_ne_zero {R : Type*} [CommRing R]
 [IsDomain R] [Fintype m] [DecidableEq m] {A : Matrix m m R} (h : A.det != 0) : 
A.rank = Fintype…
（共 32 条，此处仅展示前 30 条）
-/
theorem rank_eq (hA : A.IsPivotedBy l) : A.rank = #{i | l i ≠ ⊤} := by
  refine le_antisymm (A.rank_le_card_of_support_subset _
    (Function.support_subset_iff'.mpr fun i hi => hA.eq_top_iff.mp (by aesop))) ?_
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i : {i // l i ≠ ⊤}, A.IsLeadingEntry i.1 (g i) := fun i =>
    hA.isLeadingEntry (WithTop.coe_untop (l i.1) i.2).symm
  have htri : (A.submatrix Subtype.val g).IsUpperTriangular := by
    intro i j hij
    exact (hlead i).1 _ ((WithTop.untop_lt_untop_iff _ _).mpr (hA.strictMonoOn j.2 i.2 hij))
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_isUpperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc #{i | l i ≠ ⊤}
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

end IsPivotedBy

end Rank

/-! ## Decidability -/

section Decidability

variable [Zero R] [DecidableEq R]

/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (l : m → WithTop n) : Decidable (A.IsPivotedBy l) :=
  -- instance resolution cannot nest `Fintype.decidableForallFintype` under another binder
  have : DecidablePred fun i : m =>
      (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0 :=
    fun _ => inferInstance
  decidable_of_iff' _ isPivotedBy_iff

end Decidability

end Matrix

