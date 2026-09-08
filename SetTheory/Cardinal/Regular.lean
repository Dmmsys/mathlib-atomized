/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios, Nir Paz
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Ordinal.FixedPoint

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.FundamentalSequence

/-!
# Regular cardinals

This file defines regular, singular, and inaccessible cardinals.

## Main definitions

* `Cardinal.IsRegular c` means that `c` is an infinite cardinal, equal to its own cofinality.
* `Cardinal.IsSingular c` means that `c` is an infinite cardinal which is not regular. That is,
  its cofinality is smaller than itself.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.
-/

@[expose] public section

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal
variable {c : Cardinal}

/-! ### Regular cardinals -/

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
@[mk_iff]
/-
**Cardinal.IsRegular** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cardinal`。
形式化陈述：Cardinal.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cardinal is regular if it is infinite and it equals its own cofinality.
-/
structure IsRegular (c : Cardinal) : Prop where
  /-- A regular cardinal is infinite. -/
  aleph0_le : ℵ₀ ≤ c
  /-- A cardinal equals its own cofinality. See `IsRegular.cof_eq`. -/
  le_cof_ord : c ≤ c.ord.cof
/-
**Cardinal.IsRegular.cof_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.cof = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.cof_ord_le`：cof_ord_le (c : Cardinal) : c.ord.cof <= c
· 使用定理 `Cardinal.IsRegular.le_cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c ≤
 c.ord.cof
-/
theorem IsRegular.cof_ord (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2

@[deprecated (since := "2026-03-22")] alias IsRegular.cof_eq := IsRegular.cof_ord
/-
**Cardinal.IsRegular.cof_omega_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`
。
形式化陈述：∀ {o : Ordinal.{u_1}}, (Cardinal.aleph o).IsRegular → (Ordinal.omega o).co
f = Cardinal.aleph o
参数：Cardinal.aleph o；Ordinal.omega o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem IsRegular.cof_omega_eq {o : Ordinal} (H : (ℵ_ o).IsRegular) : (ω_ o).cof = ℵ_ o := by
  rw [← ord_aleph, H.cof_ord]
/-
**Cardinal.IsRegular.pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → 0 < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
-/
theorem IsRegular.pos (H : c.IsRegular) : 0 < c :=
  aleph0_pos.trans_le H.1
/-
**Cardinal.IsRegular.nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → ∀ (n : ℕ), ↑n < c
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
-/
theorem IsRegular.nat_lt (H : c.IsRegular) (n : ℕ) : n < c :=
  lt_of_lt_of_le natCast_lt_aleph0 H.aleph0_le
/-
**Cardinal.IsRegular.ord_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → 0 < c.ord
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Ordinal.card_zero`：card_zero : card 0 = 0
· 使用定理 `Cardinal.IsRegular.pos`：∀ {c : Cardinal.{u_1}}, c.IsRegular → 0 < c
-/
theorem IsRegular.ord_pos (H : c.IsRegular) : 0 < c.ord := by
  rw [Cardinal.lt_ord, card_zero]
  exact H.pos
/-
**Cardinal.isRegular_cof** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_cof {o : Ordinal} (h : IsSuccLimit o) : IsRegular o.cof
参数：h : IsSuccLimit o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.aleph0_le_cof_iff`：aleph0_le_cof_iff {o : Ordinal} : ℵ₀ <= cof o
 ↔ 1 < cof o
· 使用定理 `Ordinal.one_lt_cof_iff`：one_lt_cof_iff {o : Ordinal} : 1 < cof o ↔ IsSuc
cLimit o
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ordinal.cof_ord_cof`：cof_ord_cof (o : Ordinal) : o.cof.ord.cof = o.cof
-/
theorem isRegular_cof {o : Ordinal} (h : IsSuccLimit o) : IsRegular o.cof := by
  refine ⟨?_, (cof_ord_cof o).ge⟩
  rwa [aleph0_le_cof_iff, one_lt_cof_iff]

/-- If `c` is a regular cardinal, then `c.ord.ToType` has a least element. -/
/-
**Cardinal.IsRegular.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → c ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.IsRegular.pos`：∀ {c : Cardinal.{u_1}}, c.IsRegular → 0 < c

--- 原说明 ---
If `c` is a regular cardinal, then `c.ord.ToType` has a least element.
-/
lemma IsRegular.ne_zero (H : c.IsRegular) : c ≠ 0 :=
  H.pos.ne'
/-
**Cardinal.isRegular_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_aleph0 : IsRegular ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `Ordinal.cof_omega0`：cof_omega0 : cof ω = ℵ₀
-/
theorem isRegular_aleph0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩
/-
**Cardinal.fact_isRegular_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：fact_isRegular_aleph0 : Fact (IsRegular ℵ₀) where out
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_aleph0`：isRegular_aleph0 : IsRegular ℵ₀
-/
lemma fact_isRegular_aleph0 : Fact (IsRegular ℵ₀) where
  out := isRegular_aleph0
/-
**Cardinal.isRegular_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : IsRegular (succ c)
参数：hc : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ordinal.exists_isFundamentalSeq`：exists_isFundamentalSeq (ha : o.cof.ord
 = a) : exists f : Iio a -> Iio o, IsFundamentalSeq f
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Ordinal.IsFundamentalSeq.iSup_add_one_eq`：iSup_add_one_eq (hf : IsFundam
entalSeq f) : ⨆ i, (f i).1 + 1 = o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.card_le_iff`：card_le_iff {o : Ordinal} {c : Cardinal} : o.card 
<= c ↔ o < (succ c).ord
· 使用定理 `Ordinal.card_iSup_Iio_le`：card_iSup_Iio_le {o : Ordinal} {c : Cardinal} 
{f : Iio o -> Ordinal} (hι : o.card <= c) (hf : forall i, (f i).card <= c) : (⨆ 
i, f i).card <…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Order.IsSuccLimit.add_one_lt`：∀ {α : Type u_1} {x y : α} [inst : Partial
Order α] [inst_1 : Add α] [inst_2 : One α] [SuccAddOrder α],   Order.IsSuccLimit
 x → y < x → y + 1…
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isRegular_succ {c : Cardinal} (hc : ℵ₀ ≤ c) : IsRegular (succ c) := by
  have hc₀ := hc.trans (le_succ c)
  use hc₀
  by_contra! hc'
  obtain ⟨f, hf⟩ := exists_isFundamentalSeq (o := (succ c).ord) rfl
  apply hf.iSup_add_one_eq.not_lt
  rw [← card_le_iff]
  refine card_iSup_Iio_le ?_ fun i ↦ ?_
  · simpa using hc'
  · rw [card_le_iff]
    exact (isSuccLimit_ord hc₀).add_one_lt (f i).2
/-
**Cardinal.isRegular_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_aleph_one : IsRegular ℵ₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph0`：succ_aleph0 : succ ℵ₀ = ℵ₁
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem isRegular_aleph_one : IsRegular ℵ₁ := by
  rw [← succ_aleph0]
  exact isRegular_succ le_rfl

@[simp]
/-
**Cardinal.cof_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cof_omega_one : cof ω₁ = ℵ₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.cof_omega_eq`：∀ {o : Ordinal.{u_1}}, (Cardinal.aleph 
o).IsRegular → (Ordinal.omega o).cof = Cardinal.aleph o
· 使用定理 `Cardinal.isRegular_aleph_one`：isRegular_aleph_one : IsRegular ℵ₁
-/
theorem cof_omega_one : cof ω₁ = ℵ₁ := by
  simpa using isRegular_aleph_one.cof_omega_eq

/-- A countable supremum of countable ordinals is countable. -/
/-
**Cardinal._root_.Ordinal.iSup_lt_omega_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A countable supremum of countable ordinals is countable.
-/
theorem _root_.Ordinal.iSup_lt_omega_one {α : Type*} [Countable α] {f : α → Ordinal} :
    (∀ i, f i < ω₁) → ⨆ i, f i < ω₁ :=
  Ordinal.lift_iSup_lt_of_lt_cof (by simp)

@[deprecated (since := "2026-03-23")]
alias iSup_sequence_lt_omega_one := Ordinal.iSup_lt_omega_one
/-
**Cardinal.isRegular_preAleph_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_preAleph_add_one {o : Ordinal} (h : ω <= o) : IsRegular (preAlep
h (o + 1))
参数：h : ω <= o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_preAleph`：succ_preAleph (o : Ordinal) : succ (preAleph o) 
= preAleph (o + 1)
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_preAleph`：aleph0_le_preAleph {o : Ordinal} : ℵ₀ <= pr
eAleph o ↔ ω <= o
-/
theorem isRegular_preAleph_add_one {o : Ordinal} (h : ω ≤ o) : IsRegular (preAleph (o + 1)) := by
  rw [← succ_preAleph]
  exact isRegular_succ (aleph0_le_preAleph.2 h)

@[deprecated isRegular_preAleph_add_one (since := "2026-03-23")]
/-
**Cardinal.isRegular_preAleph_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_preAleph_succ {o : Ordinal} (h : ω <= o) : IsRegular (preAleph (
succ o))
参数：h : ω <= o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_preAleph_add_one`：isRegular_preAleph_add_one {o : Ord
inal} (h : ω <= o) : IsRegular (preAleph (o + 1))
-/
theorem isRegular_preAleph_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (preAleph (succ o)) :=
  isRegular_preAleph_add_one h
/-
**Cardinal.cof_preOmega_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cof_preOmega_add_one {o : Ordinal} (h : ω <= o) : (preOmega (o + 1)).cof =
 preAleph (o + 1)
参数：h : ω <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_preAleph`：ord_preAleph (o : Ordinal) : (preAleph o).ord = p
reOmega o
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Cardinal.isRegular_preAleph_add_one`：isRegular_preAleph_add_one {o : Ord
inal} (h : ω <= o) : IsRegular (preAleph (o + 1))
-/
theorem cof_preOmega_add_one {o : Ordinal} (h : ω ≤ o) :
    (preOmega (o + 1)).cof = preAleph (o + 1) := by
  rw [← ord_preAleph, (isRegular_preAleph_add_one h).cof_ord]
/-
**Cardinal.isRegular_aleph_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_aleph_add_one (o : Ordinal) : IsRegular (ℵ_ (o + 1))
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.succ_aleph`：succ_aleph (o : Ordinal) : succ (ℵ_ o) = ℵ_ (o + 1)
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
-/
theorem isRegular_aleph_add_one (o : Ordinal) : IsRegular (ℵ_ (o + 1)) := by
  rw [← succ_aleph]
  exact isRegular_succ (aleph0_le_aleph o)

@[deprecated isRegular_aleph_add_one (since := "2026-03-23")]
/-
**Cardinal.isRegular_aleph_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o))
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_aleph_add_one`：isRegular_aleph_add_one (o : Ordinal) 
: IsRegular (ℵ_ (o + 1))
-/
theorem isRegular_aleph_succ (o : Ordinal) : IsRegular (ℵ_ (succ o)) :=
  isRegular_aleph_add_one o

@[simp]
/-
**Cardinal.cof_omega_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cof_omega_add_one (o : Ordinal) : (ω_ (o + 1)).cof = ℵ_ (o + 1)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.cof_omega_eq`：∀ {o : Ordinal.{u_1}}, (Cardinal.aleph 
o).IsRegular → (Ordinal.omega o).cof = Cardinal.aleph o
· 使用定理 `Cardinal.isRegular_aleph_add_one`：isRegular_aleph_add_one (o : Ordinal) 
: IsRegular (ℵ_ (o + 1))
-/
theorem cof_omega_add_one (o : Ordinal) : (ω_ (o + 1)).cof = ℵ_ (o + 1) :=
  (isRegular_aleph_add_one o).cof_omega_eq
/-
**Cardinal.IsRegular.lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegular`。
形式化陈述：∀ {κ : Cardinal.{v}}, κ.IsRegular → (Cardinal.lift.{u, v} κ).IsRegular
参数：Cardinal.lift.{u, v} κ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ord`：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lif
t.{u, v} c)
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
lemma IsRegular.lift {κ : Cardinal.{v}} (h : κ.IsRegular) :
    (Cardinal.lift.{u} κ).IsRegular := by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

@[simp]
/-
**Cardinal.isRegular_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_lift_iff {κ : Cardinal.{v}} : (Cardinal.lift.{u} κ).IsRegular ↔ 
κ.IsRegular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Cardinal.lift_ord`：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lif
t.{u, v} c)
· 使用定理 `Cardinal.IsRegular.lift`：∀ {κ : Cardinal.{v}}, κ.IsRegular → (Cardinal.l
ift.{u, v} κ).IsRegular
-/
lemma isRegular_lift_iff {κ : Cardinal.{v}} :
    (Cardinal.lift.{u} κ).IsRegular ↔ κ.IsRegular :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨by simpa using h₁, by simpa [← lift_le.{u, v}]⟩, fun h ↦ h.lift⟩

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.lsub_lt_ord_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lsub_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c
) (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c.ord) : Ordinal.lsub
.{u, v} f < c.ord
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} #ι < c；hf : forall i, f i < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_add_one_lt_of_lt_cof`：lift_iSup_add_one_lt_of_lt_cof {
f : β -> Ordinal.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a
).cof) (hf : forall i, f i <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem lsub_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c.ord) : Ordinal.lsub.{u, v} f < c.ord := by
  apply lift_iSup_add_one_lt_of_lt_cof _ hf
  rwa [lift_umax, c.ord.lift_id', hc.cof_ord]

@[deprecated iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.lsub_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lsub_lt_ord_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι
 : #ι < c) : (forall i, f i < c.ord) -> Ordinal.lsub f < c.ord
参数：hc : IsRegular c；hι : #ι < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_add_one_lt_of_lt_cof`：iSup_add_one_lt_of_lt_cof {f : α -> O
rdinal.{u}} {a : Ordinal.{u}} (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, 
f i + 1 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  iSup_add_one_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.iSup_lt_ord_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c
) (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c.ord) : iSup f < c.o
rd
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} #ι < c；hf : forall i, f i < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem iSup_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c.ord) : iSup f < c.ord := by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rwa [lift_umax, Ordinal.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.iSup_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_lt_ord_of_isRegular {ι} {f : ι -> Ordinal} {c} (hc : IsRegular c) (hι
 : #ι < c) : (forall i, f i < c.ord) -> iSup f < c.ord
参数：hc : IsRegular c；hι : #ι < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_lt_of_lt_cof`：iSup_lt_of_lt_cof {f : α -> Ordinal.{u}} {a :
 Ordinal.{u}} (ha : #α < a.cof) (hf : forall i, f i < a) : ⨆ i, f i < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem iSup_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c.ord) → iSup f < c.ord :=
  Ordinal.iSup_lt_of_lt_cof (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.blsub_lt_ord_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {
c} (hc : IsRegular c) (ho : Cardinal.lift.{v, u} o.card < c) : (forall i hi, f i
 hi < c.ord) -> Ordinal.blsub.{u, v} o f < c.ord
参数：hc : IsRegular c；ho : Cardinal.lift.{v, u} o.card < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_lt_ord_lift`：blsub_lt_ord_lift {o : Ordinal.{u}} {f : fora
ll a < o, Ordinal} {c : Ordinal} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf 
: forall i hi, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem blsub_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.blsub.{u, v} o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_add_one_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.blsub_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：blsub_lt_ord_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (h
c : IsRegular c) (ho : o.card < c) : (forall i hi, f i hi < c.ord) -> Ordinal.bl
sub o f < c.ord
参数：hc : IsRegular c；ho : o.card < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.blsub_lt_ord`：blsub_lt_ord {o : Ordinal} {f : forall a < o, Ordi
nal} {c : Ordinal} (ho : o.card < c.cof) (hf : forall i hi, f i hi < c) : blsub.
{u, u} o f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem blsub_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_ord])

@[deprecated iSup_lt_ord_lift_of_isRegular (since := "2026-03-22")]
/-
**Cardinal.bsup_lt_ord_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c
} (hc : IsRegular c) (hι : Cardinal.lift.{v, u} o.card < c) : (forall i hi, f i 
hi < c.ord) -> Ordinal.bsup.{u, v} o f < c.ord
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} o.card < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_lt_ord_lift`：bsup_lt_ord_lift {o : Ordinal} {f : forall a <
 o, Ordinal} {c : Ordinal} (ho : Cardinal.lift.{v, u} o.card < c.cof) (hf : fora
ll i hi, f i h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem bsup_lt_ord_lift_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} o.card < c) :
    (∀ i hi, f i hi < c.ord) → Ordinal.bsup.{u, v} o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.bsup_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bsup_lt_ord_of_isRegular {o : Ordinal} {f : forall a < o, Ordinal} {c} (hc
 : IsRegular c) (hι : o.card < c) : (forall i hi, f i hi < c.ord) -> Ordinal.bsu
p o f < c.ord
参数：hc : IsRegular c；hι : o.card < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.bsup_lt_ord`：bsup_lt_ord {o : Ordinal} {f : forall a < o, Ordina
l} {c : Ordinal} (ho : o.card < c.cof) : (forall i hi, f i hi < c) -> bsup.{u, u
} o f < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem bsup_lt_ord_of_isRegular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_ord])

@[deprecated lift_iSup_lt_of_lt_cof_ord (since := "2026-03-22")]
/-
**Cardinal.iSup_lt_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_lt_lift_of_isRegular {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c) (
hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c) : iSup f < c
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} #ι < c；hf : forall i, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_iSup_lt_of_lt_cof_ord`：∀ {β : Type v} {f : β → Cardinal.{u
}} {a : Cardinal.{u}},   Cardinal.lift.{u, v} (Cardinal.mk β) < (Cardinal.lift.{
v, u} a).ord.cof → (∀ (i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem iSup_lt_lift_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : iSup f < c := by
  apply lift_iSup_lt_of_lt_cof_ord _ hf
  rwa [lift_umax, c.lift_id', hc.cof_ord]

@[deprecated iSup_lt_of_lt_cof (since := "2026-03-22")]
/-
**Cardinal.iSup_lt_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：iSup_lt_of_isRegular {ι} {f : ι -> Cardinal} {c} (hc : IsRegular c) (hι : 
#ι < c) : (forall i, f i < c) -> iSup f < c
参数：hc : IsRegular c；hι : #ι < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.iSup_lt_of_lt_cof_ord`：∀ {α : Type u} {f : α → Cardinal.{u}} {a
 : Cardinal.{u}},   Cardinal.mk α < a.ord.cof → (∀ (i : α), f i < a) → ⨆ i, f i 
< a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem iSup_lt_of_isRegular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : #ι < c) :
    (∀ i, f i < c) → iSup f < c :=
  iSup_lt_of_lt_cof_ord (by rwa [hc.cof_ord])
/-
**Cardinal.sum_lt_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_lt_lift_of_isRegular {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular 
c) (hι : Cardinal.lift.{v, u} #ι < c) (hf : forall i, f i < c) : sum f < c
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} #ι < c；hf : forall i, f i < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup`：sum_le_lift_mk_mul_iSup {ι : Type u} (
f : ι -> Cardinal.{max u v}) : sum f <= lift #ι * ⨆ i, f i
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Cardinal.lift_iSup_lt_of_lt_cof_ord`：∀ {β : Type v} {f : β → Cardinal.{u
}} {a : Cardinal.{u}},   Cardinal.lift.{u, v} (Cardinal.mk β) < (Cardinal.lift.{
v, u} a).ord.cof → (∀ (i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
-/
theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι → Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hf : ∀ i, f i < c) : sum f < c := by
  apply (sum_le_lift_mk_mul_iSup _).trans_lt <|
    mul_lt_of_lt hc.1 hι (lift_iSup_lt_of_lt_cof_ord _ hf)
  rwa [lift_umax, c.lift_id', hc.cof_ord]
/-
**Cardinal.sum_lt_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_lt_of_isRegular {ι : Type u} {f : ι -> Cardinal} (hc : IsRegular c) (h
ι : #ι < c) : (forall i, f i < c) -> sum f < c
参数：hc : IsRegular c；hι : #ι < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.sum_lt_lift_of_isRegular`：sum_lt_lift_of_isRegular {ι : Type u}
 {f : ι -> Cardinal} (hc : IsRegular c) (hι : Cardinal.lift.{v, u} #ι < c) (hf :
 forall i, f i < c) : s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem sum_lt_of_isRegular {ι : Type u} {f : ι → Cardinal} (hc : IsRegular c)
    (hι : #ι < c) : (∀ i, f i < c) → sum f < c :=
  sum_lt_lift_of_isRegular.{u, u} hc (by rwa [lift_id])

@[simp]
/-
**Cardinal.card_lt_of_card_iUnion_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_lt_of_card_iUnion_lt {ι : Type u} {α : Type u} {t : ι -> Set α} {c : 
Cardinal} (h : #(⋃ i, t i) < c) (i : ι) : #(t i) < c
参数：h : #(⋃ i, t i) < c；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem card_lt_of_card_iUnion_lt {ι : Type u} {α : Type u} {t : ι → Set α} {c : Cardinal}
    (h : #(⋃ i, t i) < c) (i : ι) : #(t i) < c :=
  lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset <| subset_iUnion _ _) h

@[simp]
/-
**Cardinal.card_iUnion_lt_iff_forall_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Car
dinal`。
形式化陈述：card_iUnion_lt_iff_forall_of_isRegular {ι : Type u} {α : Type u} {t : ι ->
 Set α} (hc : c.IsRegular) (hι : #ι < c) : #(⋃ i, t i) < c ↔ forall i, #(t i) < 
c
参数：hc : c.IsRegular；hι : #ι < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.card_lt_of_card_iUnion_lt`：card_lt_of_card_iUnion_lt {ι : Type 
u} {α : Type u} {t : ι -> Set α} {c : Cardinal} (h : #(⋃ i, t i) < c) (i : ι) : 
#(t i) < c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_sUnion_le`：mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃
₀ A) <= #A * ⨆ s : A, #s
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `Cardinal.iSup_lt_of_lt_cof_ord`：∀ {α : Type u} {f : α → Cardinal.{u}} {a
 : Cardinal.{u}},   Cardinal.mk α < a.ord.cof → (∀ (i : α), f i < a) → ⨆ i, f i 
< a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
theorem card_iUnion_lt_iff_forall_of_isRegular {ι : Type u} {α : Type u} {t : ι → Set α}
    (hc : c.IsRegular) (hι : #ι < c) : #(⋃ i, t i) < c ↔ ∀ i, #(t i) < c := by
  refine ⟨card_lt_of_card_iUnion_lt, fun h ↦ ?_⟩
  apply lt_of_le_of_lt (Cardinal.mk_sUnion_le _)
  apply Cardinal.mul_lt_of_lt hc.aleph0_le (mk_range_le.trans_lt hι)
  apply Cardinal.iSup_lt_of_lt_cof_ord (mk_range_le.trans_lt _)
  · simpa
  · rwa [hc.cof_ord]
/-
**Cardinal.card_lt_of_card_biUnion_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_lt_of_card_biUnion_lt {α β : Type u} {s : Set α} {t : forall a in s, 
Set β} {c : Cardinal} (h : #(⋃ a in s, t a ‹_›) < c) (a : α) (ha : a in s) : #(t
 a ha) < c
参数：h : #(⋃ a in s, t a ‹_›) < c；a : α；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Cardinal.card_lt_of_card_iUnion_lt`：card_lt_of_card_iUnion_lt {ι : Type 
u} {α : Type u} {t : ι -> Set α} {c : Cardinal} (h : #(⋃ i, t i) < c) (i : ι) : 
#(t i) < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem card_lt_of_card_biUnion_lt {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β} {c : Cardinal}
    (h : #(⋃ a ∈ s, t a ‹_›) < c) (a : α) (ha : a ∈ s) : #(t a ha) < c := by
  rw [biUnion_eq_iUnion] at h
  have := card_lt_of_card_iUnion_lt h
  simp_all only [iUnion_coe_set, Subtype.forall]
/-
**Cardinal.card_biUnion_lt_iff_forall_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Ca
rdinal`。
形式化陈述：card_biUnion_lt_iff_forall_of_isRegular {α β : Type u} {s : Set α} {t : fo
rall a in s, Set β} (hc : c.IsRegular) (hs : #s < c) : #(⋃ a in s, t a ‹_›) < c 
↔ forall a (ha : a in s), #(t a ha) < c
参数：hc : c.IsRegular；hs : #s < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Cardinal.card_iUnion_lt_iff_forall_of_isRegular`：card_iUnion_lt_iff_fora
ll_of_isRegular {ι : Type u} {α : Type u} {t : ι -> Set α} (hc : c.IsRegular) (h
ι : #ι < c) : #(⋃ i, t i) < c ↔ foral…
· 使用定理 `SetCoe.forall'`：SetCoe.forall' {s : Set α} {p : forall x, x in s -> Prop
} : (forall (x) (h : x in s), p x h) ↔ forall x : s, p x.1 x.2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_biUnion_lt_iff_forall_of_isRegular {α β : Type u} {s : Set α} {t : ∀ a ∈ s, Set β}
    (hc : c.IsRegular) (hs : #s < c) :
    #(⋃ a ∈ s, t a ‹_›) < c ↔ ∀ a (ha : a ∈ s), #(t a ha) < c := by
  rw [biUnion_eq_iUnion, card_iUnion_lt_iff_forall_of_isRegular hc hs, SetCoe.forall']
/-
**Cardinal.nfpFamily_lt_ord_lift_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardina
l`。
形式化陈述：nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι -> Ordinal -> Ordinal} {c} (
hc : IsRegular c) (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c != ℵ₀) (hf : foral
l (i), forall b < c.ord, f i b < c.ord) {a} (ha : a < c.ord) : nfpFamily f a < c
.ord
参数：hc : IsRegular c；hι : Cardinal.lift.{v, u} #ι < c；hc' : c != ℵ₀；hf : forall (
i), forall b < c.ord, f i b < c.ord；ha : a < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_lt_ord_lift`：nfpFamily_lt_ord_lift {ι} {f : ι -> Ordin
al -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf
 : forall (i), fora…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem nfpFamily_lt_ord_lift_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily f a < c.ord := by
  apply nfpFamily_lt_ord_lift _ _ hf ha <;> rw [hc.cof_ord]
  · exact lt_of_le_of_ne hc.1 hc'.symm
  · exact hι
/-
**Cardinal.nfpFamily_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nfpFamily_lt_ord_of_isRegular {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : 
IsRegular c) (hι : #ι < c) (hc' : c != ℵ₀) {a} (hf : forall (i), forall b < c.or
d, f i b < c.ord) : a < c.ord -> nfpFamily.{u, u} f a < c.ord
参数：hc : IsRegular c；hι : #ι < c；hc' : c != ℵ₀；hf : forall (i), forall b < c.ord,
 f i b < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nfpFamily_lt_ord_lift_of_isRegular`：nfpFamily_lt_ord_lift_of_is
Regular {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c) (hι : Cardinal.
lift.{v, u} #ι < c) (hc' : c != ℵ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem nfpFamily_lt_ord_of_isRegular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) :
    a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfpFamily_lt_ord_lift_of_isRegular hc (by rwa [lift_id]) hc' hf
/-
**Cardinal.nfp_lt_ord_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nfp_lt_ord_of_isRegular {f : Ordinal -> Ordinal} {c} (hc : IsRegular c) (h
c' : c != ℵ₀) (hf : forall i < c.ord, f i < c.ord) {a} : a < c.ord -> nfp f a < 
c.ord
参数：hc : IsRegular c；hc' : c != ℵ₀；hf : forall i < c.ord, f i < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfp_lt_ord`：nfp_lt_ord {f : Ordinal -> Ordinal} {c} (hc : ℵ₀ < c
of c) (hf : forall i < c, f i < c) {a} : a < c -> nfp f a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem nfp_lt_ord_of_isRegular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord (by rw [hc.cof_ord]; exact lt_of_le_of_ne hc.1 hc'.symm) hf
/-
**Cardinal.derivFamily_lt_ord_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：derivFamily_lt_ord_lift {ι : Type u} {f : ι -> Ordinal -> Ordinal} {c} (hc
 : IsRegular c) (hι : lift.{v} #ι < c) (hc' : c != ℵ₀) (hf : forall i, forall b 
< c.ord, f i b < c.ord) {a} : a < c.ord -> derivFamily f a < c.ord
参数：hc : IsRegular c；hι : lift.{v} #ι < c；hc' : c != ℵ₀；hf : forall i, forall b <
 c.ord, f i b < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ordinal.derivFamily_zero`：derivFamily_zero (f : ι -> Ordinal -> Ordinal)
 : derivFamily f 0 = nfpFamily f 0
· 使用定理 `Ordinal.nfpFamily_lt_ord_lift`：nfpFamily_lt_ord_lift {ι} {f : ι -> Ordin
al -> Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : Cardinal.lift.{v, u} #ι < cof c) (hf
 : forall (i), fora…
· 使用定理 `Ordinal.derivFamily_add_one`：derivFamily_add_one (f : ι -> Ordinal -> Or
dinal) (o) : derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1)
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.derivFamily_limit`：derivFamily_limit (f : ι -> Ordinal -> Ordina
l) {o} : IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
· 使用定理 `Ordinal.lift_iSup_lt_of_lt_cof`：lift_iSup_lt_of_lt_cof {f : β -> Ordinal
.{u}} {a : Ordinal.{u}} (ha : Cardinal.lift.{u} #β < (lift.{v} a).cof) (hf : for
all i, f i < a) : ⨆ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_cof`：lift_cof (o : Ordinal.{u}) : Cardinal.lift.{v} (cof o)
 = cof (Ordinal.lift.{v} o)
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem derivFamily_lt_ord_lift {ι : Type u} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : lift.{v} #ι < c) (hc' : c ≠ ℵ₀) (hf : ∀ i, ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily f a < c.ord := by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_ord]
    exact lt_of_le_of_ne hc.1 hc'.symm
  induction a using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exact
      nfpFamily_lt_ord_lift hω (by rwa [hc.cof_ord]) hf
        ((isSuccLimit_ord hc.1).succ_lt (hb ((lt_succ b).trans hb')))
  | limit b hb H =>
    intro hb'
    rw [derivFamily_limit f hb]
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rwa [← lift_cof, hc.cof_ord, mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
    · exact fun i ↦ H i.1 i.2 <| i.2.trans hb'
/-
**Cardinal.derivFamily_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：derivFamily_lt_ord {ι} {f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c
) (hι : #ι < c) (hc' : c != ℵ₀) (hf : forall (i), forall b < c.ord, f i b < c.or
d) {a} : a < c.ord -> derivFamily.{u, u} f a < c.ord
参数：hc : IsRegular c；hι : #ι < c；hc' : c != ℵ₀；hf : forall (i), forall b < c.ord,
 f i b < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.derivFamily_lt_ord_lift`：derivFamily_lt_ord_lift {ι : Type u} {
f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c) (hι : lift.{v} #ι < c) (hc' 
: c != ℵ₀) (hf : foral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem derivFamily_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : #ι < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, u} f a < c.ord :=
  derivFamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf
/-
**Cardinal.deriv_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：deriv_lt_ord {f : Ordinal.{u} -> Ordinal} {c} (hc : IsRegular c) (hc' : c 
!= ℵ₀) (hf : forall i < c.ord, f i < c.ord) {a} : a < c.ord -> deriv f a < c.ord
参数：hc : IsRegular c；hc' : c != ℵ₀；hf : forall i < c.ord, f i < c.ord。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.derivFamily_lt_ord_lift`：derivFamily_lt_ord_lift {ι : Type u} {
f : ι -> Ordinal -> Ordinal} {c} (hc : IsRegular c) (hι : lift.{v} #ι < c) (hc' 
: c != ℵ₀) (hf : foral…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  derivFamily_lt_ord_lift hc
    (by simpa using Cardinal.one_lt_aleph0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf

/-! ### Singular cardinals -/

/-- A cardinal is singular if it is infinite and not regular. -/
@[mk_iff]
/-
**Cardinal.IsSingular** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cardinal`。
形式化陈述：Cardinal.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cardinal is singular if it is infinite and not regular.
-/
structure IsSingular (c : Cardinal) : Prop where
  /-- A singular cardinal is infinite. -/
  aleph0_le : ℵ₀ ≤ c
  /-- A singular cardinal is not regular, see `IsSingular.not_isRegular`. -/
  cof_ord_ne : c.ord.cof ≠ c
/-
**Cardinal.IsSingular.cof_ord_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSingular`
。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → c.ord.cof < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ordinal.cof_ord_le`：cof_ord_le (c : Cardinal) : c.ord.cof <= c
· 使用定理 `Cardinal.IsSingular.cof_ord_ne`：∀ {c : Cardinal.{u_1}}, c.IsSingular → c
.ord.cof ≠ c
-/
theorem IsSingular.cof_ord_lt (hc : c.IsSingular) : c.ord.cof < c :=
  (cof_ord_le c).lt_of_ne hc.cof_ord_ne
/-
**Cardinal.IsSingular.natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSingular`
。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → ∀ (n : ℕ), ↑n < c
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.IsSingular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsSingular → Ca
rdinal.aleph0 ≤ c
-/
theorem IsSingular.natCast_lt (hc : c.IsSingular) (n : ℕ) : n < c :=
  natCast_lt_aleph0.trans_le hc.aleph0_le
/-
**Cardinal.IsSingular.pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSingular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → 0 < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsSingular.natCast_lt`：∀ {c : Cardinal.{u_1}}, c.IsSingular → ∀
 (n : ℕ), ↑n < c
-/
theorem IsSingular.pos (hc : c.IsSingular) : 0 < c :=
  hc.natCast_lt 0
/-
**Cardinal.IsSingular.not_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSingul
ar`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → ¬c.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Cardinal.IsRegular.le_cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c ≤
 c.ord.cof
· 使用定理 `Cardinal.IsSingular.cof_ord_lt`：∀ {c : Cardinal.{u_1}}, c.IsSingular → c
.ord.cof < c
-/
theorem IsSingular.not_isRegular (hc : c.IsSingular) : ¬ c.IsRegular :=
  fun hc' ↦ hc'.le_cof_ord.not_gt hc.cof_ord_lt
/-
**Cardinal.IsRegular.not_isSingular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsRegula
r`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsRegular → ¬c.IsSingular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `Cardinal.IsSingular.not_isRegular`：∀ {c : Cardinal.{u_1}}, c.IsSingular 
→ ¬c.IsRegular
-/
theorem IsRegular.not_isSingular (hc : c.IsRegular) : ¬ c.IsSingular :=
  imp_not_comm.1 IsSingular.not_isRegular hc

@[simp]
/-
**Cardinal.not_isSingular_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isSingular_aleph0 : ¬ IsSingular ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.not_isSingular`：∀ {c : Cardinal.{u_1}}, c.IsRegular →
 ¬c.IsSingular
· 使用定理 `Cardinal.isRegular_aleph0`：isRegular_aleph0 : IsRegular ℵ₀
-/
theorem not_isSingular_aleph0 : ¬ IsSingular ℵ₀ :=
  isRegular_aleph0.not_isSingular

@[simp]
/-
**Cardinal.not_isSingular_aleph_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isSingular_aleph_one : ¬ IsSingular ℵ₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.not_isSingular`：∀ {c : Cardinal.{u_1}}, c.IsRegular →
 ¬c.IsSingular
· 使用定理 `Cardinal.isRegular_aleph_one`：isRegular_aleph_one : IsRegular ℵ₁
-/
theorem not_isSingular_aleph_one : ¬ IsSingular ℵ₁ :=
  isRegular_aleph_one.not_isSingular

@[simp]
/-
**Cardinal.not_isSingular_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isSingular_succ (c : Cardinal) : ¬ IsSingular (succ c)
参数：c : Cardinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Cardinal.IsSingular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsSingular → Ca
rdinal.aleph0 ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.succ_natCast`：succ_natCast (n : Nat) : Order.succ (n : Cardinal
) = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.IsRegular.not_isSingular`：∀ {c : Cardinal.{u_1}}, c.IsRegular →
 ¬c.IsSingular
· 使用定理 `Cardinal.isRegular_succ`：isRegular_succ {c : Cardinal} (hc : ℵ₀ <= c) : 
IsRegular (succ c)
-/
theorem not_isSingular_succ (c : Cardinal) : ¬ IsSingular (succ c) := by
  obtain hc | hc := lt_or_ge c ℵ₀
  · obtain ⟨n, rfl⟩ := lt_aleph0.1 hc
    refine fun h ↦ h.aleph0_le.not_gt ?_
    rw [succ_natCast, ← Nat.cast_add_one]
    exact natCast_lt_aleph0
  · exact (isRegular_succ hc).not_isSingular

@[simp]
/-
**Cardinal.not_isRegular_aleph_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_isRegular_aleph_add_one (o : Ordinal) : ¬ IsSingular (ℵ_ (o + 1))
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isRegular_aleph_add_one (o : Ordinal) : ¬ IsSingular (ℵ_ (o + 1)) := by
  simp [← succ_aleph]
/-
**Cardinal.IsSingular.isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSingular
`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → Order.IsSuccLimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isSuccLimit_iff`：∀ {c : Cardinal.{u_1}}, Order.IsSuccLimit c ↔ 
c ≠ 0 ∧ Order.IsSuccPrelimit c
· 使用定理 `Order.isSuccPrelimit_iff_succ_ne`：isSuccPrelimit_iff_succ_ne : IsSuccPre
limit a ↔ forall b, succ b != a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.IsSingular.pos`：∀ {c : Cardinal.{u_1}}, c.IsSingular → 0 < c
· 使用定理 `Cardinal.not_isSingular_succ`：not_isSingular_succ (c : Cardinal) : ¬ IsS
ingular (succ c)
-/
theorem IsSingular.isSuccLimit (hc : IsSingular c) : IsSuccLimit c := by
  rw [Cardinal.isSuccLimit_iff, isSuccPrelimit_iff_succ_ne]
  refine ⟨hc.pos.ne', ?_⟩
  rintro c rfl
  exact not_isSingular_succ c hc
/-
**Cardinal.isRegular_or_isSingular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isRegular_or_isSingular (h : ℵ₀ <= c) : c.IsRegular ∨ c.IsSingular
参数：h : ℵ₀ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.isSingular_iff`：∀ (c : Cardinal.{u_1}), c.IsSingular ↔ Cardinal
.aleph0 ≤ c ∧ c.ord.cof ≠ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Ordinal.cof_ord_le`：cof_ord_le (c : Cardinal) : c.ord.cof <= c
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem isRegular_or_isSingular (h : ℵ₀ ≤ c) : c.IsRegular ∨ c.IsSingular := by
  rw [isSingular_iff, ← (cof_ord_le c).lt_iff_ne, ← not_le]
  tauto
/-
**Cardinal.lt_aleph0_or_isRegular_or_isSingular** 是 Mathlib 中的一个定理，位于命名空间 `Cardi
nal`。
形式化陈述：lt_aleph0_or_isRegular_or_isSingular : c < ℵ₀ ∨ c.IsRegular ∨ c.IsSingular
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_or_isSingular`：isRegular_or_isSingular (h : ℵ₀ <= c) 
: c.IsRegular ∨ c.IsSingular
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem lt_aleph0_or_isRegular_or_isSingular : c < ℵ₀ ∨ c.IsRegular ∨ c.IsSingular := by
  have := isRegular_or_isSingular (c := c)
  rw [← not_le]
  tauto
/-
**Cardinal.IsSingular.of_not_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSin
gular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, Cardinal.aleph0 ≤ c → ¬c.IsRegular → c.IsSingular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Cardinal.isRegular_or_isSingular`：isRegular_or_isSingular (h : ℵ₀ <= c) 
: c.IsRegular ∨ c.IsSingular
-/
theorem IsSingular.of_not_isRegular (h₀ : ℵ₀ ≤ c) (hc : ¬ IsRegular c) : IsSingular c :=
  (isRegular_or_isSingular h₀).resolve_left hc
/-
**Cardinal.IsRegular.of_not_isSingular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsReg
ular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, Cardinal.aleph0 ≤ c → ¬c.IsSingular → c.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Cardinal.isRegular_or_isSingular`：isRegular_or_isSingular (h : ℵ₀ <= c) 
: c.IsRegular ∨ c.IsSingular
-/
theorem IsRegular.of_not_isSingular (h₀ : ℵ₀ ≤ c) (hc : ¬ IsSingular c) : IsRegular c :=
  (isRegular_or_isSingular h₀).resolve_right hc
/-
**Cardinal.isSingular_aleph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSingular_aleph_iff {o : Ordinal} : (ℵ_ o).IsSingular ↔ IsSuccLimit o ∧ o
.cof < ℵ_ o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.zero_or_succ_or_isSuccLimit`：zero_or_succ_or_isSuccLimit (o : Or
dinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_zero`：aleph_zero : ℵ_ 0 = ℵ₀
· 使用定理 `Ordinal.cof_zero`：cof_zero : cof 0 = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.cof_add`：cof_add (a : Ordinal) {b : Ordinal} (hb : b != 0) : cof
 (a + b) = cof b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.cof_one`：cof_one : cof 1 = 1
· 使用定理 `Cardinal.isSingular_iff`：∀ (c : Cardinal.{u_1}), c.IsSingular ↔ Cardinal
.aleph0 ≤ c ∧ c.ord.cof ≠ c
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Ordinal.cof_ord_le`：cof_ord_le (c : Cardinal) : c.ord.cof <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Ordinal.cof_omega`：cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o)
.cof = o.cof
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem isSingular_aleph_iff {o : Ordinal} : (ℵ_ o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o := by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp
  · simp
  · rw [isSingular_iff, ← (cof_ord_le _).lt_iff_ne]
    simp [ho]
/-
**Cardinal.IsSingular.isSuccLimit_of_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.I
sSingular`。
形式化陈述：∀ {o : Ordinal.{u_1}}, (Cardinal.aleph o).IsSingular → Order.IsSuccLimit o
参数：Cardinal.aleph o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.isSingular_aleph_iff`：isSingular_aleph_iff {o : Ordinal} : (ℵ_ 
o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o
-/
theorem IsSingular.isSuccLimit_of_aleph {o : Ordinal} (hc : IsSingular (ℵ_ o)) : IsSuccLimit o :=
  (isSingular_aleph_iff.1 hc).1
/-
**Cardinal.isSingular_aleph_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isSingular_aleph_omega0 : (ℵ_ ω).IsSingular
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.cof_omega0`：cof_omega0 : cof ω = ℵ₀
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isSingular_aleph_omega0 : (ℵ_ ω).IsSingular := by simp [isSingular_aleph_iff]
/-
**Cardinal.IsSingular.aleph_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsSing
ular`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsSingular → Cardinal.aleph Ordinal.omega0 ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mem_range_aleph_iff`：mem_range_aleph_iff {c : Cardinal} : c in 
range aleph ↔ ℵ₀ <= c
· 使用定理 `Cardinal.IsSingular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsSingular → Ca
rdinal.aleph0 ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph_le_aleph`：aleph_le_aleph {o₁ o₂ : Ordinal} : ℵ_ o₁ <= ℵ_ 
o₂ ↔ o₁ <= o₂
· 使用定理 `Ordinal.omega0_le_of_isSuccLimit`：omega0_le_of_isSuccLimit {o} (h : IsSu
ccLimit o) : ω <= o
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cardinal.isSingular_aleph_iff`：isSingular_aleph_iff {o : Ordinal} : (ℵ_ 
o).IsSingular ↔ IsSuccLimit o ∧ o.cof < ℵ_ o
-/
theorem IsSingular.aleph_omega0_le (hc : IsSingular c) : ℵ_ ω ≤ c := by
  obtain ⟨o, rfl⟩ := mem_range_aleph_iff.2 hc.aleph0_le
  rw [isSingular_aleph_iff] at hc
  rw [aleph_le_aleph]
  exact omega0_le_of_isSuccLimit hc.1

/-! ### Inaccessible cardinals -/

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
/-
**Cardinal.IsInaccessible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cardinal`。
形式化陈述：Cardinal.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cardinal is inaccessible if it is an uncountable regular strong limit cardinal
.
-/
structure IsInaccessible (c : Cardinal) : Prop where
  /-- An inaccessible cardinal is uncountable. -/
  aleph0_lt : ℵ₀ < c
  /-- An inaccessible cardinal is equal to its own cofinality, see `IsInaccessible.isRegular`. -/
  le_cof_ord : c ≤ c.ord.cof
  /-- An inaccessible cardinal is a strong limit, see `IsInaccessible.isStrongLimit`. -/
  protected isStrongPrelimit : IsStrongPrelimit c
/-
**Cardinal.IsInaccessible.nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInaccessi
ble`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → ∀ (n : ℕ), ↑n < c
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
-/
theorem IsInaccessible.nat_lt (h : IsInaccessible c) (n : ℕ) : n < c :=
  natCast_lt_aleph0.trans h.1
/-
**Cardinal.IsInaccessible.pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInaccessible
`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → 0 < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
-/
theorem IsInaccessible.pos (h : IsInaccessible c) : 0 < c :=
  aleph0_pos.trans h.1
/-
**Cardinal.IsInaccessible.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInaccess
ible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → c ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Cardinal.IsInaccessible.pos`：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → 
0 < c
-/
theorem IsInaccessible.ne_zero (h : IsInaccessible c) : c ≠ 0 :=
  h.pos.ne'
/-
**Cardinal.IsInaccessible.isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInacce
ssible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → c.IsRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
· 使用定理 `Cardinal.IsInaccessible.le_cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsInaccess
ible → c ≤ c.ord.cof
-/
theorem IsInaccessible.isRegular (h : IsInaccessible c) : IsRegular c :=
  ⟨h.aleph0_lt.le, h.le_cof_ord⟩
/-
**Cardinal.IsInaccessible.isStrongLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsIn
accessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → c.IsStrongLimit
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsInaccessible.ne_zero`：∀ {c : Cardinal.{u_1}}, c.IsInaccessibl
e → c ≠ 0
· 使用定理 `Cardinal.IsInaccessible.isStrongPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsIn
accessible → c.IsStrongPrelimit
-/
theorem IsInaccessible.isStrongLimit {c : Cardinal} (h : IsInaccessible c) : IsStrongLimit c :=
  ⟨h.ne_zero, h.isStrongPrelimit⟩
/-
**Cardinal.IsInaccessible.isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInac
cessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Order.IsSuccLimit c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsStrongLimit.isSuccLimit`：∀ {c : Cardinal.{u_1}}, c.IsStrongLi
mit → Order.IsSuccLimit c
· 使用定理 `Cardinal.IsInaccessible.isStrongLimit`：∀ {c : Cardinal.{u_1}}, c.IsInacc
essible → c.IsStrongLimit
-/
theorem IsInaccessible.isSuccLimit {c : Cardinal} (h : IsInaccessible c) : IsSuccLimit c :=
  h.isStrongLimit.isSuccLimit
/-
**Cardinal.isInaccessible_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isInaccessible_def : IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLim
it c where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
· 使用定理 `Cardinal.IsInaccessible.isRegular`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → c.IsRegular
· 使用定理 `Cardinal.IsInaccessible.isStrongLimit`：∀ {c : Cardinal.{u_1}}, c.IsInacc
essible → c.IsStrongLimit
· 使用定理 `Cardinal.IsRegular.le_cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c ≤
 c.ord.cof
· 使用定理 `Cardinal.IsStrongLimit.isStrongPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsStr
ongLimit → c.IsStrongPrelimit
-/
theorem isInaccessible_def : IsInaccessible c ↔ ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c where
  mp h := ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  mpr := fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂.2, h₃.isStrongPrelimit⟩

/-- Lean's foundations prove the existence of `v` inaccessibles in universe `v`. -/
/-
**Cardinal.IsInaccessible.univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInaccessibl
e`。
形式化陈述：Cardinal.univ.{u, v}.IsInaccessible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_lt_univ`：aleph0_lt_univ : ℵ₀ < univ.{u, v}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Ordinal.cof_univ`：cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v}
· 使用定理 `Cardinal.IsStrongLimit.isStrongPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsStr
ongLimit → c.IsStrongPrelimit
· 使用定理 `Cardinal.IsStrongLimit.univ`：Cardinal.univ.{u, v}.IsStrongLimit

--- 原说明 ---
Lean's foundations prove the existence of `v` inaccessibles in universe `v`.
-/
theorem IsInaccessible.univ : IsInaccessible univ.{u, v} :=
  ⟨aleph0_lt_univ, by simp, IsStrongLimit.univ.isStrongPrelimit⟩
/-
**Cardinal.IsInaccessible.preBeth_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInac
cessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Cardinal.preBeth c.ord = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Cardinal.preBeth_strictMono`：preBeth_strictMono : StrictMono preBeth
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `Cardinal.isNormal_preBeth`：isNormal_preBeth : Order.IsNormal preBeth
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preBeth.eq_1`：∀ (o : Ordinal.{u}), Cardinal.preBeth o = ⨆ a, 2 
^ Cardinal.preBeth ↑a
· 使用定理 `Cardinal.lift_iSup_lt_of_lt_cof_ord`：∀ {β : Type v} {f : β → Cardinal.{u
}} {a : Cardinal.{u}},   Cardinal.lift.{u, v} (Cardinal.mk β) < (Cardinal.lift.{
v, u} a).ord.cof → (∀ (i …
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `Cardinal.IsRegular.lift`：∀ {κ : Cardinal.{v}}, κ.IsRegular → (Cardinal.l
ift.{u, v} κ).IsRegular
· 使用定理 `Cardinal.IsInaccessible.isRegular`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → c.IsRegular
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Cardinal.IsInaccessible.isStrongPrelimit`：∀ {c : Cardinal.{u_1}}, c.IsIn
accessible → c.IsStrongPrelimit
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem IsInaccessible.preBeth_ord (hc : IsInaccessible c) : preBeth c.ord = c := by
  apply (preBeth_strictMono.comp ord_strictMono).le_apply.antisymm'
  apply (isNormal_preBeth.le_iff_forall_le (isSuccLimit_ord hc.aleph0_lt.le)).2
  refine fun a ha ↦ le_of_lt ?_
  induction a using WellFoundedLT.induction with | ind a IH
  rw [preBeth]
  apply lift_iSup_lt_of_lt_cof_ord _ _
  · rwa [mk_Iio_ordinal, lift_lift, hc.isRegular.lift.cof_ord, lift_lt, ← lt_ord]
  · rintro ⟨b, hb⟩
    exact hc.isStrongPrelimit <| IH _ hb (hb.trans ha)
/-
**Cardinal.IsInaccessible.beth_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInacces
sible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Cardinal.beth c.ord = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.preBeth_of_omega0_sq_le`：preBeth_of_omega0_sq_le {o : Ordinal} 
(ho : ω ^ 2 <= o) : preBeth o = ℶ_ o
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ordinal.card_mul`：card_mul (a b) : card (a * b) = card a * card b
· 使用定理 `Ordinal.card_omega0`：card_omega0 : card ω = ℵ₀
· 使用定理 `Cardinal.aleph0_mul_aleph0`：aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀
· 使用定理 `Cardinal.IsInaccessible.aleph0_lt`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph0 < c
· 使用定理 `Cardinal.IsInaccessible.preBeth_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacces
sible → Cardinal.preBeth c.ord = c
-/
theorem IsInaccessible.beth_ord (hc : IsInaccessible c) : ℶ_ c.ord = c := by
  rw [← preBeth_of_omega0_sq_le (le_of_lt _), hc.preBeth_ord]
  rw [lt_ord, pow_two, card_mul, card_omega0, aleph0_mul_aleph0]
  exact hc.aleph0_lt
/-
**Cardinal.IsInaccessible.preAleph_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsIna
ccessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Cardinal.preAleph c.ord = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.preAleph_le_preBeth`：preAleph_le_preBeth (o : Ordinal) : preAle
ph o <= preBeth o
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.IsInaccessible.preBeth_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacces
sible → Cardinal.preBeth c.ord = c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
-/
theorem IsInaccessible.preAleph_ord (hc : IsInaccessible c) : preAleph c.ord = c :=
  ((preAleph_le_preBeth _).trans hc.preBeth_ord.le).antisymm
    (preAleph.strictMono.comp ord_strictMono).le_apply
/-
**Cardinal.IsInaccessible.preAleph_symm_eq_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardin
al.IsInaccessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Cardinal.preAleph.symm c = c.or
d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `Cardinal.IsInaccessible.preAleph_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacce
ssible → Cardinal.preAleph c.ord = c
-/
theorem IsInaccessible.preAleph_symm_eq_ord (hc : IsInaccessible c) : preAleph.symm c = c.ord := by
  rw [OrderIso.symm_apply_eq, hc.preAleph_ord]
/-
**Cardinal.IsInaccessible.aleph_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInacce
ssible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Cardinal.aleph c.ord = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.aleph_le_beth`：aleph_le_beth (o : Ordinal) : ℵ_ o <= ℶ_ o
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.IsInaccessible.beth_ord`：∀ {c : Cardinal.{u_1}}, c.IsInaccessib
le → Cardinal.beth c.ord = c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
-/
theorem IsInaccessible.aleph_ord (hc : IsInaccessible c) : ℵ_ c.ord = c :=
  ((aleph_le_beth _).trans hc.beth_ord.le).antisymm (aleph.strictMono.comp ord_strictMono).le_apply
/-
**Cardinal.IsInaccessible.preOmega_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsIna
ccessible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Ordinal.preOmega c.ord = c.ord
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_preAleph`：ord_preAleph (o : Ordinal) : (preAleph o).ord = p
reOmega o
· 使用定理 `Cardinal.IsInaccessible.preAleph_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacce
ssible → Cardinal.preAleph c.ord = c
-/
theorem IsInaccessible.preOmega_ord (hc : IsInaccessible c) : preOmega c.ord = c.ord := by
  rw [← ord_preAleph, hc.preAleph_ord]
/-
**Cardinal.IsInaccessible.omega_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.IsInacce
ssible`。
形式化陈述：∀ {c : Cardinal.{u_1}}, c.IsInaccessible → Ordinal.omega c.ord = c.ord
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_aleph`：ord_aleph (o : Ordinal) : (ℵ_ o).ord = ω_ o
· 使用定理 `Cardinal.IsInaccessible.aleph_ord`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph c.ord = c
-/
theorem IsInaccessible.omega_ord (hc : IsInaccessible c) : ω_ c.ord = c.ord := by
  rw [← ord_aleph, hc.aleph_ord]

@[simp]
/-
**Cardinal.preBeth_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preBeth_univ : preBeth Ordinal.univ.{u, v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Cardinal.IsInaccessible.preBeth_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacces
sible → Cardinal.preBeth c.ord = c
· 使用定理 `Cardinal.IsInaccessible.univ`：Cardinal.univ.{u, v}.IsInaccessible
-/
theorem preBeth_univ : preBeth Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preBeth_ord

@[simp]
/-
**Cardinal.beth_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：beth_univ : ℶ_ Ordinal.univ.{u, v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Cardinal.IsInaccessible.beth_ord`：∀ {c : Cardinal.{u_1}}, c.IsInaccessib
le → Cardinal.beth c.ord = c
· 使用定理 `Cardinal.IsInaccessible.univ`：Cardinal.univ.{u, v}.IsInaccessible
-/
theorem beth_univ : ℶ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.beth_ord

@[simp]
/-
**Cardinal.preAleph_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_univ : preAleph Ordinal.univ.{u, v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Cardinal.IsInaccessible.preAleph_ord`：∀ {c : Cardinal.{u_1}}, c.IsInacce
ssible → Cardinal.preAleph c.ord = c
· 使用定理 `Cardinal.IsInaccessible.univ`：Cardinal.univ.{u, v}.IsInaccessible
-/
theorem preAleph_univ : preAleph Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.preAleph_ord

@[simp]
/-
**Cardinal.preAleph_symm_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：preAleph_symm_univ : preAleph.symm univ.{u, v} = Ordinal.univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.preAleph_univ`：preAleph_univ : preAleph Ordinal.univ.{u, v} = u
niv.{u, v}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preAleph_symm_univ : preAleph.symm univ.{u, v} = Ordinal.univ.{u, v} := by
  simp [OrderIso.symm_apply_eq]

@[simp]
/-
**Cardinal.aleph_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_univ : ℵ_ Ordinal.univ.{u, v} = univ.{u, v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_univ`：ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v}
· 使用定理 `Cardinal.IsInaccessible.aleph_ord`：∀ {c : Cardinal.{u_1}}, c.IsInaccessi
ble → Cardinal.aleph c.ord = c
· 使用定理 `Cardinal.IsInaccessible.univ`：Cardinal.univ.{u, v}.IsInaccessible
-/
theorem aleph_univ : ℵ_ Ordinal.univ.{u, v} = univ.{u, v} := by
  simpa using IsInaccessible.univ.aleph_ord

@[simp]
/-
**Cardinal._root_.Ordinal.preOmega_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.preOmega_univ : preOmega Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.preOmega_ord

@[simp]
/-
**Cardinal._root_.Ordinal.omega_univ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ordinal.omega_univ : ω_ Ordinal.univ.{u, v} = Ordinal.univ.{u, v} := by
  simpa using IsInaccessible.univ.omega_ord

end Cardinal

