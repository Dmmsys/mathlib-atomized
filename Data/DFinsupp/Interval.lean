/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Order
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `Π₀ i, α i` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.
-/

@[expose] public section


open DFinsupp Finset

open scoped Pointwise

variable {ι : Type*} {α : ι → Type*}

namespace Finset

variable [DecidableEq ι] [∀ i, Zero (α i)] {s : Finset ι} {f : Π₀ i, α i} {t : ∀ i, Finset (α i)}

/-- Finitely supported product of finsets. -/
/-
**Finset.dfinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：dfinsupp (s : Finset ι) (t : forall i, Finset (α i)) : Finset (Π₀ i, α i)
参数：s : Finset ι；t : forall i, Finset (α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finitely supported product of finsets.
-/
def dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : Finset (Π₀ i, α i) :=
  (s.pi t).map
    ⟨fun f => DFinsupp.mk s fun i => f i i.2, by
      refine (mk_injective _).comp fun f g h => ?_
      ext i hi
      convert! congr_fun h ⟨i, hi⟩⟩

@[simp]
/-
**Finset.card_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_dfinsupp (s : Finset ι) (t : forall i, Finset (α i)) : #(s.dfinsupp t
) = ∏ i in s, #(t i)
参数：s : Finset ι；t : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq 
ι] (s : Finset ι) (t : (i : ι) → Finset (α i)),   (s.pi t).card = ∏ i ∈ s, (t i)
.car…
-/
theorem card_dfinsupp (s : Finset ι) (t : ∀ i, Finset (α i)) : #(s.dfinsupp t) = ∏ i ∈ s, #(t i) :=
  (card_map _).trans <| card_pi _ _

variable [∀ i, DecidableEq (α i)]
/-
**Finset.mem_dfinsupp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_dfinsupp_iff : f in s.dfinsupp t ↔ f.support subseteq s ∧ forall i in 
s, f i in t i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `DFinsupp.support_mk_subset`：support_mk_subset {s : Finset ι} {x : forall
 i : (↑s : Set ι), β i.1} : (mk s x).support subseteq s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.mk_of_mem`：mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i
 = x ⟨i, hi⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_pi`：mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : f
orall a in s, β a} : f in s.pi t ↔ forall (a) (h : a in s), f a h in t a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_dfinsupp_iff : f ∈ s.dfinsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    rw [Function.Embedding.coeFn_mk]
    refine ⟨support_mk_subset, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact mk_of_mem hi
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    dsimp
    exact ite_eq_left_iff.2 fun hi => (notMem_support_iff.1 fun H => hi <| h.1 H).symm

/-- When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is pointwise in `t`.
-/
@[simp]
/-
**Finset.mem_dfinsupp_iff_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.suppor
t subseteq s) : f in s.dfinsupp t ↔ forall i, f i in t i
参数：α i；ht : t.support subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_dfinsupp_iff`：mem_dfinsupp_iff : f in s.dfinsupp t ↔ f.suppor
t subseteq s ∧ forall i in s, f i in t i
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Finset.zero_mem_zero`：∀ {α : Type u_2} [inst : Zero α], 0 ∈ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Finset.mem_zero`：∀ {α : Type u_2} [inst : Zero α] {a : α}, a ∈ 0 ↔ a = 0

--- 原说明 ---
When `t` is supported on `s`, `f ∈ s.dfinsupp t` precisely means that `f` is poi
ntwise in `t`.
-/
theorem mem_dfinsupp_iff_of_support_subset {t : Π₀ i, Finset (α i)} (ht : t.support ⊆ s) :
    f ∈ s.dfinsupp t ↔ ∀ i, f i ∈ t i := by
  refine mem_dfinsupp_iff.trans (forall_and.symm.trans <| forall_congr' fun i =>
      ⟨ fun h => ?_,
        fun h => ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff.1 (notMem_mono ht hi)]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h

end Finset

namespace DFinsupp

section BundledSingleton

variable [∀ i, Zero (α i)] {f : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `Finset.singleton` bundled as a `DFinsupp`. -/
/-
**DFinsupp.singleton** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) where toFun i
参数：f : Π₀ i, α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise `Finset.singleton` bundled as a `DFinsupp`.
-/
def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := {f i}
  support' := f.support'.map fun s => ⟨s.1, fun i => (s.prop i).imp id (congr_arg _)⟩
/-
**DFinsupp.mem_singleton_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mem_singleton_apply_iff : a in f.singleton i ↔ a = f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton

end BundledSingleton

section BundledIcc

variable [∀ i, Zero (α i)] [∀ i, PartialOrder (α i)] [∀ i, LocallyFiniteOrder (α i)]
  {f g : Π₀ i, α i} {i : ι} {a : α i}

/-- Pointwise `Finset.Icc` bundled as a `DFinsupp`. -/
/-
**DFinsupp.rangeIcc** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) where toFun i
参数：f g : Π₀ i, α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise `Finset.Icc` bundled as a `DFinsupp`.
-/
def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) where
  toFun i := Icc (f i) (g i)
  support' := f.support'.bind fun fs => g.support'.map fun gs =>
    ⟨ fs.1 + gs.1,
      fun i => or_iff_not_imp_left.2 fun h => by
        have hf : f i = 0 := (fs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_right _ _) h)
        have hg : g i = 0 := (gs.prop i).resolve_left
            (Multiset.notMem_mono (Multiset.Le.subset <| Multiset.le_add_left _ _) h)
        simp_rw [hf, hg]
        exact Icc_self _⟩

@[simp]
/-
**DFinsupp.rangeIcc_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i
)
参数：f g : Π₀ i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl
/-
**DFinsupp.mem_rangeIcc_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mem_rangeIcc_apply_iff : a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc
/-
**DFinsupp.support_rangeIcc_subset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_rangeIcc_subset [DecidableEq ι] [forall i, DecidableEq (α i)] : (f
.rangeIcc g).support subseteq f.support union g.support
参数：α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.rangeIcc_apply`：rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.ra
ngeIcc g i = Icc (f i) (g i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem support_rangeIcc_subset [DecidableEq ι] [∀ i, DecidableEq (α i)] :
    (f.rangeIcc g).support ⊆ f.support ∪ g.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 ?_ hx
  rw [rangeIcc_apply, notMem_support_iff.1 (notMem_mono subset_union_left h),
    notMem_support_iff.1 (notMem_mono subset_union_right h)]
  exact Icc_self _

end BundledIcc

section Pi

variable [∀ i, Zero (α i)] [DecidableEq ι] [∀ i, DecidableEq (α i)]

/-- Given a finitely supported function `f : Π₀ i, Finset (α i)`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
/-
**DFinsupp.pi** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i)
参数：f : Π₀ i, Finset (α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finitely supported function `f : Π₀ i, Finset (α i)`, one can define the
 finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for al
l `i`.
-/
def pi (f : Π₀ i, Finset (α i)) : Finset (Π₀ i, α i) := f.support.dfinsupp f

@[simp]
/-
**DFinsupp.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g in f.pi ↔ forall i, g 
i in f i
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_dfinsupp_iff_of_support_subset`：mem_dfinsupp_iff_of_support_s
ubset {t : Π₀ i, Finset (α i)} (ht : t.support subseteq s) : f in s.dfinsupp t ↔
 forall i, f i in t i
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem mem_pi {f : Π₀ i, Finset (α i)} {g : Π₀ i, α i} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_dfinsupp_iff_of_support_subset <| Subset.refl _

@[simp]
/-
**DFinsupp.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：card_pi (f : Π₀ i, Finset (α i)) : #f.pi = f.prod fun i => #(f i)
参数：f : Π₀ i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.pi.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → 
Zero (α i)] [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → DecidableEq (α i)] (f
 : Π₀ …
· 使用定理 `Finset.card_dfinsupp`：card_dfinsupp (s : Finset ι) (t : forall i, Finset
 (α i)) : #(s.dfinsupp t) = ∏ i in s, #(t i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_pi (f : Π₀ i, Finset (α i)) : #f.pi = f.prod fun i ↦ #(f i) := by
  rw [pi, card_dfinsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

end Pi

section PartialOrder

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]
variable [∀ i, PartialOrder (α i)] [∀ i, Zero (α i)] [∀ i, LocallyFiniteOrder (α i)]

/-
**DFinsupp.instLocallyFiniteOrder** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instLocallyFiniteOrder : LocallyFiniteOrder (Π₀ i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Π₀ i, α i) :=
  LocallyFiniteOrder.ofIcc (Π₀ i, α i)
    (fun f g => (f.support ∪ g.support).dfinsupp <| f.rangeIcc g)
    (fun f g x => by
      refine (mem_dfinsupp_iff_of_support_subset <| support_rangeIcc_subset).trans ?_
      simp_rw [mem_rangeIcc_apply_iff, forall_and]
      rfl)

variable (f g : Π₀ i, α i)
/-
**DFinsupp.Icc_eq** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：Icc_eq : Icc f g = (f.support union g.support).dfinsupp (f.rangeIcc g)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_eq : Icc f g = (f.support ∪ g.support).dfinsupp (f.rangeIcc g) := rfl
/-
**DFinsupp.card_Icc** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Icc : #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i
))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_dfinsupp`：card_dfinsupp (s : Finset ι) (t : forall i, Finset
 (α i)) : #(s.dfinsupp t) = ∏ i in s, #(t i)
-/
lemma card_Icc : #(Icc f g) = ∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i)) :=
  card_dfinsupp _ _
/-
**DFinsupp.card_Ico** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Ico : #(Ico f g) = (∏ i in f.support union g.support, #(Icc (f i) (g 
i))) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
-/
lemma card_Ico : #(Ico f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
/-
**DFinsupp.card_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Ioc : #(Ioc f g) = (∏ i in f.support union g.support, #(Icc (f i) (g 
i))) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
-/
lemma card_Ioc : #(Ioc f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
/-
**DFinsupp.card_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Ioo : #(Ioo f g) = (∏ i in f.support union g.support, #(Icc (f i) (g 
i))) - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
-/
lemma card_Ioo : #(Ioo f g) = (∏ i ∈ f.support ∪ g.support, #(Icc (f i) (g i))) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end PartialOrder

section Lattice
variable [DecidableEq ι] [∀ i, DecidableEq (α i)] [∀ i, Lattice (α i)] [∀ i, Zero (α i)]
  [∀ i, LocallyFiniteOrder (α i)] (f g : Π₀ i, α i)

/-
**DFinsupp.card_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_uIcc : #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (
g i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.support_inf_union_support_sup`：support_inf_union_support_sup : 
(f ⊓ g).support union (f ⊔ g).support = f.support union g.support
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
-/
lemma card_uIcc : #(uIcc f g) = ∏ i ∈ f.support ∪ g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _

end Lattice

section IsBotZeroClass

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]
variable [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]
  [∀ i, OrderBot (α i)] [∀ i, LocallyFiniteOrder (α i)]
variable (f : Π₀ i, α i)

/-
**DFinsupp.card_Iic** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `DFinsupp.instIsBotZeroClass`：∀ {ι : Type u_1} (α : ι → Type u_2) [inst :
 (i : ι) → AddCommMonoid (α i)] [inst_1 : (i : ι) → PartialOrder (α i)]   [∀ (i 
: ι), IsBotZeroCl…
· 使用引理 `DFinsupp.card_Icc`：card_Icc : #(Icc f g) = ∏ i in f.support union g.supp
ort, #(Icc (f i) (g i))
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_Iic : #(Iic f) = ∏ i ∈ f.support, #(Iic (f i)) := by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]
/-
**DFinsupp.card_Iio** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：card_Iio : #(Iio f) = (∏ i in f.support, #(Iic (f i))) - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Iio_eq_card_Iic_sub_one`：card_Iio_eq_card_Iic_sub_one (a : α
) : #(Iio a) = #(Iic a) - 1
· 使用引理 `DFinsupp.card_Iic`：card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i))
-/
lemma card_Iio : #(Iio f) = (∏ i ∈ f.support, #(Iic (f i))) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end IsBotZeroClass

end DFinsupp

