/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finitely supported product of finsets

This file defines the finitely supported product of finsets as a `Finset (ι →₀ α)`.

## Main declarations

* `Finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `Finsupp.pi`: `f.pi` is the finset of `Finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `Finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : Finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/

@[expose] public section


noncomputable section

open Finsupp

open scoped Pointwise

variable {ι α : Type*} [Zero α] {s : Finset ι} {f : ι →₀ α}

namespace Finset

open scoped Classical in
/-- Finitely supported product of finsets. -/
/-
**Finset.finsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{ι : Type u_1} → {α : Type u_2} → [inst : Zero α] → Finset ι → (ι → Finset
 α) → Finset (ι →₀ α)
参数：ι → Finset α；ι →₀ α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.indicator_injective`：indicator_injective : Injective fun f : for
all i in s, α => indicator s f

--- 原说明 ---
Finitely supported product of finsets.
-/
protected def finsupp (s : Finset ι) (t : ι → Finset α) : Finset (ι →₀ α) :=
  (s.pi t).map ⟨indicator s, indicator_injective s⟩
/-
**Finset.mem_finsupp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_finsupp_iff {t : ι -> Finset α} : f in s.finsupp t ↔ f.support subsete
q s ∧ forall i in s, f i in t i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finsupp.indicator_injective`：indicator_injective : Injective fun f : for
all i in s, α => indicator s f
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finsupp.support_indicator_subset`：support_indicator_subset : (indicator 
s f).support subseteq s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.indicator_of_mem`：indicator_of_mem (hi : i in s) (f : forall i i
n s, α) : indicator s f i = f i hi
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_pi`：mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : f
orall a in s, β a} : f in s.pi t ↔ forall (a) (h : a in s), f a h in t a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `ite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y :
 α}, (if p then x else y) = x ↔ ¬p → y = x
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_finsupp_iff {t : ι → Finset α} :
    f ∈ s.finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  classical
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (notMem_support_iff.1 fun H => hi <| h.1 H).symm

/-- When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is pointwise in `t`. -/
@[simp]
/-
**Finset.mem_finsupp_iff_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_finsupp_iff_of_support_subset {t : ι ->₀ Finset α} (ht : t.support sub
seteq s) : f in s.finsupp t ↔ forall i, f i in t i
参数：ht : t.support subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_finsupp_iff`：mem_finsupp_iff {t : ι -> Finset α} : f in s.fin
supp t ↔ f.support subseteq s ∧ forall i in s, f i in t i
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.zero_mem_zero`：∀ {α : Type u_2} [inst : Zero α], 0 ∈ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_zero`：∀ {α : Type u_2} [inst : Zero α] {a : α}, a ∈ 0 ↔ a = 0

--- 原说明 ---
When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is poin
twise in `t`.
-/
theorem mem_finsupp_iff_of_support_subset {t : ι →₀ Finset α} (ht : t.support ⊆ s) :
    f ∈ s.finsupp t ↔ ∀ i, f i ∈ t i := by
  refine
    mem_finsupp_iff.trans
      (forall_and.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => ?_, fun h =>
            ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff.1 fun H => hi <| ht H]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h

@[simp]
/-
**Finset.card_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_finsupp (s : Finset ι) (t : ι -> Finset α) : #(s.finsupp t) = ∏ i in 
s, #(t i)
参数：s : Finset ι；t : ι -> Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.indicator_injective`：indicator_injective : Injective fun f : for
all i in s, α => indicator s f
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq 
ι] (s : Finset ι) (t : (i : ι) → Finset (α i)),   (s.pi t).card = ∏ i ∈ s, (t i)
.car…
-/
theorem card_finsupp (s : Finset ι) (t : ι → Finset α) : #(s.finsupp t) = ∏ i ∈ s, #(t i) := by
  classical exact (card_map _).trans <| card_pi _ _

end Finset

open Finset

namespace Finsupp

/-- Given a finitely supported function `f : ι →₀ Finset α`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
/-
**Finsupp.pi** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：pi (f : ι ->₀ Finset α) : Finset (ι ->₀ α)
参数：f : ι ->₀ Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finitely supported function `f : ι →₀ Finset α`, one can define the fins
et
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for al
l `i`.
-/
def pi (f : ι →₀ Finset α) : Finset (ι →₀ α) :=
  f.support.finsupp f

@[simp]
/-
**Finsupp.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_pi {f : ι ->₀ Finset α} {g : ι ->₀ α} : g in f.pi ↔ forall i, g i in f
 i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_finsupp_iff_of_support_subset`：mem_finsupp_iff_of_support_sub
set {t : ι ->₀ Finset α} (ht : t.support subseteq s) : f in s.finsupp t ↔ forall
 i, f i in t i
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem mem_pi {f : ι →₀ Finset α} {g : ι →₀ α} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_finsupp_iff_of_support_subset <| Subset.refl _

@[simp]
/-
**Finsupp.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_pi (f : ι ->₀ Finset α) : #f.pi = f.prod fun i => #(f i)
参数：f : ι ->₀ Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.pi.eq_1`：∀ {ι : Type u_1} {α : Type u_2} [inst : Zero α] (f : ι 
→₀ Finset α), f.pi = f.support.finsupp ⇑f
· 使用定理 `Finset.card_finsupp`：card_finsupp (s : Finset ι) (t : ι -> Finset α) : #
(s.finsupp t) = ∏ i in s, #(t i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_pi (f : ι →₀ Finset α) : #f.pi = f.prod fun i ↦ #(f i) := by
  rw [pi, card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

end Finsupp

