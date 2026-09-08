/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Topology.MetricSpace.Basic

/-!
# Infimum separation

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `Set` namespace to give access to dot notation.

## Main definitions
* `Set.einfsep`: Extended infimum separation of a set.
* `Set.infsep`: Infimum separation of a set (when in a pseudometric space).

-/

@[expose] public section


variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

/-- The "extended infimum separation" of a set with an edist function. -/
/-
**Set.einfsep** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：einfsep [EDist α] (s : Set α) : Real>=0∞
参数：s : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "extended infimum separation" of a set with an edist function.
-/
noncomputable def einfsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (_ : x ≠ y), edist x y

section EDist

variable [EDist α] {x y : α} {s t : Set α}

/-
**Set.le_einfsep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep_iff {d} : d <= s.einfsep ↔ forall x in s, forall y in s, x != y
 -> d <= edist x y
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by
  simp_rw [einfsep, le_iInf_iff]
/-
**Set.einfsep_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_zero : s.einfsep = 0 ↔ forall C > 0, exists x in s, exists y in s,
 x != y ∧ edist x y < C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_zero : s.einfsep = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < C := by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]
/-
**Set.einfsep_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pos : 0 < s.einfsep ↔ exists C > 0, forall x in s, forall y in s, 
x != y -> C <= edist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.einfsep_zero`：einfsep_zero : s.einfsep = 0 ↔ forall C > 0, exists x 
in s, exists y in s, x != y ∧ edist x y < C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_pos : 0 < s.einfsep ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [pos_iff_ne_zero, Ne, einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]
/-
**Set.einfsep_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_top : s.einfsep = ∞ ↔ forall x in s, forall y in s, x != y -> edis
t x y = ∞
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_top :
    s.einfsep = ∞ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edist x y = ∞ := by
  simp_rw [einfsep, iInf_eq_top]
/-
**Set.einfsep_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_lt_top : s.einfsep < ∞ ↔ exists x in s, exists y in s, x != y ∧ ed
ist x y < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < ∞ := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]
/-
**Set.einfsep_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_ne_top : s.einfsep != ∞ ↔ exists x in s, exists y in s, x != y ∧ e
dist x y != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_ne_top :
    s.einfsep ≠ ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y ≠ ∞ := by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]
/-
**Set.einfsep_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_lt_iff {d} : s.einfsep < d ↔ exists x in s, exists y in s, x != y 
∧ edist x y < d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < d := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]
/-
**Set.nontrivial_of_einfsep_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial
参数：hs : s.einfsep < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.einfsep_lt_top`：einfsep_lt_top : s.einfsep < ∞ ↔ exists x in s, exis
ts y in s, x != y ∧ edist x y < ∞
-/
theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial := by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩
/-
**Set.nontrivial_of_einfsep_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_einfsep_ne_top (hs : s.einfsep != ∞) : s.Nontrivial
参数：hs : s.einfsep != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_einfsep_lt_top`：nontrivial_of_einfsep_lt_top (hs : s.e
infsep < ∞) : s.Nontrivial
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.Nontrivial :=
  nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)
/-
**Set.Subsingleton.einfsep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Set α}, s.Subsingleton → s.einfsep 
= ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.einfsep_top`：einfsep_top : s.einfsep = ∞ ↔ forall x in s, forall y i
n s, x != y -> edist x y = ∞
-/
theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ := by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim
/-
**Set.le_einfsep_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep_image_iff {d} {f : β -> α} {s : Set β} : d <= einfsep (f '' s) 
↔ forall x in s, forall y in s, f x != f y -> d <= edist (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_einfsep_image_iff {d} {f : β → α} {s : Set β} : d ≤ einfsep (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) := by
  simp_rw [le_einfsep_iff, forall_mem_image]
/-
**Set.le_edist_of_le_einfsep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_edist_of_le_einfsep {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y
) (hd : d <= s.einfsep) : d <= edist x y
参数：hx : x in s；hy : y in s；hxy : x != y；hd : d <= s.einfsep。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.le_einfsep_iff`：le_einfsep_iff {d} : d <= s.einfsep ↔ forall x in s,
 forall y in s, x != y -> d <= edist x y
-/
theorem le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.einfsep) : d ≤ edist x y :=
  le_einfsep_iff.1 hd x hx y hy hxy
/-
**Set.einfsep_le_edist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_le_edist_of_mem {x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
 : s.einfsep <= edist x y
参数：hx : x in s；hy : y in s；hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_edist_of_le_einfsep`：le_edist_of_le_einfsep {d x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) (hd : d <= s.einfsep) : d <= edist x y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    s.einfsep ≤ edist x y :=
  le_edist_of_le_einfsep hx hy hxy le_rfl
/-
**Set.einfsep_le_of_mem_of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_le_of_mem_of_edist_le {d x} (hx : x in s) {y} (hy : y in s) (hxy :
 x != y) (hxy' : edist x y <= d) : s.einfsep <= d
参数：hx : x in s；hy : y in s；hxy : x != y；hxy' : edist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.einfsep_le_edist_of_mem`：einfsep_le_edist_of_mem {x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) : s.einfsep <= edist x y
-/
theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : s.einfsep ≤ d :=
  le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'
/-
**Set.le_einfsep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep {d} (h : forall x in s, forall y in s, x != y -> d <= edist x y
) : d <= s.einfsep
参数：h : forall x in s, forall y in s, x != y -> d <= edist x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.le_einfsep_iff`：le_einfsep_iff {d} : d <= s.einfsep ↔ forall x in s,
 forall y in s, x != y -> d <= edist x y
-/
theorem le_einfsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.einfsep :=
  le_einfsep_iff.2 h

@[simp]
/-
**Set.einfsep_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_empty : (∅ : Set α).einfsep = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.einfsep`：∀ {α : Type u_1} [inst : EDist α] {s : Set α},
 s.Subsingleton → s.einfsep = ⊤
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem einfsep_empty : (∅ : Set α).einfsep = ∞ :=
  subsingleton_empty.einfsep

@[simp]
/-
**Set.einfsep_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_singleton : ({x} : Set α).einfsep = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.einfsep`：∀ {α : Type u_1} [inst : EDist α] {s : Set α},
 s.Subsingleton → s.einfsep = ⊤
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem einfsep_singleton : ({x} : Set α).einfsep = ∞ :=
  subsingleton_singleton.einfsep
/-
**Set.einfsep_iUnion_mem_option** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι -> Set α) : (⋃
 i in o, s i).einfsep = ⨅ i in o, (s i).einfsep
参数：o : Option ι；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.einfsep_empty`：einfsep_empty : (∅ : Set α).einfsep = ∞
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `iInf_iInf_eq_right`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatt
ice α] {b : β} {f : (x : β) → b = x → α},   ⨅ x, ⨅ (h : b = x), f x h = f b ⋯
-/
theorem einfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set α) :
    (⋃ i ∈ o, s i).einfsep = ⨅ i ∈ o, (s i).einfsep := by cases o <;> simp
/-
**Set.einfsep_anti** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_anti (hst : s subseteq t) : t.einfsep <= s.einfsep
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_einfsep`：le_einfsep {d} (h : forall x in s, forall y in s, x != y
 -> d <= edist x y) : d <= s.einfsep
· 使用定理 `Set.einfsep_le_edist_of_mem`：einfsep_le_edist_of_mem {x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) : s.einfsep <= edist x y
-/
theorem einfsep_anti (hst : s ⊆ t) : t.einfsep ≤ s.einfsep :=
  le_einfsep fun _x hx _y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)
/-
**Set.einfsep_insert_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_insert_le : (insert x s).einfsep <= ⨅ (y in s) (_ : x != y), edist
 x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.einfsep_le_edist_of_mem`：einfsep_le_edist_of_mem {x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) : s.einfsep <= edist x y
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
-/
theorem einfsep_insert_le : (insert x s).einfsep ≤ ⨅ (y ∈ s) (_ : x ≠ y), edist x y := by
  simp_rw [le_iInf_iff]
  exact fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
/-
**Set.le_einfsep_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep_pair : edist x y ⊓ edist y x <= ({x, y} : Set α).einfsep
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem le_einfsep_pair : edist x y ⊓ edist y x ≤ ({x, y} : Set α).einfsep := by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction
/-
**Set.einfsep_pair_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pair_le_left (hxy : x != y) : ({x, y} : Set α).einfsep <= edist x 
y
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.einfsep_le_edist_of_mem`：einfsep_le_edist_of_mem {x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) : s.einfsep <= edist x y
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem einfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist x y :=
  einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy
/-
**Set.einfsep_pair_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pair_le_right (hxy : x != y) : ({x, y} : Set α).einfsep <= edist y
 x
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Set.einfsep_pair_le_left`：einfsep_pair_le_left (hxy : x != y) : ({x, y} 
: Set α).einfsep <= edist x y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem einfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist y x := by
  rw [pair_comm]; exact einfsep_pair_le_left hxy.symm
/-
**Set.einfsep_pair_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pair_eq_inf (hxy : x != y) : ({x, y} : Set α).einfsep = edist x y 
⊓ edist y x
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Set.einfsep_pair_le_left`：einfsep_pair_le_left (hxy : x != y) : ({x, y} 
: Set α).einfsep <= edist x y
· 使用定理 `Set.einfsep_pair_le_right`：einfsep_pair_le_right (hxy : x != y) : ({x, y
} : Set α).einfsep <= edist y x
· 使用定理 `Set.le_einfsep_pair`：le_einfsep_pair : edist x y ⊓ edist y x <= ({x, y} 
: Set α).einfsep
-/
theorem einfsep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y ⊓ edist y x :=
  le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair
/-
**Set.einfsep_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]
/-
**Set.einfsep_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_of_fintype [Fintype s] : s.einfsep = s.offDiag.toFinset.inf (uncur
ry edist)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem einfsep_of_fintype [Fintype s] : s.einfsep = s.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]
/-
**Set.Finite.einfsep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Set α} (hs : s.Finite), s.einfsep =
 ⋯.toFinset.inf (Function.uncurry edist)
参数：hs : s.Finite；Function.uncurry edist。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Set.Finite.offDiag`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.offDiag.F
inite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Finite.einfsep (hs : s.Finite) : s.einfsep = hs.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]
/-
**Set.Finset.coe_einfsep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finset`。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Finset α}, (↑s).einfsep = s.offDiag
.inf (Function.uncurry edist)
参数：↑s；Function.uncurry edist。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.einfsep_of_fintype`：einfsep_of_fintype [Fintype s] : s.einfsep = s.o
ffDiag.toFinset.inf (uncurry edist)
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finset.coe_einfsep {s : Finset α} :
    (s : Set α).einfsep = s.offDiag.inf (uncurry edist) := by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
/-
**Set.Nontrivial.einfsep_exists_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontriv
ial`。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Set α} [Finite ↑s],   s.Nontrivial 
→ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.einfsep_of_fintype`：einfsep_of_fintype [Fintype s] : s.einfsep = s.o
ffDiag.toFinset.inf (uncurry edist)
· 使用定理 `Finset.exists_mem_eq_inf`：∀ {α : Type u_2} {ι : Type u_5} [inst : Linear
Order α] [inst_1 : OrderTop α] (s : Finset ι),   s.Nonempty → ∀ (f : ι → α), ∃ i
 ∈ s, s.inf f …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nontrivial.einfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y := by
  cases nonempty_fintype s
  simp_rw [einfsep_of_fintype]
  rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
/-
**Set.Finite.einfsep_exists_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`
。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Set α}, s.Finite → s.Nontrivial → ∃
 x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.einfsep_exists_of_finite`：∀ {α : Type u_1} [inst : EDist 
α] {s : Set α} [Finite ↑s],   s.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep
 = edist x y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.einfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y :=
  letI := hsf.fintype
  hs.einfsep_exists_of_finite

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s : Set α}

/-
**Set.einfsep_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pair (hxy : x != y) : ({x, y} : Set α).einfsep = edist x y
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Set.einfsep_pair_eq_inf`：einfsep_pair_eq_inf (hxy : x != y) : ({x, y} : 
Set α).einfsep = edist x y ⊓ edist y x
-/
theorem einfsep_pair (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y := by
  nth_rw 1 [← min_self (edist x y)]
  convert! einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]
/-
**Set.einfsep_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_insert : einfsep (insert x s) = (⨅ (y in s) (_ : x != y), edist x 
y) ⊓ s.einfsep
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Set.einfsep_insert_le`：einfsep_insert_le : (insert x s).einfsep <= ⨅ (y 
in s) (_ : x != y), edist x y
· 使用定理 `Set.einfsep_anti`：einfsep_anti (hst : s subseteq t) : t.einfsep <= s.ein
fsep
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.einfsep_le_edist_of_mem`：einfsep_le_edist_of_mem {x} (hx : x in s) {
y} (hy : y in s) (hxy : x != y) : s.einfsep <= edist x y
-/
theorem einfsep_insert : einfsep (insert x s) =
    (⨅ (y ∈ s) (_ : x ≠ y), edist x y) ⊓ s.einfsep := by
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) ?_
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (einfsep_le_edist_of_mem hy hz hyz)
/-
**Set.einfsep_triple** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_triple (hxy : x != y) (hyz : y != z) (hxz : x != z) : einfsep ({x,
 y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z
参数：hxy : x != y；hyz : y != z；hxz : x != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.einfsep_insert`：einfsep_insert : einfsep (insert x s) = (⨅ (y in s) 
(_ : x != y), edist x y) ⊓ s.einfsep
· 使用定理 `iInf_insert`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{f : β → α} {s : Set β} {b : β},   ⨅ x ∈ insert b s, f x = f b ⊓ ⨅ x ∈ s, f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iInf_singleton`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice 
α] {f : β → α} {b : β}, ⨅ x ∈ {b}, f x = f b
· 使用定理 `Set.einfsep_singleton`：einfsep_singleton : ({x} : Set α).einfsep = ∞
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `ciInf_pos`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderInf
 α] {p : Prop} {f : p → α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem einfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]
/-
**Set.le_einfsep_pi_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep_pi_of_le {X : β -> Type*} [Fintype β] [forall b, PseudoEMetricS
pace (X b)] {s : forall b : β, Set (X b)} {c : Real>=0∞} (h : forall b, c <= ein
fsep (s b)) : c <= einfsep (Set.pi univ s)
参数：X b；X b；h : forall b, c <= einfsep (s b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_einfsep`：le_einfsep {d} (h : forall x in s, forall y in s, x != y
 -> d <= edist x y) : d <= s.einfsep
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.le_einfsep_iff`：le_einfsep_iff {d} : d <= s.einfsep ↔ forall x in s,
 forall y in s, x != y -> d <= edist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `edist_le_pi_edist`：edist_le_pi_edist [forall b, EDist (X b)] (f g : fora
ll b, X b) (b : β) : edist (f b) (g b) <= edist f g
-/
theorem le_einfsep_pi_of_le {X : β → Type*} [Fintype β] [∀ b, PseudoEMetricSpace (X b)]
    {s : ∀ b : β, Set (X b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ einfsep (s b)) :
    c ≤ einfsep (Set.pi univ s) := by
  refine le_einfsep fun x hx y hy hxy => ?_
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

/-
**Set.subsingleton_of_einfsep_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton
参数：hs : s.einfsep = ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.einfsep_top`：einfsep_top : s.einfsep = ∞ ↔ forall x in s, forall y i
n s, x != y -> edist x y = ∞
-/
theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton := by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)
/-
**Set.einfsep_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_einfsep_eq_top`：subsingleton_of_einfsep_eq_top (hs :
 s.einfsep = ∞) : s.Subsingleton
· 使用定理 `Set.Subsingleton.einfsep`：∀ {α : Type u_1} [inst : EDist α] {s : Set α},
 s.Subsingleton → s.einfsep = ⊤
-/
theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton :=
  ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩
/-
**Set.Nontrivial.einfsep_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α}, s.Nontrivial → 
s.einfsep ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.subsingleton_of_einfsep_eq_top`：subsingleton_of_einfsep_eq_top (hs :
 s.einfsep = ∞) : s.Subsingleton
-/
theorem Nontrivial.einfsep_ne_top (hs : s.Nontrivial) : s.einfsep ≠ ∞ := by
  contrapose! hs
  exact subsingleton_of_einfsep_eq_top hs
/-
**Set.Nontrivial.einfsep_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α}, s.Nontrivial → 
s.einfsep < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Set.Nontrivial.einfsep_ne_top`：∀ {α : Type u_1} [inst : PseudoMetricSpac
e α] {s : Set α}, s.Nontrivial → s.einfsep ≠ ⊤
-/
theorem Nontrivial.einfsep_lt_top (hs : s.Nontrivial) : s.einfsep < ∞ := by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top
/-
**Set.einfsep_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_einfsep_lt_top`：nontrivial_of_einfsep_lt_top (hs : s.e
infsep < ∞) : s.Nontrivial
· 使用定理 `Set.Nontrivial.einfsep_lt_top`：∀ {α : Type u_1} [inst : PseudoMetricSpac
e α] {s : Set α}, s.Nontrivial → s.einfsep < ⊤
-/
theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩
/-
**Set.einfsep_ne_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_ne_top_iff : s.einfsep != ∞ ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_einfsep_ne_top`：nontrivial_of_einfsep_ne_top (hs : s.e
infsep != ∞) : s.Nontrivial
· 使用定理 `Set.Nontrivial.einfsep_ne_top`：∀ {α : Type u_1} [inst : PseudoMetricSpac
e α] {s : Set α}, s.Nontrivial → s.einfsep ≠ ⊤
-/
theorem einfsep_ne_top_iff : s.einfsep ≠ ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩
/-
**Set.le_einfsep_of_forall_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_einfsep_of_forall_dist_le {d} (h : forall x in s, forall y in s, x != y
 -> d <= dist x y) : ENNReal.ofReal d <= s.einfsep
参数：h : forall x in s, forall y in s, x != y -> d <= dist x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_einfsep`：le_einfsep {d} (h : forall x in s, forall y in s, x != y
 -> d <= edist x y) : d <= s.einfsep
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
-/
theorem le_einfsep_of_forall_dist_le {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) :
    ENNReal.ofReal d ≤ s.einfsep :=
  le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {s : Set α}

/-
**Set.einfsep_pos_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：einfsep_pos_of_finite [Finite s] : 0 < s.einfsep
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Set.Nontrivial.einfsep_exists_of_finite`：∀ {α : Type u_1} [inst : EDist 
α] {s : Set α} [Finite ↑s],   s.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep
 = edist x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `edist_pos`：edist_pos {x y : γ} : 0 < edist x y ↔ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.top_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α], 0 < ⊤
· 使用定理 `Set.Subsingleton.einfsep`：∀ {α : Type u_1} [inst : EDist α] {s : Set α},
 s.Subsingleton → s.einfsep = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
theorem einfsep_pos_of_finite [Finite s] : 0 < s.einfsep := by
  cases nonempty_fintype s
  by_cases hs : s.Nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, _hx, y, _hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.top_pos
/-
**Set.relatively_discrete_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：relatively_discrete_of_finite [Finite s] : exists C > 0, forall x in s, fo
rall y in s, x != y -> C <= edist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.einfsep_pos`：einfsep_pos : 0 < s.einfsep ↔ exists C > 0, forall x in
 s, forall y in s, x != y -> C <= edist x y
· 使用定理 `Set.einfsep_pos_of_finite`：einfsep_pos_of_finite [Finite s] : 0 < s.einf
sep
-/
theorem relatively_discrete_of_finite [Finite s] :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite
/-
**Set.Finite.einfsep_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : EMetricSpace α] {s : Set α}, s.Finite → 0 < s.ein
fsep
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.einfsep_pos_of_finite`：einfsep_pos_of_finite [Finite s] : 0 < s.einf
sep
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.einfsep_pos (hs : s.Finite) : 0 < s.einfsep :=
  letI := hs.fintype
  einfsep_pos_of_finite
/-
**Set.Finite.relatively_discrete** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : EMetricSpace α] {s : Set α}, s.Finite → ∃ C > 0, 
∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.relatively_discrete_of_finite`：relatively_discrete_of_finite [Finite
 s] : exists C > 0, forall x in s, forall y in s, x != y -> C <= edist x y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.relatively_discrete (hs : s.Finite) :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y :=
  letI := hs.fintype
  relatively_discrete_of_finite

end EMetricSpace

end Einfsep

section Infsep

open ENNReal

open Set Function

/-- The "infimum separation" of a set with an edist function. -/
/-
**Set.infsep** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：infsep [EDist α] (s : Set α) : Real
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "infimum separation" of a set with an edist function.
-/
noncomputable def infsep [EDist α] (s : Set α) : ℝ :=
  ENNReal.toReal s.einfsep

section EDist

variable [EDist α] {x y : α} {s : Set α}

/-
**Set.infsep_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep.eq_1`：∀ {α : Type u_1} [inst : EDist α] (s : Set α), s.infsep
 = s.einfsep.toReal
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ := by
  rw [infsep, ENNReal.toReal_eq_zero_iff]
/-
**Set.infsep_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_nonneg : 0 <= s.infsep
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem infsep_nonneg : 0 ≤ s.infsep :=
  ENNReal.toReal_nonneg
/-
**Set.infsep_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ := by
  simp_rw [infsep, ENNReal.toReal_pos_iff]
/-
**Set.Subsingleton.infsep_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : EDist α] {s : Set α}, s.Subsingleton → s.infsep =
 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infsep_zero`：infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep 
= ∞
· 使用定理 `Set.Subsingleton.einfsep`：∀ {α : Type u_1} [inst : EDist α] {s : Set α},
 s.Subsingleton → s.einfsep = ⊤
-/
theorem Subsingleton.infsep_zero (hs : s.Subsingleton) : s.infsep = 0 :=
  Set.infsep_zero.mpr <| Or.inr hs.einfsep
/-
**Set.nontrivial_of_infsep_pos** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial
参数：hs : 0 < s.infsep。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
theorem nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial := by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _
/-
**Set.infsep_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_empty : (∅ : Set α).infsep = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem infsep_empty : (∅ : Set α).infsep = 0 :=
  subsingleton_empty.infsep_zero
/-
**Set.infsep_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_singleton : ({x} : Set α).infsep = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem infsep_singleton : ({x} : Set α).infsep = 0 :=
  subsingleton_singleton.infsep_zero
/-
**Set.infsep_pair_le_toReal_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_pair_le_toReal_inf (hxy : x != y) : ({x, y} : Set α).infsep <= (edi
st x y ⊓ edist y x).toReal
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.einfsep_pair_eq_inf`：einfsep_pair_eq_inf (hxy : x != y) : ({x, y} : 
Set α).einfsep = edist x y ⊓ edist y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem infsep_pair_le_toReal_inf (hxy : x ≠ y) :
    ({x, y} : Set α).infsep ≤ (edist x y ⊓ edist y x).toReal := by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
  simp

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α}

/-
**Set.infsep_pair_eq_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.pair_eq_singleton`：pair_eq_singleton (a : α) : ({a, a} : Set α) = {a
}
· 使用定理 `Set.infsep_singleton`：infsep_singleton : ({x} : Set α).infsep = 0
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.infsep.eq_1`：∀ {α : Type u_1} [inst : EDist α] (s : Set α), s.infsep
 = s.einfsep.toReal
· 使用定理 `Set.einfsep_pair`：einfsep_pair (hxy : x != y) : ({x, y} : Set α).einfsep
 = edist x y
-/
theorem infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal := by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.toReal_zero]
  · rw [infsep, einfsep_pair hxy]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

/-
**Set.Nontrivial.le_infsep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} {d : ℝ},   s.Non
trivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y)
参数：d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
· 使用定理 `Set.Nontrivial.einfsep_ne_top`：∀ {α : Type u_1} [inst : PseudoMetricSpac
e α] {s : Set α}, s.Nontrivial → s.einfsep ≠ ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nontrivial.le_infsep_iff {d} (hs : s.Nontrivial) :
    d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y := by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]
/-
**Set.Nontrivial.infsep_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} {d : ℝ},   s.Non
trivial → (s.infsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d)
参数：s.infsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d。
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
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
-/
theorem Nontrivial.infsep_lt_iff {d} (hs : s.Nontrivial) :
    s.infsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d := by
  contrapose!; exact hs.le_infsep_iff
/-
**Set.Nontrivial.le_infsep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} {d : ℝ},   s.Non
trivial → (∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) → d ≤ s.infsep
参数：∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
-/
theorem Nontrivial.le_infsep {d} (hs : s.Nontrivial)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) : d ≤ s.infsep :=
  hs.le_infsep_iff.2 h
/-
**Set.le_edist_of_le_infsep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_edist_of_le_infsep {d x} (hx : x in s) {y} (hy : y in s) (hxy : x != y)
 (hd : d <= s.infsep) : d <= dist x y
参数：hx : x in s；hy : y in s；hxy : x != y；hd : d <= s.infsep。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.infsep) : d ≤ dist x y := by
  by_cases hs : s.Nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg
/-
**Set.infsep_le_dist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_le_dist_of_mem (hx : x in s) (hy : y in s) (hxy : x != y) : s.infse
p <= dist x y
参数：hx : x in s；hy : y in s；hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.le_edist_of_le_infsep`：le_edist_of_le_infsep {d x} (hx : x in s) {y}
 (hy : y in s) (hxy : x != y) (hd : d <= s.infsep) : d <= dist x y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infsep ≤ dist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl
/-
**Set.infsep_le_of_mem_of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_le_of_mem_of_edist_le {d x} (hx : x in s) {y} (hy : y in s) (hxy : 
x != y) (hxy' : dist x y <= d) : s.infsep <= d
参数：hx : x in s；hy : y in s；hxy : x != y；hxy' : dist x y <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.infsep_le_dist_of_mem`：infsep_le_dist_of_mem (hx : x in s) (hy : y i
n s) (hxy : x != y) : s.infsep <= dist x y
-/
theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : dist x y ≤ d) : s.infsep ≤ d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'
/-
**Set.infsep_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_pair : ({x, y} : Set α).infsep = dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep_pair_eq_toReal`：infsep_pair_eq_toReal : ({x, y} : Set α).infs
ep = (edist x y).toReal
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem infsep_pair : ({x, y} : Set α).infsep = dist x y := by
  rw [infsep_pair_eq_toReal, edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg
/-
**Set.infsep_triple** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_triple (hxy : x != y) (hyz : y != z) (hxz : x != z) : ({x, y, z} : 
Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z
参数：hxy : x != y；hyz : y != z；hxz : x != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.einfsep_triple`：einfsep_triple (hxy : x != y) (hyz : y != z) (hxz : 
x != z) : einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z
· 使用定理 `ENNReal.toReal_inf`：toReal_inf {a b : Real>=0∞} : a != ∞ -> b != ∞ -> (a
 ⊓ b).toReal = a.toReal ⊓ b.toReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z := by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne, inf_eq_top_iff, and_self_iff,
    not_false_iff]
/-
**Set.Nontrivial.infsep_anti** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s t : Set α}, s.Nontrivial 
→ s ⊆ t → t.infsep ≤ s.infsep
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Set.Nontrivial.einfsep_ne_top`：∀ {α : Type u_1} [inst : PseudoMetricSpac
e α] {s : Set α}, s.Nontrivial → s.einfsep ≠ ⊤
· 使用定理 `Set.einfsep_anti`：einfsep_anti (hst : s subseteq t) : t.einfsep <= s.ein
fsep
-/
theorem Nontrivial.infsep_anti (hs : s.Nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep :=
  ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)
/-
**Set.infsep_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_eq_iInf [Decidable s.Nontrivial] : s.infsep = if s.Nontrivial then 
⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
· 使用定理 `le_ciInf_set_iff`：le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι -> α} 
{a : α} (hs : s.Nonempty) (hf : BddBelow (f '' s)) : (a <= ⨅ i : s, f i) ↔ foral
l i in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.offDiag_nonempty`：offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivi
al
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
theorem infsep_eq_iInf [Decidable s.Nontrivial] :
    s.infsep = if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0 := by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.offDiag) := by
      refine ⟨0, fun d h => ?_⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, le_ciInf_set_iff (offDiag_nonempty.mpr hs) hb, imp_forall_iff,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · exact (not_nontrivial_iff.mp hs).infsep_zero
/-
**Set.Nontrivial.infsep_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α}, s.Nontrivial → 
s.infsep = ⨅ d, Function.uncurry dist ↑d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep_eq_iInf`：infsep_eq_iInf [Decidable s.Nontrivial] : s.infsep =
 if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem Nontrivial.infsep_eq_iInf (hs : s.Nontrivial) :
    s.infsep = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by
  classical rw [Set.infsep_eq_iInf, if_pos hs]
/-
**Set.infsep_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_of_fintype [Decidable s.Nontrivial] [Fintype s] : s.infsep = if hs 
: s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
theorem infsep_of_fintype [Decidable s.Nontrivial] [Fintype s] : s.infsep =
    if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_toFinset, mem_offDiag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero
/-
**Set.Nontrivial.infsep_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} [inst_1 : Fintyp
e ↑s] (hs : s.Nontrivial),   s.infsep = s.offDiag.toFinset.inf' ⋯ (Function.uncu
rry dist)
参数：hs : s.Nontrivial；Function.uncurry dist。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep_of_fintype`：infsep_of_fintype [Decidable s.Nontrivial] [Finty
pe s] : s.infsep = if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) 
(uncurry di…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem Nontrivial.infsep_of_fintype [Fintype s] (hs : s.Nontrivial) :
    s.infsep = s.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical rw [Set.infsep_of_fintype, dif_pos hs]
/-
**Set.Finite.infsep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} [inst_1 : Decida
ble s.Nontrivial] (hsf : s.Finite),   s.infsep = if hs : s.Nontrivial then ⋯.toF
inset.inf' ⋯ (Function.uncurry dist) else 0
参数：hsf : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Set.Finite.offDiag`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.offDiag.F
inite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nontrivial.le_infsep_iff`：∀ {α : Type u_1} [inst : PseudoMetricSpace
 α] {s : Set α} {d : ℝ},   s.Nontrivial → (d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ 
y → d ≤ dist x y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.Subsingleton.infsep_zero`：∀ {α : Type u_1} [inst : EDist α] {s : Set
 α}, s.Subsingleton → s.infsep = 0
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
theorem Finite.infsep [Decidable s.Nontrivial] (hsf : s.Finite) :
    s.infsep =
      if hs : s.Nontrivial then hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, Finite.mem_toFinset,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero
/-
**Set.Finite.infsep_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} (hsf : s.Finite)
 (hs : s.Nontrivial),   s.infsep = ⋯.toFinset.inf' ⋯ (Function.uncurry dist)
参数：hsf : s.Finite；hs : s.Nontrivial；Function.uncurry dist。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Set.Finite.offDiag`：∀ {α : Type u_1} {s : Set α}, s.Finite → s.offDiag.F
inite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.infsep`：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Se
t α} [inst_1 : Decidable s.Nontrivial] (hsf : s.Finite),   s.infsep = if hs : s.
Nontriv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finite.infsep_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    s.infsep = hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical simp_rw [hsf.infsep, dif_pos hs]
/-
**Set._root_.Finset.coe_infsep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.coe_infsep (s : Finset α) : (s : Set α).infsep =
    if hs : s.offDiag.Nonempty then s.offDiag.inf' hs (uncurry dist) else 0 := by
  have H : (s : Set α).Nontrivial ↔ s.offDiag.Nonempty := by
    rw [← Set.offDiag_nonempty, ← Finset.coe_offDiag, Finset.coe_nonempty]
  split_ifs with hs
  · classical simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H.mp.mt hs)).infsep_zero
/-
**Set._root_.Finset.coe_infsep_of_offDiag_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Se
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.coe_infsep_of_offDiag_nonempty {s : Finset α}
    (hs : s.offDiag.Nonempty) : (s : Set α).infsep = s.offDiag.inf' hs (uncurry dist) := by
  rw [Finset.coe_infsep, dif_pos hs]
/-
**Set._root_.Finset.coe_infsep_of_offDiag_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.coe_infsep_of_offDiag_empty
    {s : Finset α} (hs : s.offDiag = ∅) : (s : Set α).infsep = 0 := by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep, dif_neg hs]
/-
**Set.Nontrivial.infsep_exists_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivi
al`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α} [Finite ↑s],   s
.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nontrivial.infsep_of_fintype`：∀ {α : Type u_1} [inst : PseudoMetricS
pace α] {s : Set α} [inst_1 : Fintype ↑s] (hs : s.Nontrivial),   s.infsep = s.of
fDiag.toFinset.inf' ⋯ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.exists_mem_eq_inf'`：∀ {α : Type u_2} {ι : Type u_5} [inst : Linea
rOrder α] {s : Finset ι} (H : s.Nonempty) (f : ι → α),   ∃ i ∈ s, s.inf' H f = f
 i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nontrivial.infsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y := by
  cases nonempty_fintype s
  simp_rw [hs.infsep_of_fintype]
  rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
    ⟨w, hxy, hed⟩
  simp_rw [mem_toFinset] at hxy
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
/-
**Set.Finite.infsep_exists_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {s : Set α},   s.Finite → s.
Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.infsep_exists_of_finite`：∀ {α : Type u_1} [inst : PseudoM
etricSpace α] {s : Set α} [Finite ↑s],   s.Nontrivial → ∃ x ∈ s, ∃ y ∈ s, x ≠ y 
∧ s.infsep = dist x y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.infsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y :=
  letI := hsf.fintype
  hs.infsep_exists_of_finite

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

/-
**Set.infsep_zero_iff_subsingleton_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsi
ngleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep_zero`：infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep 
= ∞
· 使用定理 `Set.einfsep_eq_top_iff`：einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingle
ton
· 使用定理 `or_iff_right_iff_imp`：∀ {a b : Prop}, (a ∨ b ↔ b) ↔ a → b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.einfsep_pos_of_finite`：einfsep_pos_of_finite [Finite s] : 0 < s.einf
sep
-/
theorem infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton := by
  rw [infsep_zero, einfsep_eq_top_iff, or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim
/-
**Set.infsep_pos_iff_nontrivial_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivi
al
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infsep_pos`：infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < 
∞
· 使用定理 `Set.einfsep_lt_top_iff`：einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivia
l
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `Set.einfsep_pos_of_finite`：einfsep_pos_of_finite [Finite s] : 0 < s.einf
sep
-/
theorem infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial := by
  rw [infsep_pos, einfsep_lt_top_iff, and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite
/-
**Set.Finite.infsep_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`
。
形式化陈述：∀ {α : Type u_1} [inst : MetricSpace α] {s : Set α}, s.Finite → (s.infsep 
= 0 ↔ s.Subsingleton)
参数：s.infsep = 0 ↔ s.Subsingleton。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infsep_zero_iff_subsingleton_of_finite`：infsep_zero_iff_subsingleton
_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.infsep_zero_iff_subsingleton (hs : s.Finite) : s.infsep = 0 ↔ s.Subsingleton :=
  letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite
/-
**Set.Finite.infsep_pos_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_1} [inst : MetricSpace α] {s : Set α}, s.Finite → (0 < s.inf
sep ↔ s.Nontrivial)
参数：0 < s.infsep ↔ s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infsep_pos_iff_nontrivial_of_finite`：infsep_pos_iff_nontrivial_of_fi
nite [Finite s] : 0 < s.infsep ↔ s.Nontrivial
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial :=
  letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite
/-
**Set._root_.Finset.infsep_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    (s : Set α).infsep = 0 ↔ (s : Set α).Subsingleton :=
  infsep_zero_iff_subsingleton_of_finite
/-
**Set._root_.Finset.infsep_pos_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < (s : Set α).infsep ↔ (s : Set α).Nontrivial :=
  infsep_pos_iff_nontrivial_of_finite

end MetricSpace

end Infsep

end Set

