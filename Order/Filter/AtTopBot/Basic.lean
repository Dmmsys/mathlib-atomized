/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Subsingleton

/-!
# Basic results on `Filter.atTop` and `Filter.atBot` filters

In this file we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

section IsDirected
variable [Preorder α] [IsDirectedOrder α] {p : α → Prop}

-- `Filter.HasMonotoneBasis` doesn't exist, so we cannot use `to_dual` here.
/-
**Filter.hasAntitoneBasis_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasAntitoneBasis.iInf_principal`：∀ {α : Type u_1} {ι : Type u_7} 
[inst : Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {s : ι → Set α},   Antitone
 s → (⨅ i, Filter.principal …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
-/
theorem hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici :=
  .iInf_principal fun _ _ ↦ Ici_subset_Ici.2
/-
**Filter.atTop_basis** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Filter.hasAntitoneBasis_atTop`：hasAntitoneBasis_atTop [Nonempty α] : (@a
tTop α _).HasAntitoneBasis Ici
-/
theorem atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici :=
  hasAntitoneBasis_atTop.1

@[to_dual existing]
/-
**Filter.atBot_basis** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α] : 
(@atBot α _).HasBasis (fun _ => True) Iic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
lemma atBot_basis {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α] :
    (@atBot α _).HasBasis (fun _ => True) Iic := atTop_basis (α := αᵒᵈ)

@[to_dual]
/-
**Filter.atTop_basis_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _
 => True) Ioi
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
lemma atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _ => True) Ioi :=
  atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

@[to_dual]
/-
**Filter.atTop_basis_Ioi'** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `trivial`：True
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

@[to_dual]
/-
**Filter.atTop_basis'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_basis' (a : α) : atTop.HasBasis (a <= ·) Ici
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `trivial`：True
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem atTop_basis' (a : α) : atTop.HasBasis (a ≤ ·) Ici := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

variable [Nonempty α]

@[to_dual]
/-
**Filter.atTop_neBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：atTop_neBot : NeBot (atTop : Filter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
-/
instance atTop_neBot : NeBot (atTop : Filter α) := atTop_basis.neBot_iff.2 fun _ => nonempty_Ici

@[to_dual]
/-
**Filter.atTop_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_neBot_iff {α : Type*} [Preorder α] : (atTop : Filter α).NeBot ↔ None
mpty α ∧ IsDirectedOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_neBot`：nonempty_of_neBot (f : Filter α) [NeBot f] : N
onempty α
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
theorem atTop_neBot_iff {α : Type*} [Preorder α] :
    (atTop : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α := by
  refine ⟨fun h ↦ ⟨nonempty_of_neBot atTop, ⟨fun x y ↦ ?_⟩⟩, fun ⟨h₁, h₂⟩ ↦ atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists

@[to_dual (attr := simp)]
/-
**Filter.mem_atTop_sets** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：mem_atTop_sets {s : Set α} : s in (atTop : Filter α) ↔ exists a : α, foral
l b, a <= b -> b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma mem_atTop_sets {s : Set α} : s ∈ (atTop : Filter α) ↔ ∃ a : α, ∀ b, a ≤ b → b ∈ s :=
  atTop_basis.mem_iff.trans <| exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]
/-
**Filter.eventually_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventually_atTop : (forallᶠ x in atTop, p x) ↔ exists a, forall b, a <= b 
-> p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
-/
lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b := mem_atTop_sets

@[to_dual]
/-
**Filter.frequently_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_atTop : (existsᶠ x in atTop, p x) ↔ forall a, exists b, a <= b 
∧ p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b, a ≤ b ∧ p b :=
  atTop_basis.frequently_iff.trans <| by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

-- `to_dual` cannot translate `forall_ge_iff`
/-
**Filter.exists_eventually_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：exists_eventually_atTop {r : α -> β -> Prop} : (exists b, forallᶠ a in atT
op, r a b) ↔ forallᶠ a₀ in atTop, exists b, forall a, a₀ <= a -> r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `forall_ge_iff`：forall_ge_iff {P : α -> Prop} {x₀ : α} (hP : Monotone P) 
: (forall x >= x₀, P x) ↔ P x₀
· 使用定理 `Monotone.exists`：Monotone.exists {P : β -> α -> Prop} (hP : forall x, Mo
notone (P x)) : Monotone fun y => exists x, P x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma exists_eventually_atTop {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atTop, r a b) ↔ ∀ᶠ a₀ in atTop, ∃ b, ∀ a, a₀ ≤ a → r a b := by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
  exact exists_congr fun a ↦ .symm <| forall_ge_iff <| Monotone.exists fun _ _ _ hb H n hn ↦
    H n (hb.trans hn)

@[to_dual existing]
/-
**Filter.exists_eventually_atBot** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：exists_eventually_atBot {α : Type*} [Preorder α] [IsCodirectedOrder α] [No
nempty α] {r : α -> β -> Prop} : (exists b, forallᶠ a in atBot, r a b) ↔ forallᶠ
 a₀ in atBot, exists b, forall a <= a₀, r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.exists_eventually_atTop`：exists_eventually_atTop {r : α -> β -> P
rop} : (exists b, forallᶠ a in atTop, r a b) ↔ forallᶠ a₀ in atTop, exists b, fo
rall a, a₀ <= a -> r…
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
lemma exists_eventually_atBot {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
    {r : α → β → Prop} : (∃ b, ∀ᶠ a in atBot, r a b) ↔ ∀ᶠ a₀ in atBot, ∃ b, ∀ a ≤ a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]
/-
**Filter.map_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_atTop_eq {f : α -> β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a <= a' })
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_iInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{s : ι → Set α},   l.HasBasis (fun x => True) s → l = ⨅ i, Filter.principal (s i
)
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
-/
theorem map_atTop_eq {f : α → β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a ≤ a' }) :=
  (atTop_basis.map f).eq_iInf

@[to_dual]
/-
**Filter.frequently_atTop'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_atTop' [NoMaxOrder α] : (existsᶠ x in atTop, p x) ↔ forall a, e
xists b > a, p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_atTop' [NoMaxOrder α] : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b > a, p b :=
  atTop_basis_Ioi.frequently_iff.trans <| by simp

end IsDirected

/-!
### Sequences
-/

/-
**Filter.extraction_of_frequently_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：extraction_of_frequently_atTop {P : Nat -> Prop} (h : existsᶠ n in atTop, 
P n) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n)
参数：h : existsᶠ n in atTop, P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono_subsequence`：exists_strictMono_subsequence {P : Na
t -> Prop} (h : forall N, exists n > N, P n) : exists φ : Nat -> Nat, StrictMono
 φ ∧ forall n, P (φ n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_atTop'`：frequently_atTop' [NoMaxOrder α] : (existsᶠ x 
in atTop, p x) ↔ forall a, exists b > a, p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
### Sequences
-/
theorem extraction_of_frequently_atTop {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  rw [frequently_atTop'] at h
  exact Nat.exists_strictMono_subsequence h
/-
**Filter.extraction_of_eventually_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：extraction_of_eventually_atTop {P : Nat -> Prop} (h : forallᶠ n in atTop, 
P n) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P (φ n)
参数：h : forallᶠ n in atTop, P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_of_frequently_atTop`：extraction_of_frequently_atTop {P
 : Nat -> Prop} (h : existsᶠ n in atTop, P n) : exists φ : Nat -> Nat, StrictMon
o φ ∧ forall n, P (φ n)
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem extraction_of_eventually_atTop {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) :=
  extraction_of_frequently_atTop h.frequently
/-
**Filter.extraction_forall_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：extraction_forall_of_frequently {P : Nat -> Nat -> Prop} (h : forall n, ex
istsᶠ k in atTop, P n k) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P n (
φ n)
参数：h : forall n, existsᶠ k in atTop, P n k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem extraction_forall_of_frequently {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) := by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : ℕ → ℕ)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']
/-
**Filter.extraction_forall_of_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：extraction_forall_of_eventually {P : Nat -> Nat -> Prop} (h : forall n, fo
rallᶠ k in atTop, P n k) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n, P n (
φ n)
参数：h : forall n, forallᶠ k in atTop, P n k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_forall_of_frequently`：extraction_forall_of_frequently 
{P : Nat -> Nat -> Prop} (h : forall n, existsᶠ k in atTop, P n k) : exists φ : 
Nat -> Nat, StrictMono φ ∧ f…
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem extraction_forall_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_frequently fun n => (h n).frequently
/-
**Filter.extraction_forall_of_eventually'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：extraction_forall_of_eventually' {P : Nat -> Nat -> Prop} (h : forall n, e
xists N, forall k >= N, P n k) : exists φ : Nat -> Nat, StrictMono φ ∧ forall n,
 P n (φ n)
参数：h : forall n, exists N, forall k >= N, P n k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_forall_of_eventually`：extraction_forall_of_eventually 
{P : Nat -> Nat -> Prop} (h : forall n, forallᶠ k in atTop, P n k) : exists φ : 
Nat -> Nat, StrictMono φ ∧ f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem extraction_forall_of_eventually' {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ N, ∀ k ≥ N, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_eventually (by simp [eventually_atTop, h])

section IsDirected
variable [Preorder α] [IsDirectedOrder α] {F : Filter β} {u : α → β}

@[to_dual inf_map_atBot_neBot_iff]
/-
**Filter.inf_map_atTop_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：inf_map_atTop_neBot_iff [Nonempty α] : NeBot (F ⊓ map u atTop) ↔ forall U 
in F, forall N, exists n, N <= n ∧ u n in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_map_atTop_neBot_iff [Nonempty α] :
    NeBot (F ⊓ map u atTop) ↔ ∀ U ∈ F, ∀ N, ∃ n, N ≤ n ∧ u n ∈ U := by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl

variable [Preorder β]

@[to_dual (dont_translate := α)]
/-
**Filter.exists_le_of_tendsto_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：exists_le_of_tendsto_atTop (h : Tendsto u atTop atTop) (a : α) (b : β) : e
xists a', a <= a' ∧ b <= u a'
参数：h : Tendsto u atTop atTop；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
-/
lemma exists_le_of_tendsto_atTop (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a', a ≤ a' ∧ b ≤ u a' := by
  have : Nonempty α := ⟨a⟩
  have : ∀ᶠ x in atTop, a ≤ x ∧ b ≤ u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists

@[to_dual (dont_translate := α)]
/-
**Filter.exists_lt_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a :
 α) (b : β) : exists a', a <= a' ∧ b < u a'
参数：h : Tendsto u atTop atTop；a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用引理 `Filter.exists_le_of_tendsto_atTop`：exists_le_of_tendsto_atTop (h : Tends
to u atTop atTop) (a : α) (b : β) : exists a', a <= a' ∧ b <= u a'
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a', a ≤ a' ∧ b < u a' := by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

end IsDirected

section IsDirected
variable [Nonempty α] [Preorder α] [IsDirectedOrder α] {f : α → β} {l : Filter β}

@[to_dual]
/-
**Filter.tendsto_atTop'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop' : Tendsto f atTop l ↔ forall s in l, exists a, forall b, a 
<= b -> f b in s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop' : Tendsto f atTop l ↔ ∀ s ∈ l, ∃ a, ∀ b, a ≤ b → f b ∈ s := by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]

@[to_dual]
/-
**Filter.tendsto_atTop_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_principal {s : Set β} : Tendsto f atTop (𝓟 s) ↔ exists N, fo
rall n, N <= n -> f n in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop_principal {s : Set β} :
    Tendsto f atTop (𝓟 s) ↔ ∃ N, ∀ n, N ≤ n → f n ∈ s := by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]

variable [Preorder β]

@[to_dual]
/-
**Filter.tendsto_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atTop : Tendsto f atTop atTop ↔ forall b : β, exists i : α, 
forall a : α, i <= a -> b <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Filter.tendsto_atTop_principal`：tendsto_atTop_principal {s : Set β} : Te
ndsto f atTop (𝓟 s) ↔ exists N, forall n, N <= n -> f n in s
-/
theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
  tendsto_iInf.trans <| forall_congr' fun _ => tendsto_atTop_principal

@[to_dual]
/-
**Filter.tendsto_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atBot : Tendsto f atTop atBot ↔ forall b : β, exists i : α, 
forall a : α, i <= a -> f a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
-/
theorem tendsto_atTop_atBot : Tendsto f atTop atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → f a ≤ b :=
  tendsto_atTop_atTop (β := βᵒᵈ)

@[to_dual]
/-
**Filter.tendsto_atTop_atTop_iff_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) : Tendsto f atTop at
Top ↔ forall b : β, exists a, b <= f a
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) :
    Tendsto f atTop atTop ↔ ∀ b : β, ∃ a, b ≤ f a :=
  tendsto_atTop_atTop.trans <| forall_congr' fun _ => exists_congr fun a =>
    ⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h <| hf ha'⟩

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone

@[to_dual]
/-
**Filter.tendsto_atTop_atBot_iff_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) : Tendsto f atTop at
Bot ↔ forall b : β, exists a, f a <= b
参数：hf : Antitone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_iff_of_monotone`：tendsto_atTop_atTop_iff_of_m
onotone (hf : Monotone f) : Tendsto f atTop atTop ↔ forall b : β, exists a, b <=
 f a
-/
theorem tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) :
    Tendsto f atTop atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

end IsDirected

/-
**Filter.Tendsto.subseq_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {F : Filter α} {V : ℕ → Set α},   (∀ (n : ℕ), V n ∈ F) → 
∀ {u : ℕ → α}, Filter.Tendsto u Filter.atTop F → ∃ φ, StrictMono φ ∧ ∀ (n : ℕ), 
u (φ n) ∈ V n
参数：∀ (n : ℕ), V n ∈ F；n : ℕ；φ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_forall_of_eventually'`：extraction_forall_of_eventually
' {P : Nat -> Nat -> Prop} (h : forall n, exists N, forall k >= N, P n k) : exis
ts φ : Nat -> Nat, StrictMono…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
theorem Tendsto.subseq_mem {F : Filter α} {V : ℕ → Set α} (h : ∀ n, V n ∈ F) {u : ℕ → α}
    (hu : Tendsto u atTop F) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ V n :=
  extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : ∀ n, ∃ N, ∀ k ≥ N, u k ∈ V n)

/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
@[to_dual
/-- A function `f` maps downwards closed sets (atBot sets) to downwards closed sets when it is a
Galois coinsertion. The Galois "coinsertion" and "connection" is weakened to only require it to be
an insertion and a connection below `b`. -/]
/-
**Filter.map_atTop_eq_of_gc_preorder** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_atTop_eq_of_gc_preorder [Preorder α] [IsDirectedOrder α] [Preorder β] 
[IsDirectedOrder β] {f : α -> β} (hf : Monotone f) (b : β) (hgi : forall c, b <=
 c -> exists x, f x = c ∧ forall a, f a <= c ↔ a <= x) : map f atTop = atTop
参数：hf : Monotone f；b : β；hgi : forall c, b <= c -> exists x, f x = c ∧ forall a,
 f a <= c ↔ a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem map_atTop_eq_of_gc_preorder
    [Preorder α] [IsDirectedOrder α] [Preorder β] [IsDirectedOrder β] {f : α → β}
    (hf : Monotone f) (b : β)
    (hgi : ∀ c, b ≤ c → ∃ x, f x = c ∧ ∀ a, f a ≤ c ↔ a ≤ x) : map f atTop = atTop := by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c ↦ ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
    intro a _
    filter_upwards [eventually_ge_atTop (f a), eventually_ge_atTop b] with c hac hbc
    exact ⟨g c, (hgle _ hbc _).1 hac, hfg _ hbc⟩

/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
@[to_dual
/-- A function `f` maps downwards closed sets (atBot sets) to downwards closed sets when it is a
Galois coinsertion. The Galois "coinsertion" and "connection" is weakened to only require it to be
an insertion and a connection below `b`. -/]
/-
**Filter.map_atTop_eq_of_gc** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_atTop_eq_of_gc [Preorder α] [IsDirectedOrder α] [PartialOrder β] [IsDi
rectedOrder β] {f : α -> β} (g : β -> α) (b : β) (hf : Monotone f) (gc : forall 
a, forall c, b <= c -> (f a <= c ↔ a <= g c)) (hgi : forall c, b <= c -> (c <= f
 (g c))) : map f atTop = atTop
参数：g : β -> α；b : β；hf : Monotone f；gc : forall a, forall c, b <= c -> (f a <= c
 ↔ a <= g c)；hgi : forall c, b <= c -> (c <= f (g c))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc_preorder`：map_atTop_eq_of_gc_preorder [Preorde
r α] [IsDirectedOrder α] [Preorder β] [IsDirectedOrder β] {f : α -> β} (hf : Mon
otone f) (b : β) (hgi : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem map_atTop_eq_of_gc
    [Preorder α] [IsDirectedOrder α] [PartialOrder β] [IsDirectedOrder β]
    {f : α → β} (g : β → α) (b : β) (hf : Monotone f)
    (gc : ∀ a, ∀ c, b ≤ c → (f a ≤ c ↔ a ≤ g c)) (hgi : ∀ c, b ≤ c → (c ≤ f (g c))) :
    map f atTop = atTop :=
  map_atTop_eq_of_gc_preorder hf b fun c hc ↦
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩

@[to_dual]
/-
**Filter.map_val_atTop_of_Ici_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_val_atTop_of_Ici_subset [Preorder α] [IsDirectedOrder α] {a : α} {s : 
Set α} (h : Ici a subseteq s) : map ((↑) : s -> α) atTop = atTop
参数：h : Ici a subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDirectedOrder.eq_1`：∀ (α : Type u_5) [inst : LE α], IsDirectedOrder α 
= IsDirected α fun x1 x2 => x1 ≤ x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `directed_id_iff`：directed_id_iff : Directed r id ↔ IsDirected α r
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Filter.map_atTop_eq_of_gc_preorder`：map_atTop_eq_of_gc_preorder [Preorde
r α] [IsDirectedOrder α] [Preorder β] [IsDirectedOrder β] {f : α -> β} (hf : Mon
otone f) (b : β) (hgi : …
· 使用定理 `Subtype.mono_coe`：Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monoto
ne ((↑) : Subtype p -> α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem map_val_atTop_of_Ici_subset [Preorder α] [IsDirectedOrder α] {a : α} {s : Set α}
    (h : Ici a ⊆ s) : map ((↑) : s → α) atTop = atTop := by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· ≤ ·) s := fun x _ y _ ↦
    ⟨f a (f x y), h <| hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirectedOrder s := by
    rw [directedOn_iff_directed] at this
    rwa [IsDirectedOrder, ← directed_id_iff]
  refine map_atTop_eq_of_gc_preorder (Subtype.mono_coe _) a fun c hc ↦ ?_
  exact ⟨⟨c, h hc⟩, rfl, fun _ ↦ .rfl⟩

@[simp]
/-
**Filter._root_.Nat.map_cast_int_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.map_cast_int_atTop : map ((↑) : ℕ → ℤ) atTop = atTop := by
  refine map_atTop_eq_of_gc_preorder (fun _ _ ↦ Int.ofNat_le.2) 0 fun n hn ↦ ?_
  lift n to ℕ using hn
  exact ⟨n, rfl, fun _ ↦ Int.ofNat_le⟩

/-- The image of the filter `atTop` on `Ici a` under the coercion equals `atTop`. -/
@[to_dual (attr := simp)
/-- The image of the filter `atBot` on `Iic a` under the coercion equals `atBot`. -/]
/-
**Filter.map_val_Ici_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_val_Ici_atTop [Preorder α] [IsDirectedOrder α] (a : α) : map ((↑) : Ic
i a -> α) atTop = atTop
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_val_atTop_of_Ici_subset`：map_val_atTop_of_Ici_subset [Preorde
r α] [IsDirectedOrder α] {a : α} {s : Set α} (h : Ici a subseteq s) : map ((↑) :
 s -> α) atTop = atTop
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem map_val_Ici_atTop [Preorder α] [IsDirectedOrder α] (a : α) :
    map ((↑) : Ici a → α) atTop = atTop :=
  map_val_atTop_of_Ici_subset Subset.rfl

/-- The image of the filter `atTop` on `Ioi a` under the coercion equals `atTop`. -/
@[to_dual (attr := simp)
/-- The image of the filter `atBot` on `Iio a` under the coercion equals `atBot`. -/]
/-
**Filter.map_val_Ioi_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α] (a : α) 
: map ((↑) : Ioi a -> α) atTop = atTop
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Filter.map_val_atTop_of_Ici_subset`：map_val_atTop_of_Ici_subset [Preorde
r α] [IsDirectedOrder α] {a : α} {s : Set α} (h : Ici a subseteq s) : map ((↑) :
 s -> α) atTop = atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
-/
theorem map_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α] (a : α) :
    map ((↑) : Ioi a → α) atTop = atTop :=
  let ⟨_b, hb⟩ := exists_gt a
  map_val_atTop_of_Ici_subset <| Ici_subset_Ioi.2 hb

/-- The `atTop` filter for `↑(Ioi a)` comes from the `atTop` filter in the ambient order. -/
@[to_dual
/-- The `atBot` filter for `↑(Iio a)` comes from the `atBot` filter in the ambient order. -/]
/-
**Filter.atTop_Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_Ioi_eq [Preorder α] [IsDirectedOrder α] (a : α) : atTop = comap ((↑)
 : Ioi a -> α) atTop
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_val_atTop_of_Ici_subset`：map_val_atTop_of_Ici_subset [Preorde
r α] [IsDirectedOrder α] {a : α} {s : Set α} (h : Ici a subseteq s) : map ((↑) :
 s -> α) atTop = atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem atTop_Ioi_eq [Preorder α] [IsDirectedOrder α] (a : α) :
    atTop = comap ((↑) : Ioi a → α) atTop := by
  rcases isEmpty_or_nonempty (Ioi a) with h | ⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]

/-- The `atTop` filter for `↑(Ici a)` comes from the `atTop` filter in the ambient order. -/
@[to_dual
/-- The `atBot` filter for `↑(Iic a)` comes from the `atBot` filter in the ambient order. -/]
/-
**Filter.atTop_Ici_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：atTop_Ici_eq [Preorder α] [IsDirectedOrder α] (a : α) : atTop = comap ((↑)
 : Ici a -> α) atTop
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_val_Ici_atTop`：map_val_Ici_atTop [Preorder α] [IsDirectedOrde
r α] (a : α) : map ((↑) : Ici a -> α) atTop = atTop
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem atTop_Ici_eq [Preorder α] [IsDirectedOrder α] (a : α) :
    atTop = comap ((↑) : Ici a → α) atTop := by
  rw [← map_val_Ici_atTop a, comap_map Subtype.coe_injective]

@[to_dual]
/-
**Filter.tendsto_Ioi_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioi_atTop [Preorder α] [IsDirectedOrder α] {a : α} {f : β -> Ioi a
} {l : Filter β} : Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.atTop_Ioi_eq`：atTop_Ioi_eq [Preorder α] [IsDirectedOrder α] (a : 
α) : atTop = comap ((↑) : Ioi a -> α) atTop
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Ioi_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : β → Ioi a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ioi_eq, tendsto_comap_iff, Function.comp_def]

@[to_dual]
/-
**Filter.tendsto_Ici_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_Ici_atTop [Preorder α] [IsDirectedOrder α] {a : α} {f : β -> Ici a
} {l : Filter β} : Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.atTop_Ici_eq`：atTop_Ici_eq [Preorder α] [IsDirectedOrder α] (a : 
α) : atTop = comap ((↑) : Ici a -> α) atTop
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Ici_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : β → Ici a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ici_eq, tendsto_comap_iff, Function.comp_def]

@[to_dual (attr := simp)]
/-
**Filter.tendsto_comp_val_Ioi_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comp_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α]
 {a : α} {f : α -> β} {l : Filter β} : Tendsto (fun x : Ioi a => f x) atTop l ↔ 
Tendsto f atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_val_Ioi_atTop`：map_val_Ioi_atTop [Preorder α] [IsDirectedOrde
r α] [NoMaxOrder α] (a : α) : map ((↑) : Ioi a -> α) atTop = atTop
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_val_Ioi_atTop [Preorder α] [IsDirectedOrder α] [NoMaxOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ioi a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ioi_atTop a, tendsto_map'_iff, Function.comp_def]

@[to_dual (attr := simp)]
/-
**Filter.tendsto_comp_val_Ici_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comp_val_Ici_atTop [Preorder α] [IsDirectedOrder α] {a : α} {f : α
 -> β} {l : Filter β} : Tendsto (fun x : Ici a => f x) atTop l ↔ Tendsto f atTop
 l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_val_Ici_atTop`：map_val_Ici_atTop [Preorder α] [IsDirectedOrde
r α] (a : α) : map ((↑) : Ici a -> α) atTop = atTop
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_val_Ici_atTop [Preorder α] [IsDirectedOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ici a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ici_atTop a, tendsto_map'_iff, Function.comp_def]
/-
**Filter.map_add_atTop_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_add_atTop_eq_nat (k : Nat) : map (fun a => a + k) atTop = atTop
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc`：map_atTop_eq_of_gc [Preorder α] [IsDirectedOr
der α] [PartialOrder β] [IsDirectedOrder β] {f : α -> β} (g : β -> α) (b : β) (h
f : Monotone f)…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nat.add_le_add_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n + k ≤ m + k
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.le_sub_iff_add_le`：∀ {k m n : ℕ}, k ≤ m → (n ≤ m - k ↔ n + k ≤ m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_add_atTop_eq_nat (k : ℕ) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]
/-
**Filter.map_sub_atTop_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_sub_atTop_eq_nat (k : Nat) : map (fun a => a - k) atTop = atTop
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc`：map_atTop_eq_of_gc [Preorder α] [IsDirectedOr
der α] [PartialOrder β] [IsDirectedOrder β] {f : α -> β} (g : β -> α) (b : β) (h
f : Monotone f)…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nat.sub_le_sub_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n - k ≤ m - k
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_sub_atTop_eq_nat (k : ℕ) : map (fun a => a - k) atTop = atTop :=
  map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]
/-
**Filter.tendsto_add_atTop_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_add_atTop_nat (k : Nat) : Tendsto (fun a => a + k) atTop atTop
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.map_add_atTop_eq_nat`：map_add_atTop_eq_nat (k : Nat) : map (fun a
 => a + k) atTop = atTop
-/
theorem tendsto_add_atTop_nat (k : ℕ) : Tendsto (fun a => a + k) atTop atTop :=
  le_of_eq (map_add_atTop_eq_nat k)
/-
**Filter.tendsto_sub_atTop_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_sub_atTop_nat (k : Nat) : Tendsto (fun a => a - k) atTop atTop
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.map_sub_atTop_eq_nat`：map_sub_atTop_eq_nat (k : Nat) : map (fun a
 => a - k) atTop = atTop
-/
theorem tendsto_sub_atTop_nat (k : ℕ) : Tendsto (fun a => a - k) atTop atTop :=
  le_of_eq (map_sub_atTop_eq_nat k)
/-
**Filter.tendsto_add_atTop_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_add_atTop_iff_nat {f : Nat -> α} {l : Filter α} (k : Nat) : Tendst
o (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l
参数：k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.map_add_atTop_eq_nat`：map_add_atTop_eq_nat (k : Nat) : map (fun a
 => a + k) atTop = atTop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_add_atTop_iff_nat {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_add_atTop_eq_nat]
/-
**Filter.map_div_atTop_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_div_atTop_eq_nat (k : Nat) (hk : 0 < k) : map (fun a => a / k) atTop =
 atTop
参数：k : Nat；hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_atTop_eq_of_gc`：map_atTop_eq_of_gc [Preorder α] [IsDirectedOr
der α] [PartialOrder β] [IsDirectedOrder β] {f : α -> β} (g : β -> α) (b : β) (h
f : Monotone f)…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nat.div_le_div_right`：∀ {a b c : ℕ}, a ≤ b → a / c ≤ b / c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_le_iff_le_mul_add_pred`：∀ {b a c : ℕ}, 0 < b → (a / b ≤ c ↔ a ≤ 
b * c + (b - 1))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Nat.mul_add_div`：∀ {m : ℕ}, m > 0 → ∀ (x y : ℕ), (m * x + y) / m = x + y
 / m
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_div_atTop_eq_nat (k : ℕ) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, Nat.add_zero]; lia
/-
**Filter.tendsto_inf_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inf_atTop {α β : Type*} [SemilatticeInf α] {f g : β -> α} (F : Fil
ter β) (hf : Tendsto f F atTop) (hg : Tendsto g F atTop) : Tendsto (fun x => f x
 ⊓ g x) F atTop
参数：F : Filter β；hf : Tendsto f F atTop；hg : Tendsto g F atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_inf_atTop {α β : Type*} [SemilatticeInf α]
    {f g : β → α} (F : Filter β) (hf : Tendsto f F atTop) (hg : Tendsto g F atTop) :
    Tendsto (fun x ↦ f x ⊓ g x) F atTop := by
  rw [Filter.tendsto_atTop] at *
  simp [eventually_and, hf, hg]
/-
**Filter.tendsto_sup_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_sup_atBot {α β : Type*} [SemilatticeSup α] {f g : β -> α} (F : Fil
ter β) (hf : Tendsto f F atBot) (hg : Tendsto g F atBot) : Tendsto (fun x => f x
 ⊔ g x) F atBot
参数：F : Filter β；hf : Tendsto f F atBot；hg : Tendsto g F atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β
] {m : α → β} {f : Filter α},   Filter.Tendsto m f Filter.atBot ↔ ∀ (b : β), ∀ᶠ 
(a : α) in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendsto_sup_atBot {α β : Type*} [SemilatticeSup α]
    {f g : β → α} (F : Filter β) (hf : Tendsto f F atBot) (hg : Tendsto g F atBot) :
    Tendsto (fun x ↦ f x ⊔ g x) F atBot := by
  rw [Filter.tendsto_atBot] at *
  simp [eventually_and, hf, hg]

section NeBot
variable [Preorder β] {l : Filter α} [NeBot l] {f : α → β}

@[to_dual]
/-
**Filter.not_bddAbove_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_bddAbove_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f l atTop) : ¬Bd
dAbove (range f)
参数：h : Tendsto f l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Filter.empty_notMem`：empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
-/
theorem not_bddAbove_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f l atTop) :
    ¬BddAbove (range f) := by
  rintro ⟨M, hM⟩
  have : ∀ x, f x ≤ M := by aesop
  have : ∅ = f ⁻¹' Ioi M := by aesop (add forward safe not_le_of_gt)
  apply Filter.empty_notMem l
  aesop (add safe Ioi_mem_atTop)

end NeBot

/-
**Filter.HasAntitoneBasis.eventually_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ha
sAntitoneBasis`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : Preorder ι] {l : Filter α} {s : ι 
→ Set α},   l.HasAntitoneBasis s → ∀ {t : Set α}, t ∈ l → ∀ᶠ (i : ι) in Filter.a
tTop, s i ⊆ t
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
-/
theorem HasAntitoneBasis.eventually_subset [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {t : Set α} (ht : t ∈ l) : ∀ᶠ i in atTop, s i ⊆ t :=
  let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi
/-
**Filter.HasAntitoneBasis.tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAntitoneB
asis`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_3} [inst : Preorder ι] {l : Filter α} {s : ι 
→ Set α},   l.HasAntitoneBasis s → ∀ {φ : ι → α}, (∀ (i : ι), φ i ∈ s i) → Filte
r.Tendsto φ Filter.atTop l
参数：∀ (i : ι), φ i ∈ s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.HasAntitoneBasis.eventually_subset`：∀ {ι : Type u_1} {α : Type u_
3} [inst : Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → 
∀ {t : Set α}, t ∈ l → ∀ᶠ (i : …
-/
protected theorem HasAntitoneBasis.tendsto [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {φ : ι → α} (h : ∀ i : ι, φ i ∈ s i) : Tendsto φ atTop l :=
  fun _t ht => mem_map.2 <| (hl.eventually_subset ht).mono fun i hi => hi (h i)
/-
**Filter.HasAntitoneBasis.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasAntiton
eBasis`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {α : Type u_3} [Nonempty ι] [inst : Preor
der ι] [IsDirectedOrder ι]   [inst_2 : Preorder ι'] {l : Filter α} {s : ι' → Set
 α},   l.HasAntitoneBasis s →     ∀ {φ : ι → ι'}, Monotone φ → Filter.Tendsto φ 
Filter.atTop Filter.atTop → l.HasAntitoneBasis (s ∘ φ)
参数：s ∘ φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `Filter.HasAntitoneBasis.antitone`：∀ {α : Type u_1} {ι'' : Type u_6} [ins
t : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → Ant
itone s
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
-/
theorem HasAntitoneBasis.comp_mono [Nonempty ι] [Preorder ι] [IsDirectedOrder ι] [Preorder ι']
    {l : Filter α}
    {s : ι' → Set α} (hs : l.HasAntitoneBasis s) {φ : ι → ι'} (φ_mono : Monotone φ)
    (hφ : Tendsto φ atTop atTop) : l.HasAntitoneBasis (s ∘ φ) :=
  ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩
/-
**Filter.HasAntitoneBasis.comp_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasA
ntitoneBasis`。
形式化陈述：∀ {α : Type u_3} {l : Filter α} {s : ℕ → Set α},   l.HasAntitoneBasis s → 
∀ {φ : ℕ → ℕ}, StrictMono φ → l.HasAntitoneBasis (s ∘ φ)
参数：s ∘ φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasAntitoneBasis.comp_mono`：∀ {ι : Type u_1} {ι' : Type u_2} {α :
 Type u_3} [Nonempty ι] [inst : Preorder ι] [IsDirectedOrder ι]   [inst_2 : Preo
rder ι'] {l : Filter α}…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
-/
theorem HasAntitoneBasis.comp_strictMono {l : Filter α} {s : ℕ → Set α} (hs : l.HasAntitoneBasis s)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : l.HasAntitoneBasis (s ∘ φ) :=
  hs.comp_mono hφ.monotone hφ.tendsto_atTop
/-
**Filter.subseq_forall_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subseq_forall_of_frequently {ι : Type*} {x : Nat -> ι} {p : ι -> Prop} {l 
: Filter ι} (h_tendsto : Tendsto x atTop l) (h : existsᶠ n in atTop, p (x n)) : 
exists ns : Nat -> Nat, Tendsto (fun n => x (ns n)) atTop l ∧ forall n, p (x (ns
 n))
参数：h_tendsto : Tendsto x atTop l；h : existsᶠ n in atTop, p (x n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem subseq_forall_of_frequently {ι : Type*} {x : ℕ → ι} {p : ι → Prop} {l : Filter ι}
    (h_tendsto : Tendsto x atTop l) (h : ∃ᶠ n in atTop, p (x n)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n => x (ns n)) atTop l ∧ ∀ n, p (x (ns n)) := by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

end Filter

