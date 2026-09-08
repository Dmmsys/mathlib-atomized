/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Filter.Bases.Finite
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finiteness and `Filter.atTop` and `Filter.atBot` filters

This file contains results on `Filter.atTop` and `Filter.atBot` that depend on
the finiteness theory developed in Mathlib.
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

/-
**Filter.eventually_forall_ge_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_forall_ge_atTop [Preorder α] {p : α -> Prop} : (forallᶠ x in at
Top, forall y, x <= y -> p y) ↔ forallᶠ x in atTop, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.hasBasis_iInf_principal_finite`：hasBasis_iInf_principal_finite {ι
 : Type*} (s : ι -> Set α) : (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite)
 fun t => ⋂ i in t, s i
· 使用定理 `Filter.mem_iInf_of_iInter`：mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U
 : Set α} {I : Set ι} (I_fin : I.Finite) {V : I -> Set α} (hV : forall (i : I), 
V i in s i) (hU…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem eventually_forall_ge_atTop [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atTop, ∀ y, x ≤ y → p y) ↔ ∀ᶠ x in atTop, p x := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ hx x le_rfl, fun h ↦ ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x ↦ Ici x.1) (fun _ ↦ Subset.rfl) fun x hx y hy ↦ ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz ↦ le_trans (hx ⟨z, hz⟩) hy
/-
**Filter.eventually_forall_le_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_forall_le_atBot [Preorder α] {p : α -> Prop} : (forallᶠ x in at
Bot, forall y, y <= x -> p y) ↔ forallᶠ x in atBot, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_forall_ge_atTop`：eventually_forall_ge_atTop [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x i
n atTop, p x
-/
theorem eventually_forall_le_atBot [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atBot, ∀ y, y ≤ x → p y) ↔ ∀ᶠ x in atBot, p x :=
  eventually_forall_ge_atTop (α := αᵒᵈ)
/-
**Filter.Tendsto.eventually_forall_ge_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] {l : Filter α} {p : β 
→ Prop} {f : α → β},   Filter.Tendsto f l Filter.atTop → (∀ᶠ (x : β) in Filter.a
tTop, p x) → ∀ᶠ (x : α) in l, ∀ (y : β), f x ≤ y → p y
参数：∀ᶠ (x : β) in Filter.atTop, p x；x : α；y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_forall_ge_atTop`：eventually_forall_ge_atTop [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x i
n atTop, p x
-/
theorem Tendsto.eventually_forall_ge_atTop [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atTop) (h_evtl : ∀ᶠ x in atTop, p x) :
    ∀ᶠ x in l, ∀ y, f x ≤ y → p y := by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap
/-
**Filter.Tendsto.eventually_forall_le_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] {l : Filter α} {p : β 
→ Prop} {f : α → β},   Filter.Tendsto f l Filter.atBot → (∀ᶠ (x : β) in Filter.a
tBot, p x) → ∀ᶠ (x : α) in l, ∀ y ≤ f x, p y
参数：∀ᶠ (x : β) in Filter.atBot, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_forall_le_atBot`：eventually_forall_le_atBot [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atBot, forall y, y <= x -> p y) ↔ forallᶠ x i
n atBot, p x
-/
theorem Tendsto.eventually_forall_le_atBot [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atBot) (h_evtl : ∀ᶠ x in atBot, p x) :
    ∀ᶠ x in l, ∀ y, y ≤ f x → p y := by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

/-!
### Sequences
-/

/-- If `u` is a sequence which is unbounded above,
then after any point, it reaches a value strictly greater than all previous values.
-/
/-
**Filter.high_scores** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu : Tendsto u 
atTop atTop) : forall N, exists n >= N, forall k < n, u k < u n
参数：hu : Tendsto u atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_max_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.exists_lt_of_tendsto_atTop`：exists_lt_of_tendsto_atTop [NoMaxOrde
r β] (h : Tendsto u atTop atTop) (a : α) (b : β) : exists a', a <= a' ∧ b < u a'
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)

--- 原说明 ---
If `u` is a sequence which is unbounded above,
then after any point, it reaches a value strictly greater than all previous valu
es.
-/
theorem high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β} (hu : Tendsto u atTop atTop) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n := by
  intro N
  obtain ⟨k : ℕ, - : k ≤ N, hku : ∀ l ≤ N, u l ≤ u k⟩ : ∃ k ≤ N, ∀ l ≤ N, u l ≤ u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : ∃ n ≥ N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : ℕ, hnN : n ≥ N, hnk : u k < u n, hn_min : ∀ m, m < n → N ≤ m → u m ≤ u k⟩ :
      ∃ n ≥ N, u k < u n ∧ ∀ m, m < n → N ≤ m → u m ≤ u k := by
    rcases Nat.findX ex with ⟨n, ⟨hnN, hnk⟩, hn_min⟩
    push Not at hn_min
    exact ⟨n, hnN, hnk, hn_min⟩
  use n, hnN
  grind

/-- If `u` is a sequence which is unbounded below,
then after any point, it reaches a value strictly smaller than all previous values.
-/
/-
**Filter.low_scores** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：low_scores [LinearOrder β] [NoMinOrder β] {u : Nat -> β} (hu : Tendsto u a
tTop atBot) : forall N, exists n >= N, forall k < n, u n < u k
参数：hu : Tendsto u atTop atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.high_scores`：high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat 
-> β} (hu : Tendsto u atTop atTop) : forall N, exists n >= N, forall k < n, u k 
< u n
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
If `u` is a sequence which is unbounded below,
then after any point, it reaches a value strictly smaller than all previous valu
es.
-/
theorem low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β} (hu : Tendsto u atTop atBot) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u n < u k :=
  @high_scores βᵒᵈ _ _ _ hu

/-- If `u` is a sequence which is unbounded above,
then it `Frequently` reaches a value strictly greater than all previous values.
-/
/-
**Filter.frequently_high_scores** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu :
 Tendsto u atTop atTop) : existsᶠ n in atTop, forall k < n, u k < u n
参数：hu : Tendsto u atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.high_scores`：high_scores [LinearOrder β] [NoMaxOrder β] {u : Nat 
-> β} (hu : Tendsto u atTop atTop) : forall N, exists n >= N, forall k < n, u k 
< u n

--- 原说明 ---
If `u` is a sequence which is unbounded above,
then it `Frequently` reaches a value strictly greater than all previous values.
-/
theorem frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ᶠ n in atTop, ∀ k < n, u k < u n := by
  simpa [frequently_atTop] using high_scores hu

/-- If `u` is a sequence which is unbounded below,
then it `Frequently` reaches a value strictly smaller than all previous values.
-/
/-
**Filter.frequently_low_scores** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : Nat -> β} (hu : 
Tendsto u atTop atBot) : existsᶠ n in atTop, forall k < n, u n < u k
参数：hu : Tendsto u atTop atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_high_scores`：frequently_high_scores [LinearOrder β] [N
oMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop) : existsᶠ n in atTop, f
orall k < n, u k < …
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
If `u` is a sequence which is unbounded below,
then it `Frequently` reaches a value strictly smaller than all previous values.
-/
theorem frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atBot) : ∃ᶠ n in atTop, ∀ k < n, u n < u k :=
  @frequently_high_scores βᵒᵈ _ _ _ hu
/-
**Filter.strictMono_subseq_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : Nat
 -> β} (hu : Tendsto u atTop atTop) : exists φ : Nat -> Nat, StrictMono φ ∧ Stri
ctMono (u ∘ φ)
参数：hu : Tendsto u atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_of_frequently_atTop`：extraction_of_frequently_atTop {P
 : Nat -> Prop} (h : existsᶠ n in atTop, P n) : exists φ : Nat -> Nat, StrictMon
o φ ∧ forall n, P (φ n)
· 使用定理 `Filter.frequently_high_scores`：frequently_high_scores [LinearOrder β] [N
oMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop) : existsᶠ n in atTop, f
orall k < n, u k < …
-/
theorem strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩
/-
**Filter.strictMono_subseq_of_id_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：strictMono_subseq_of_id_le {u : Nat -> Nat} (hu : forall n, n <= u n) : ex
ists φ : Nat -> Nat, StrictMono φ ∧ StrictMono (u ∘ φ)
参数：hu : forall n, n <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.strictMono_subseq_of_tendsto_atTop`：strictMono_subseq_of_tendsto_
atTop [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop)
 : exists φ : Nat -> Nat, Stric…
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem strictMono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)
/-
**Filter.Eventually.atTop_of_arithmetic** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventu
ally`。
形式化陈述：∀ {p : ℕ → Prop} {n : ℕ}, n ≠ 0 → (∀ k < n, ∀ᶠ (a : ℕ) in Filter.atTop, p 
(n * a + k)) → ∀ᶠ (a : ℕ) in Filter.atTop, p a
参数：∀ k < n, ∀ᶠ (a : ℕ) in Filter.atTop, p (n * a + k)；a : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Eventually.atTop_of_arithmetic {p : ℕ → Prop} {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ k < n, ∀ᶠ a in atTop, p (n * a + k)) : ∀ᶠ a in atTop, p a := by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [Nat.le_div_iff_mul_le hn.bot_lt, mul_comm]
  exact (Finset.le_sup (f := (n * N ·)) (Finset.mem_range.2 hlt)).trans hb

/-- Given an antitone basis `s : ℕ → Set α` of a filter, extract an antitone subbasis `s ∘ φ`,
`φ : ℕ → ℕ`, such that `m < n` implies `r (φ m) (φ n)`. This lemma can be used to extract an
antitone basis with basis sets decreasing "sufficiently fast". -/
/-
**Filter.HasAntitoneBasis.subbasis_with_rel** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ha
sAntitoneBasis`。
形式化陈述：∀ {α : Type u_3} {f : Filter α} {s : ℕ → Set α},   f.HasAntitoneBasis s → 
    ∀ {r : ℕ → ℕ → Prop},       (∀ (m : ℕ), ∀ᶠ (n : ℕ) in Filter.atTop, r m n) →
         ∃ φ, StrictMono φ ∧ (∀ ⦃m n : ℕ⦄, m < n → r (φ m) (φ n)) ∧ f.HasAntiton
eBasis (s ∘ φ)
参数：∀ (m : ℕ), ∀ᶠ (n : ℕ) in Filter.atTop, r m n；∀ ⦃m n : ℕ⦄, m < n → r (φ m) (φ 
n)；s ∘ φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finite`：eventually_all_finite {ι} {I : Set ι} (hI 
: I.Finite) {l} {p : ι -> α -> Prop} : (forallᶠ x in l, forall i in I, p i x) ↔ 
forall i in I, for…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Set.seq_of_forall_finite_exists`：seq_of_forall_finite_exists {γ : Type*}
 {P : γ -> Set γ -> Prop} (h : forall t : Set γ, t.Finite -> exists c, P c t) : 
exists u : Nat -> γ, …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.HasAntitoneBasis.comp_strictMono`：∀ {α : Type u_3} {l : Filter α}
 {s : ℕ → Set α},   l.HasAntitoneBasis s → ∀ {φ : ℕ → ℕ}, StrictMono φ → l.HasAn
titoneBasis (s ∘ φ)

--- 原说明 ---
Given an antitone basis `s : ℕ → Set α` of a filter, extract an antitone subbasi
s `s ∘ φ`,
`φ : ℕ → ℕ`, such that `m < n` implies `r (φ m) (φ n)`. This lemma can be used t
o extract an
antitone basis with basis sets decreasing "sufficiently fast".
-/
theorem HasAntitoneBasis.subbasis_with_rel {f : Filter α} {s : ℕ → Set α}
    (hs : f.HasAntitoneBasis s) {r : ℕ → ℕ → Prop} (hr : ∀ m, ∀ᶠ n in atTop, r m n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ ⦃m n⦄, m < n → r (φ m) (φ n)) ∧ f.HasAntitoneBasis (s ∘ φ) := by
  rsuffices ⟨φ, hφ, hrφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m n, m < n → r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : ∀ t : Set ℕ, t.Finite → ∀ᶠ n in atTop, ∀ m ∈ t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (eventually_gt_atTop m).and (hr _)
  rcases seq_of_forall_finite_exists fun t ht => (this t ht).exists with ⟨φ, hφ⟩
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.2 hφ.1, forall_comm.2 hφ.2⟩

end Filter

open Filter Finset

namespace Nat

/-
**Nat.eventually_pow_lt_factorial_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eventually_pow_lt_factorial_sub (c d : Nat) : forallᶠ n in atTop, c ^ n < 
(n - d)!
参数：c d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_pow_of_pos`：∀ (n : ℕ), 0 < n → 0 ^ n = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.mul_lt_mul_of_le_of_lt`：∀ {a c b d : ℕ}, a ≤ c → b < d → 0 < c → a *
 b < c * d
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
（共 33 条，此处仅展示前 30 条）
-/
theorem eventually_pow_lt_factorial_sub (c d : ℕ) : ∀ᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to! (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    lia
  · congr 1
    lia
  refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le <|
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : ℕ)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)
/-
**Nat.eventually_mul_pow_lt_factorial_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eventually_mul_pow_lt_factorial_sub (a c d : Nat) : forallᶠ n in atTop, a 
* c ^ n < (n - d)!
参数：a c d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Nat.eventually_pow_lt_factorial_sub`：eventually_pow_lt_factorial_sub (c 
d : Nat) : forallᶠ n in atTop, c ^ n < (n - d)!
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.le_self_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
theorem eventually_mul_pow_lt_factorial_sub (a c d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

end Nat

