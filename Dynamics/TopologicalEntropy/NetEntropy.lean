/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via nets

We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

The major design decisions are the same as in
`Mathlib/Dynamics/TopologicalEntropy/CoverEntropy.lean`, and are explained in detail there:
use of uniform spaces, definition of the topological entropy of a subset, and values taken in
`EReal`.

Given a map `T : X → X` and a subset `F ⊆ X`, the topological entropy is loosely defined using
nets as the exponential growth (in `n`) of the number of distinguishable orbits of length `n`
starting from `F`. More precisely, given an entourage `U`, two orbits of length `n` can be
distinguished if there exists some index `k < n` such that `T^[k] x` and `T^[k] y` are far enough
(i.e. `(T^[k] x, T^[k] y)` is not in `U`). The maximal number of distinguishable orbits of
length `n` is `netMaxcard T F U n`, and its exponential growth `netEntropyEntourage T F U`. This
quantity increases when `U` decreases, and a definition of the topological entropy is
`⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U`.

The definition of topological entropy using nets coincides with the definition using covers.
Instead of defining a new notion of topological entropy, we prove that
`coverEntropy` coincides with `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`.

## Main definitions
- `IsDynNetIn`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `netMaxcard`: maximal cardinality of a dynamical net. Takes values in `ℕ∞`.
- `netEntropyInfEntourage`/`netEntropyEntourage`: exponential growth of `netMaxcard`. The former is
  defined with a `liminf`, the latter with a `limsup`. Take values in `EReal`.

## Implementation notes
As when using covers, there are two competing definitions `netEntropyInfEntourage` and
`netEntropyEntourage` in this file: one uses a `liminf`, the other a `limsup`. When using covers,
we chose the `limsup` definition as the default.

## Main results
- `coverEntropy_eq_iSup_netEntropyEntourage`: equality between the notions of topological entropy
  defined with covers and with nets. Has a variant for `coverEntropyInf`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

@[expose] public section

open Set Uniformity UniformSpace
open scoped SetRel

namespace Dynamics

variable {X : Type*} {T : X → X} {U V : SetRel X X} {m n : ℕ} {F s : Set X} {x : X}

/-! ### Dynamical nets -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` of `F` is a
`(U, n)`-dynamical net of `F` if no two orbits of length `n` of points in `s` shadow each other. -/
/-
**Dynamics.IsDynNetIn** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：IsDynNetIn (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set X)
 : Prop
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` of `F` is 
a
`(U, n)`-dynamical net of `F` if no two orbits of length `n` of points in `s` sh
adow each other.
-/
def IsDynNetIn (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) (s : Set X) : Prop :=
  s ⊆ F ∧ s.PairwiseDisjoint fun x : X ↦ ball x (dynEntourage T U n)
/-
**Dynamics.IsDynNetIn.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynNetIn`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {m n : ℕ} {F s : Set X},   m
 ≤ n → Dynamics.IsDynNetIn T F U m s → Dynamics.IsDynNetIn T F U n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.PairwiseDisjoint.mono`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjoint
 f → g ≤ f → s.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用引理 `Dynamics.dynEntourage_antitone`：dynEntourage_antitone (T : X -> X) (U : 
SetRel X X) : Antitone (fun n : Nat => dynEntourage T U n)
-/
lemma IsDynNetIn.of_le (m_n : m ≤ n) (h : IsDynNetIn T F U m s) : IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 fun x ↦ ball_mono (dynEntourage_antitone T U m_n) x⟩
/-
**Dynamics.IsDynNetIn.of_entourage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.Is
DynNetIn`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U V : SetRel X X} {n : ℕ} {F s : Set X},   U
 ⊆ V → Dynamics.IsDynNetIn T F V n s → Dynamics.IsDynNetIn T F U n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.PairwiseDisjoint.mono`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f g : ι → α},   s.PairwiseDisjoint
 f → g ≤ f → s.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用引理 `Dynamics.dynEntourage_monotone`：dynEntourage_monotone (T : X -> X) (n : 
Nat) : Monotone (fun U : SetRel X X => dynEntourage T U n)
-/
lemma IsDynNetIn.of_entourage_subset (U_V : U ⊆ V) (h : IsDynNetIn T F V n s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 fun x ↦ ball_mono (dynEntourage_monotone T n U_V) x⟩
/-
**Dynamics.isDynNetIn_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：isDynNetIn_empty : IsDynNetIn T F U n ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
lemma isDynNetIn_empty : IsDynNetIn T F U n ∅ := ⟨empty_subset F, pairwise_empty _⟩
/-
**Dynamics.isDynNetIn_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：isDynNetIn_singleton (T : X -> X) (U : SetRel X X) (n : Nat) (h : x in F) 
: IsDynNetIn T F U n {x}
参数：T : X -> X；U : SetRel X X；n : Nat；h : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
lemma isDynNetIn_singleton (T : X → X) (U : SetRel X X) (n : ℕ) (h : x ∈ F) :
    IsDynNetIn T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

/-- Given an entourage `U` and a time `n`, a dynamical net has a smaller cardinality than
  a dynamical cover. This lemma is the first of two key results to compare two versions of
  topological entropy: with cover and with nets, the second being `coverMincard_le_netMaxcard`. -/
/-
**Dynamics.IsDynNetIn.card_le_card_of_isDynCoverOf** 是 Mathlib 中的一个定理，位于命名空间 `Dy
namics.IsDynNetIn`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {n : ℕ} {F : Set X} {s t : F
inset X},   Dynamics.IsDynNetIn T F U n ↑s → Dynamics.IsDynCoverOf T F U n ↑t → 
s.card ≤ t.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Given an entourage `U` and a time `n`, a dynamical net has a smaller cardinality
 than
  a dynamical cover. This lemma is the first of two key results to compare two v
ersions of
  topological entropy: with cover and with nets, the second being `coverMincard_
le_netMaxcard`.
-/
lemma IsDynNetIn.card_le_card_of_isDynCoverOf {s t : Finset X}
    (hs : IsDynNetIn T F U n s) (ht : IsDynCoverOf T F U n t) :
    s.card ≤ t.card := by
  have (x : X) (x_s : x ∈ s) : ∃ z ∈ t, z ∈ ball x (dynEntourage T U n) := by
    simpa using! ht (hs.1 x_s)
  choose! F s_t using this
  apply Finset.card_le_card_of_injOn F fun x x_s ↦ (s_t x x_s).1
  exact fun x x_s y y_s Fx_Fy ↦
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinality of dynamical nets -/

/-- The largest cardinality of a `(U, n)`-dynamical net of `F`. Takes values in `ℕ∞`, and is
infinite if and only if `F` admits nets of arbitrarily large size. -/
/-
**Dynamics.netMaxcard** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) : Nat∞
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest cardinality of a `(U, n)`-dynamical net of `F`. Takes values in `ℕ∞`
, and is
infinite if and only if `F` admits nets of arbitrarily large size.
-/
noncomputable def netMaxcard (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : ℕ∞)
/-
**Dynamics.IsDynNetIn.card_le_netMaxcard** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsD
ynNetIn`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {n : ℕ} {F : Set X} {s : Fin
set X},   Dynamics.IsDynNetIn T F U n ↑s → ↑s.card ≤ Dynamics.netMaxcard T F U n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma IsDynNetIn.card_le_netMaxcard {s : Finset X} (h : IsDynNetIn T F U n s) :
    s.card ≤ netMaxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h
/-
**Dynamics.netMaxcard_monotone_time** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_monotone_time (T : X -> X) (F : Set X) (U : SetRel X X) : Monot
one fun n : Nat => netMaxcard T F U n
参数：T : X -> X；F : Set X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `Dynamics.IsDynNetIn.of_le`：∀ {X : Type u_1} {T : X → X} {U : SetRel X X}
 {m n : ℕ} {F s : Set X},   m ≤ n → Dynamics.IsDynNetIn T F U m s → Dynamics.IsD
ynNetIn T F U n…
-/
lemma netMaxcard_monotone_time (T : X → X) (F : Set X) (U : SetRel X X) :
    Monotone fun n : ℕ ↦ netMaxcard T F U n :=
  fun _ _ m_n ↦ biSup_mono fun _ h ↦ h.of_le m_n
/-
**Dynamics.netMaxcard_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_antitone (T : X -> X) (F : Set X) (n : Nat) : Antitone fun U : 
SetRel X X => netMaxcard T F U n
参数：T : X -> X；F : Set X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `Dynamics.IsDynNetIn.of_entourage_subset`：∀ {X : Type u_1} {T : X → X} {U
 V : SetRel X X} {n : ℕ} {F s : Set X},   U ⊆ V → Dynamics.IsDynNetIn T F V n s 
→ Dynamics.IsDynNetIn T F U n…
-/
lemma netMaxcard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone fun U : SetRel X X ↦ netMaxcard T F U n :=
  fun _ _ U_V ↦ biSup_mono fun _ h ↦ h.of_entourage_subset U_V
/-
**Dynamics.netMaxcard_finite_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_finite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) 
: netMaxcard T F U n < ⊤ ↔ exists s : Finset X, IsDynNetIn T F U n s ∧ (s.card :
 Nat∞) = netMaxcard T F U n
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Dynamics.netMaxcard.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set X) (U : 
SetRel X X) (n : ℕ),   Dynamics.netMaxcard T F U n = ⨆ s, ⨆ (_ : Dynamics.IsDynN
etIn T F U n ↑…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `biSup_congr`：biSup_congr {p : ι -> Prop} (h : forall i, p i -> f i = g i
) : ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Filter.frequently_principal`：frequently_principal {a : Set α} {p : α -> 
Prop} : (existsᶠ x in 𝓟 a, p x) ↔ exists x in a, p x
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用引理 `Dynamics.isDynNetIn_empty`：isDynNetIn_empty : IsDynNetIn T F U n ∅
· 使用定理 `Nat.sSup_mem`：sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s)
 : sSup s in s
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `WithTop.coe_sSup'`：coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) : 
↑(sSup s) = (sSup ((fun (a : α) => ↑a) '' s) : WithTop α)
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
lemma netMaxcard_finite_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    netMaxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynNetIn T F U n s ∧ (s.card : ℕ∞) = netMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · obtain ⟨k, k_max⟩ := ENat.ne_top_iff_exists.mp h.ne
    rw [← k_max]
    simp only [Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have : netMaxcard T F U n
      = sSup (WithTop.some '' Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      rw [netMaxcard, ← image_comp, sSup_image]
      simp only [mem_ofPred_eq, ENat.some_eq_natCast, Function.comp_apply]
      exact biSup_congr (fun _ _ ↦ rfl)
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      refine ⟨k, mem_upperBounds.2 ?_⟩
      simp only [mem_image, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s h
      rw [← ENat.natCast_le_natCast, k_max]
      apply le_sSup
      exact Filter.frequently_principal.mp fun a ↦ a (by simpa using ⟨_, h, rfl⟩) rfl
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [mem_image, mem_ofPred_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetIn_empty
    rw [← WithTop.coe_sSup' h_bdda] at k_max
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← Nat.cast_inj.mp k_max, mem_image] at key
    simp only [mem_ofPred_eq] at key
    exact key
  · obtain ⟨s, _, s_card⟩ := h
    rw [← s_card]
    exact WithTop.coe_lt_top s.card

@[simp]
/-
**Dynamics.netMaxcard_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_empty : netMaxcard T ∅ U n = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.netMaxcard.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set X) (U : 
SetRel X X) (n : ℕ),   Dynamics.netMaxcard T F U n = ⨆ s, ⨆ (_ : Dynamics.IsDynN
etIn T F U n ↑…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iSup₂_eq_bot`：iSup₂_eq_bot {f : forall i, κ i -> α} : ⨆ (i) (j), f i j =
 ⊥ ↔ forall i j, f i j = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
-/
lemma netMaxcard_empty : netMaxcard T ∅ U n = 0 := by
  rw [netMaxcard, ← bot_eq_zero, iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']
/-
**Dynamics.netMaxcard_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_eq_zero_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat)
 : netMaxcard T F U n = 0 ↔ F = ∅
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用引理 `Dynamics.isDynNetIn_singleton`：isDynNetIn_singleton (T : X -> X) (U : Se
tRel X X) (n : Nat) (h : x in F) : IsDynNetIn T F U n {x}
· 使用定理 `Dynamics.IsDynNetIn.card_le_netMaxcard`：∀ {X : Type u_1} {T : X → X} {U 
: SetRel X X} {n : ℕ} {F : Set X} {s : Finset X},   Dynamics.IsDynNetIn T F U n 
↑s → ↑s.card ≤ Dynamics.netM…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `Dynamics.netMaxcard_empty`：netMaxcard_empty : netMaxcard T ∅ U n = 0
-/
lemma netMaxcard_eq_zero_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    netMaxcard T F U n = 0 ↔ F = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, netMaxcard_empty]⟩
  rw [eq_empty_iff_forall_notMem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_netMaxcard
  rw [Finset.card_singleton, Nat.cast_one, h] at key
  exact key.not_gt zero_lt_one
/-
**Dynamics.one_le_netMaxcard_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：one_le_netMaxcard_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) 
: 1 <= netMaxcard T F U n ↔ F.Nonempty
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `Dynamics.netMaxcard_eq_zero_iff`：netMaxcard_eq_zero_iff (T : X -> X) (F 
: Set X) (U : SetRel X X) (n : Nat) : netMaxcard T F U n = 0 ↔ F = ∅
-/
lemma one_le_netMaxcard_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    1 ≤ netMaxcard T F U n ↔ F.Nonempty := by
  rw [Order.one_le_iff_ne_zero, nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_eq_zero_iff T F U n)
/-
**Dynamics.netMaxcard_zero** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_zero (T : X -> X) (h : F.Nonempty) (U : SetRel X X) : netMaxcar
d T F U 0 = 1
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Dynamics.dynEntourage_zero`：∀ {X : Type u_1} {T : X → X} {U : SetRel X X
}, Dynamics.dynEntourage T U 0 = Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用引理 `Dynamics.one_le_netMaxcard_iff`：one_le_netMaxcard_iff (T : X -> X) (F : 
Set X) (U : SetRel X X) (n : Nat) : 1 <= netMaxcard T F U n ↔ F.Nonempty
-/
lemma netMaxcard_zero (T : X → X) (h : F.Nonempty) (U : SetRel X X) : netMaxcard T F U 0 = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s ↦ ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)
/-
**Dynamics.netMaxcard_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_univ (T : X -> X) (h : F.Nonempty) (n : Nat) : netMaxcard T F u
niv n = 1
参数：T : X -> X；h : F.Nonempty；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.dynEntourage_univ`：dynEntourage_univ {T : X -> X} {n : Nat} : d
ynEntourage T univ n = univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用引理 `Dynamics.one_le_netMaxcard_iff`：one_le_netMaxcard_iff (T : X -> X) (F : 
Set X) (U : SetRel X X) (n : Nat) : 1 <= netMaxcard T F U n ↔ F.Nonempty
-/
lemma netMaxcard_univ (T : X → X) (h : F.Nonempty) (n : ℕ) : netMaxcard T F univ n = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 fun x x_s y y_s ↦ ?_
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)
/-
**Dynamics.netMaxcard_infinite_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_infinite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat
) : netMaxcard T F U n = ⊤ ↔ forall k : Nat, exists s : Finset X, IsDynNetIn T F
 U n s ∧ k <= s.card
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Dynamics.netMaxcard.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set X) (U : 
SetRel X X) (n : ℕ),   Dynamics.netMaxcard T F U n = ⨆ s, ⨆ (_ : Dynamics.IsDynN
etIn T F U n ↑…
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.eq_top_iff_forall_gt`：eq_top_iff_forall_gt : n = ⊤ ↔ forall m : Nat
, m < n
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Dynamics.IsDynNetIn.card_le_netMaxcard`：∀ {X : Type u_1} {T : X → X} {U 
: SetRel X X} {n : ℕ} {F : Set X} {s : Finset X},   Dynamics.IsDynNetIn T F U n 
↑s → ↑s.card ≤ Dynamics.netM…
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma netMaxcard_infinite_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    netMaxcard T F U n = ⊤ ↔ ∀ k : ℕ, ∃ s : Finset X, IsDynNetIn T F U n s ∧ k ≤ s.card := by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard, iSup_subtype', iSup_eq_top] at h
    specialize h k (ENat.natCast_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    obtain ⟨s, s_net, s_k⟩ := h
    exact ⟨s, s_net, s_k.le⟩
  · refine ENat.eq_top_iff_forall_gt.mpr fun k ↦ ?_
    specialize h (k + 1)
    obtain ⟨s, s_net, s_card⟩ := h
    apply s_net.card_le_netMaxcard.trans_lt'
    rw [Nat.cast_lt]
    exact (lt_add_one k).trans_le s_card
/-
**Dynamics.netMaxcard_le_coverMincard** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_le_coverMincard (T : X -> X) (F : Set X) (n : Nat) : netMaxcard
 T F U n <= coverMincard T F U n
参数：T : X -> X；F : Set X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Dynamics.IsDynNetIn.card_le_card_of_isDynCoverOf`：∀ {X : Type u_1} {T : 
X → X} {U : SetRel X X} {n : ℕ} {F : Set X} {s t : Finset X},   Dynamics.IsDynNe
tIn T F U n ↑s → Dynamics.IsDynCoverOf…
-/
lemma netMaxcard_le_coverMincard (T : X → X) (F : Set X) (n : ℕ) :
    netMaxcard T F U n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · obtain ⟨t, t_cover, t_mincard⟩ := (coverMincard_finite_iff T F U n).1 h
    rw [← t_mincard]
    exact iSup₂_le fun s s_net ↦ Nat.cast_le.2 (s_net.card_le_card_of_isDynCoverOf t_cover)

/-- Given an entourage `U` and a time `n`, a minimal dynamical cover by `U ○ U` has a smaller
  cardinality than a maximal dynamical net by `U`. This lemma is the second of two key results to
  compare two versions topological entropy: with cover and with nets. -/
/-
**Dynamics.coverMincard_le_netMaxcard** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_le_netMaxcard (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] 
(n : Nat) : coverMincard T F (U ○ U) n <= netMaxcard T F U n
参数：T : X -> X；F : Set X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.netMaxcard_finite_iff`：netMaxcard_finite_iff (T : X -> X) (F : 
Set X) (U : SetRel X X) (n : Nat) : netMaxcard T F U n < ⊤ ↔ exists s : Finset X
, IsDynNetIn T F U n…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Dynamics.IsDynCoverOf.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set X) (U 
: SetRel X X) (n : ℕ) (s : Set X),   Dynamics.IsDynCoverOf T F U n s = (Dynamics
.dynEntourage T …
· 使用引理 `UniformSpace.isCover_iff_subset_iUnion_ball`：isCover_iff_subset_iUnion_b
all {U : SetRel β β} [U.IsSymm] {s N : Set β} : U.IsCover s N ↔ s subseteq ⋃ y i
n N, ball y U
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwiseDisjoint_insert`：pairwiseDisjoint_insert {i : ι} : (insert i
 s).PairwiseDisjoint f ↔ s.PairwiseDisjoint f ∧ forall j in s, i != j -> Disjoin
t (f i) (f j)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Dynamics.mem_ball_dynEntourage_comp`：mem_ball_dynEntourage_comp (T : X -
> X) (n : Nat) {U : SetRel X X} [U.IsSymm] (x y : X) (h : (ball x (dynEntourage 
T U n) inter ball y (dynE…
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Dynamics.IsDynNetIn.card_le_netMaxcard`：∀ {X : Type u_1} {T : X → X} {U 
: SetRel X X} {n : ℕ} {F : Set X} {s : Finset X},   Dynamics.IsDynNetIn T F U n 
↑s → ↑s.card ≤ Dynamics.netM…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Given an entourage `U` and a time `n`, a minimal dynamical cover by `U ○ U` has 
a smaller
  cardinality than a maximal dynamical net by `U`. This lemma is the second of t
wo key results to
  compare two versions topological entropy: with cover and with nets.
-/
lemma coverMincard_le_netMaxcard (T : X → X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ netMaxcard T F U n := by
  classical
  -- WLOG, there exists a maximal dynamical net `s`.
  rcases eq_top_or_lt_top (netMaxcard T F U n) with h | h
  · exact h ▸ le_top
  obtain ⟨s, s_net, s_card⟩ := (netMaxcard_finite_iff T F U n).1 h
  rw [← s_card]
  apply IsDynCoverOf.coverMincard_le_card
  --  We have to check that `s` is a cover for `dynEntourage T F (U ○ U) n`.
  -- If `s` is not a cover, then we can add to `s` a point `x` which is not covered
  -- and get a new net. This contradicts the maximality of `s`.
  rw [IsDynCoverOf, isCover_iff_subset_iUnion_ball]
  by_contra h
  obtain ⟨x, x_F, x_uncov⟩ := not_subset.1 h
  simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
  have larger_net : IsDynNetIn T F U n (insert x s) := by
    refine ⟨insert_subset x_F s_net.1, pairwiseDisjoint_insert.2 ⟨s_net.2, ?_⟩⟩
    refine fun y y_s _ ↦ disjoint_left.2 fun z z_x z_y ↦ x_uncov y y_s ?_
    exact mem_ball_dynEntourage_comp T n x y (nonempty_of_mem ⟨z_x, z_y⟩)
  rw [← s.coe_insert x] at larger_net
  apply larger_net.card_le_netMaxcard.not_gt
  rw [← s_card, Nat.cast_lt]
  refine (lt_add_one s.card).trans_eq (s.card_insert_of_notMem fun x_s ↦ ?_).symm
  exact x_uncov x x_s (ball_mono (dynEntourage_monotone T n SetRel.left_subset_comp) x <|
    SetRel.rfl (dynEntourage T U n))

/-! ### Net entropy of entourages -/

open ENNReal EReal ExpGrowth Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `limsup`, and is chosen as the default definition. -/
/-
**Dynamics.netEntropyEntourage** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X)
参数：T : X -> X；F : Set X；U : SetRel X X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of an entourage `U`, defined as the exponential rate of growth of th
e size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended rea
l numbers
`[-∞,+∞]`. This version uses a `limsup`, and is chosen as the default definition
.
-/
noncomputable def netEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthSup fun n : ℕ ↦ netMaxcard T F U n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `liminf`, and is an alternative definition. -/
/-
**Dynamics.netEntropyInfEntourage** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage (T : X -> X) (F : Set X) (U : SetRel X X)
参数：T : X -> X；F : Set X；U : SetRel X X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of an entourage `U`, defined as the exponential rate of growth of th
e size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended rea
l numbers
`[-∞,+∞]`. This version uses a `liminf`, and is an alternative definition.
-/
noncomputable def netEntropyInfEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthInf fun n : ℕ ↦ netMaxcard T F U n
/-
**Dynamics.netEntropyInfEntourage_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_antitone (T : X -> X) (F : Set X) : Antitone fun U 
: SetRel X X => netEntropyInfEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_antitone`：netMaxcard_antitone (T : X -> X) (F : Set 
X) (n : Nat) : Antitone fun U : SetRel X X => netMaxcard T F U n
-/
lemma netEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ netEntropyInfEntourage T F U :=
  fun _ _ U_V ↦ expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)
/-
**Dynamics.netEntropyEntourage_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage_antitone (T : X -> X) (F : Set X) : Antitone fun U : S
etRel X X => netEntropyEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_antitone`：netMaxcard_antitone (T : X -> X) (F : Set 
X) (n : Nat) : Antitone fun U : SetRel X X => netMaxcard T F U n
-/
lemma netEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ netEntropyEntourage T F U :=
  fun _ _ U_V ↦ expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)
/-
**Dynamics.netEntropyInfEntourage_le_netEntropyEntourage** 是 Mathlib 中的一个引理，位于命名
空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_le_netEntropyEntourage (T : X -> X) (F : Set X) (U 
: SetRel X X) : netEntropyInfEntourage T F U <= netEntropyEntourage T F U
参数：T : X -> X；F : Set X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_le_expGrowthSup`：expGrowthInf_le_expGrowthSup : e
xpGrowthInf u <= expGrowthSup u
-/
lemma netEntropyInfEntourage_le_netEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :
    netEntropyInfEntourage T F U ≤ netEntropyEntourage T F U :=
  expGrowthInf_le_expGrowthSup

@[simp]
/-
**Dynamics.netEntropyEntourage_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage_empty : netEntropyEntourage T ∅ U = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.netEntropyEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set
 X) (U : SetRel X X),   Dynamics.netEntropyEntourage T F U = ExpGrowth.expGrowth
Sup fun n => ↑(Dynamics…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.netMaxcard_empty`：netMaxcard_empty : netMaxcard T ∅ U n = 0
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma netEntropyEntourage_empty : netEntropyEntourage T ∅ U = ⊥ := by
  rw [netEntropyEntourage, ← expGrowthSup_zero]
  congr
  simp only [netMaxcard_empty, ENat.toENNReal_zero, Pi.zero_def]

@[simp]
/-
**Dynamics.netEntropyInfEntourage_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_empty : netEntropyInfEntourage T ∅ U = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用引理 `Dynamics.netEntropyInfEntourage_le_netEntropyEntourage`：netEntropyInfEnt
ourage_le_netEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) : netEnt
ropyInfEntourage T F U <= netEntropyEntourag…
· 使用引理 `Dynamics.netEntropyEntourage_empty`：netEntropyEntourage_empty : netEntro
pyEntourage T ∅ U = ⊥
-/
lemma netEntropyInfEntourage_empty : netEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (netEntropyInfEntourage_le_netEntropyEntourage T ∅ U) netEntropyEntourage_empty
/-
**Dynamics.netEntropyInfEntourage_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X 
X) : 0 <= netEntropyInfEntourage T F U
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.expGrowthInf_nonneg`：∀ {u : ℕ → ENNReal}, Monotone u → u ≠ 0 → 
0 ≤ ExpGrowth.expGrowthInf u
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_monotone_time`：netMaxcard_monotone_time (T : X -> X)
 (F : Set X) (U : SetRel X X) : Monotone fun n : Nat => netMaxcard T F U n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Dynamics.netMaxcard_zero`：netMaxcard_zero (T : X -> X) (h : F.Nonempty) 
(U : SetRel X X) : netMaxcard T F U 0 = 1
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
lemma netEntropyInfEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ netEntropyInfEntourage T F U := by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n ↦ ENat.toENNReal_mono (netMaxcard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [netMaxcard_zero T h U, Pi.zero_apply, ENat.toENNReal_one]
    exact one_ne_zero
/-
**Dynamics.netEntropyEntourage_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X) 
: 0 <= netEntropyEntourage T F U
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.netEntropyInfEntourage_nonneg`：netEntropyInfEntourage_nonneg (T
 : X -> X) (h : F.Nonempty) (U : SetRel X X) : 0 <= netEntropyInfEntourage T F U
· 使用引理 `Dynamics.netEntropyInfEntourage_le_netEntropyEntourage`：netEntropyInfEnt
ourage_le_netEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) : netEnt
ropyInfEntourage T F U <= netEntropyEntourag…
-/
lemma netEntropyEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ netEntropyEntourage T F U :=
  (netEntropyInfEntourage_nonneg T h U).trans (netEntropyInfEntourage_le_netEntropyEntourage T F U)
/-
**Dynamics.netEntropyInfEntourage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_univ (T : X -> X) {F : Set X} (h : F.Nonempty) : ne
tEntropyInfEntourage T F univ = 0
参数：T : X -> X；h : F.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthInf_const`：expGrowthInf_const (h : b != 0) (h' : b !=
 ∞) : expGrowthInf (fun _ => b) = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Dynamics.netEntropyInfEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F : 
Set X) (U : SetRel X X),   Dynamics.netEntropyInfEntourage T F U = ExpGrowth.exp
GrowthInf fun n => ↑(Dynam…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.netMaxcard_univ`：netMaxcard_univ (T : X -> X) (h : F.Nonempty) 
(n : Nat) : netMaxcard T F univ n = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma netEntropyInfEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropyInfEntourage T F univ = 0 := by
  rw [← expGrowthInf_const one_ne_zero one_ne_top, netEntropyInfEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]
/-
**Dynamics.netEntropyEntourage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage_univ (T : X -> X) {F : Set X} (h : F.Nonempty) : netEn
tropyEntourage T F univ = 0
参数：T : X -> X；h : F.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthSup_const`：expGrowthSup_const (h : b != 0) (h' : b !=
 ∞) : expGrowthSup (fun _ => b) = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Dynamics.netEntropyEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set
 X) (U : SetRel X X),   Dynamics.netEntropyEntourage T F U = ExpGrowth.expGrowth
Sup fun n => ↑(Dynamics…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.netMaxcard_univ`：netMaxcard_univ (T : X -> X) (h : F.Nonempty) 
(n : Nat) : netMaxcard T F univ n = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma netEntropyEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropyEntourage T F univ = 0 := by
  rw [← expGrowthSup_const one_ne_zero one_ne_top, netEntropyEntourage]
  simp only [netMaxcard_univ T h, ENat.toENNReal_one]
/-
**Dynamics.netEntropyInfEntourage_le_coverEntropyInfEntourage** 是 Mathlib 中的一个引理
，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_le_coverEntropyInfEntourage (T : X -> X) (F : Set X
) : netEntropyInfEntourage T F U <= coverEntropyInfEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_le_coverMincard`：netMaxcard_le_coverMincard (T : X -
> X) (F : Set X) (n : Nat) : netMaxcard T F U n <= coverMincard T F U n
-/
lemma netEntropyInfEntourage_le_coverEntropyInfEntourage (T : X → X) (F : Set X) :
    netEntropyInfEntourage T F U ≤ coverEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)
/-
**Dynamics.coverEntropyInfEntourage_le_netEntropyInfEntourage** 是 Mathlib 中的一个引理
，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_le_netEntropyInfEntourage (T : X -> X) (F : Set X
) [U.IsRefl] [U.IsSymm] : coverEntropyInfEntourage T F (U ○ U) <= netEntropyInfE
ntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_le_netMaxcard`：coverMincard_le_netMaxcard (T : X -
> X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : Nat) : coverMincard T F (U ○ U) n <=
 netMaxcard T F U n
-/
lemma coverEntropyInfEntourage_le_netEntropyInfEntourage (T : X → X) (F : Set X) [U.IsRefl]
    [U.IsSymm] :
    coverEntropyInfEntourage T F (U ○ U) ≤ netEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)
/-
**Dynamics.netEntropyEntourage_le_coverEntropyEntourage** 是 Mathlib 中的一个引理，位于命名空
间 `Dynamics`。
形式化陈述：netEntropyEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) : ne
tEntropyEntourage T F U <= coverEntropyEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_le_coverMincard`：netMaxcard_le_coverMincard (T : X -
> X) (F : Set X) (n : Nat) : netMaxcard T F U n <= coverMincard T F U n
-/
lemma netEntropyEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) :
    netEntropyEntourage T F U ≤ coverEntropyEntourage T F U :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (netMaxcard_le_coverMincard T F n)
/-
**Dynamics.coverEntropyEntourage_le_netEntropyEntourage** 是 Mathlib 中的一个引理，位于命名空
间 `Dynamics`。
形式化陈述：coverEntropyEntourage_le_netEntropyEntourage (T : X -> X) (F : Set X) [U.I
sRefl] [U.IsSymm] : coverEntropyEntourage T F (U ○ U) <= netEntropyEntourage T F
 U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_le_netMaxcard`：coverMincard_le_netMaxcard (T : X -
> X) (F : Set X) [U.IsRefl] [U.IsSymm] (n : Nat) : coverMincard T F (U ○ U) n <=
 netMaxcard T F U n
-/
lemma coverEntropyEntourage_le_netEntropyEntourage (T : X → X) (F : Set X) [U.IsRefl] [U.IsSymm] :
    coverEntropyEntourage T F (U ○ U) ≤ netEntropyEntourage T F U :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_le_netMaxcard T F n)

/-! ### Relationship with entropy via covers -/

variable [UniformSpace X] (T : X → X) (F : Set X)

/-- Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topological entropy using
  covers, so there is no need to define a new notion of topological entropy. This version of the
/-
**Dynamics.relates** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
  theorem relates the `liminf` versions of topological entropy. -/
/-
**Dynamics.coverEntropyInf_eq_iSup_netEntropyInfEntourage** 是 Mathlib 中的一个定理，位于命
名空间 `Dynamics`。
形式化陈述：coverEntropyInf_eq_iSup_netEntropyInfEntourage : coverEntropyInf T F = ⨆ U
 in 𝓤 X, netEntropyInfEntourage T F U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInfEntourage_antitone`：coverEntropyInfEntourage_ant
itone (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyInfE
ntourage T F U
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_netEntropyInfEntourage`：coverEntrop
yInfEntourage_le_netEntropyInfEntourage (T : X -> X) (F : Set X) [U.IsRefl] [U.I
sSymm] : coverEntropyInfEntourage T F (U ○ U) <= …
· 使用引理 `Dynamics.netEntropyInfEntourage_antitone`：netEntropyInfEntourage_antiton
e (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => netEntropyInfEntoura
ge T F U
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用引理 `Dynamics.netEntropyInfEntourage_le_coverEntropyInfEntourage`：netEntropyI
nfEntourage_le_coverEntropyInfEntourage (T : X -> X) (F : Set X) : netEntropyInf
Entourage T F U <= coverEntropyInfEntourage T F U

--- 原说明 ---
Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topol
ogical entropy using
  covers, so there is no need to define a new notion of topological entropy. Thi
s version of the
  theorem relates the `liminf` versions of topological entropy.
-/
theorem coverEntropyInf_eq_iSup_netEntropyInfEntourage :
    coverEntropyInf T F = ⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
    have := isRefl_of_mem_uniformity V_uni
    apply (coverEntropyInfEntourage_antitone T F V_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyInfEntourage_le_netEntropyInfEntourage T F
  · apply (netEntropyInfEntourage_antitone T F SetRel.symmetrize_subset_self).trans
    apply (le_iSup₂ (SetRel.symmetrize U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyInfEntourage_le_coverEntropyInfEntourage T F

/-- Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topological entropy using
  covers, so there is no need to define a new notion of topological entropy. This version of the
/-
**Dynamics.relates** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
  theorem relates the `limsup` versions of topological entropy. -/
/-
**Dynamics.coverEntropy_eq_iSup_netEntropyEntourage** 是 Mathlib 中的一个定理，位于命名空间 `D
ynamics`。
形式化陈述：coverEntropy_eq_iSup_netEntropyEntourage : coverEntropy T F = ⨆ U in 𝓤 X, 
netEntropyEntourage T F U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_antitone`：coverEntropyEntourage_antitone 
(T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyEntourage 
T F U
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `isRefl_of_mem_uniformity`：isRefl_of_mem_uniformity {s : SetRel α α} (h :
 s in 𝓤 α) : s.IsRefl
· 使用引理 `Dynamics.coverEntropyEntourage_le_netEntropyEntourage`：coverEntropyEntou
rage_le_netEntropyEntourage (T : X -> X) (F : Set X) [U.IsRefl] [U.IsSymm] : cov
erEntropyEntourage T F (U ○ U) <= netEntrop…
· 使用引理 `Dynamics.netEntropyEntourage_antitone`：netEntropyEntourage_antitone (T :
 X -> X) (F : Set X) : Antitone fun U : SetRel X X => netEntropyEntourage T F U
· 使用引理 `SetRel.symmetrize_subset_self`：symmetrize_subset_self : R.symmetrize sub
seteq R
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用引理 `Dynamics.netEntropyEntourage_le_coverEntropyEntourage`：netEntropyEntoura
ge_le_coverEntropyEntourage (T : X -> X) (F : Set X) : netEntropyEntourage T F U
 <= coverEntropyEntourage T F U

--- 原说明 ---
Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topol
ogical entropy using
  covers, so there is no need to define a new notion of topological entropy. Thi
s version of the
  theorem relates the `limsup` versions of topological entropy.
-/
theorem coverEntropy_eq_iSup_netEntropyEntourage :
    coverEntropy T F = ⨆ U ∈ 𝓤 X, netEntropyEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · obtain ⟨V, V_uni, V_symm, V_comp_U⟩ := comp_symm_mem_uniformity_sets U_uni
    apply (coverEntropyEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    have := isRefl_of_mem_uniformity V_uni
    exact coverEntropyEntourage_le_netEntropyEntourage T F
  · apply (netEntropyEntourage_antitone T F SetRel.symmetrize_subset_self).trans
    apply (le_iSup₂ (SetRel.symmetrize U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyEntourage_le_coverEntropyEntourage T F
/-
**Dynamics.coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage** 是 Mathlib 中的一个
引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage {ι : Sort*} {p : ι ->
 Prop} {s : ι -> SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) :
 coverEntropyInf T F = ⨆ (i : ι) (_ : p i), netEntropyInfEntourage T F (s i)
参数：h : (𝓤 X).HasBasis p s；T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.coverEntropyInf_eq_iSup_netEntropyInfEntourage`：coverEntropyInf
_eq_iSup_netEntropyInfEntourage : coverEntropyInf T F = ⨆ U in 𝓤 X, netEntropyIn
fEntourage T F U
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.netEntropyInfEntourage_antitone`：netEntropyInfEntourage_antiton
e (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => netEntropyInfEntoura
ge T F U
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), netEntropyInfEntourage T F (s i) := by
  rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyInfEntourage_antitone T F si_U).trans
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ netEntropyInfEntourage T F (s i)) i h_i
/-
**Dynamics.coverEntropy_eq_iSup_basis_netEntropyEntourage** 是 Mathlib 中的一个引理，位于命
名空间 `Dynamics`。
形式化陈述：coverEntropy_eq_iSup_basis_netEntropyEntourage {ι : Sort*} {p : ι -> Prop}
 {s : ι -> SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) : cover
Entropy T F = ⨆ (i : ι) (_ : p i), netEntropyEntourage T F (s i)
参数：h : (𝓤 X).HasBasis p s；T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.coverEntropy_eq_iSup_netEntropyEntourage`：coverEntropy_eq_iSup_
netEntropyEntourage : coverEntropy T F = ⨆ U in 𝓤 X, netEntropyEntourage T F U
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.netEntropyEntourage_antitone`：netEntropyEntourage_antitone (T :
 X -> X) (F : Set X) : Antitone fun U : SetRel X X => netEntropyEntourage T F U
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma coverEntropy_eq_iSup_basis_netEntropyEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), netEntropyEntourage T F (s i) := by
  rw [coverEntropy_eq_iSup_netEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  apply (netEntropyEntourage_antitone T F si_U).trans _
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ netEntropyEntourage T F (s i)) i h_i
/-
**Dynamics.netEntropyInfEntourage_le_coverEntropyInf** 是 Mathlib 中的一个引理，位于命名空间 `
Dynamics`。
形式化陈述：netEntropyInfEntourage_le_coverEntropyInf (h : U in 𝓤 X) : netEntropyInfEn
tourage T F U <= coverEntropyInf T F
参数：h : U in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dynamics.coverEntropyInf_eq_iSup_netEntropyInfEntourage`：coverEntropyInf
_eq_iSup_netEntropyInfEntourage : coverEntropyInf T F = ⨆ U in 𝓤 X, netEntropyIn
fEntourage T F U
-/
lemma netEntropyInfEntourage_le_coverEntropyInf (h : U ∈ 𝓤 X) :
    netEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  coverEntropyInf_eq_iSup_netEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ netEntropyInfEntourage T F U) U h
/-
**Dynamics.netEntropyEntourage_le_coverEntropy** 是 Mathlib 中的一个引理，位于命名空间 `Dynami
cs`。
形式化陈述：netEntropyEntourage_le_coverEntropy (h : U in 𝓤 X) : netEntropyEntourage T
 F U <= coverEntropy T F
参数：h : U in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dynamics.coverEntropy_eq_iSup_netEntropyEntourage`：coverEntropy_eq_iSup_
netEntropyEntourage : coverEntropy T F = ⨆ U in 𝓤 X, netEntropyEntourage T F U
-/
lemma netEntropyEntourage_le_coverEntropy (h : U ∈ 𝓤 X) :
    netEntropyEntourage T F U ≤ coverEntropy T F :=
  coverEntropy_eq_iSup_netEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ netEntropyEntourage T F U) U h

end Dynamics

