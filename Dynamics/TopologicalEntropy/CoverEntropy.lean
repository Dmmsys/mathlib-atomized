/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage

/-!
# Topological entropy via covers

We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single theorem (`subset_restriction_entropy` in `TopologicalEntropy.Semiconj`) will give the
equivalence between both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal` numbers.

## Main definitions
- `IsDynCoverOf`: property that dynamical balls centered on a subset `s` cover a subset `F`.
- `coverMincard`: minimal cardinality of a dynamical cover. Takes values in `ℕ∞`.
- `coverEntropyInfEntourage`/`coverEntropyEntourage`: exponential growth of `coverMincard`.
  The former is defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `coverEntropyInf`/`coverEntropy`: supremum of `coverEntropyInfEntourage`/`coverEntropyEntourage`
  over all entourages (or limit as the entourages go to the diagonal). These are Bowen-Dinaburg's
  versions of the topological entropy with covers. Take values in `EReal`.

## Implementation notes
There are two competing definitions of topological entropy in this file: one uses a `liminf`,
the other a `limsup`. These two topological entropies are equal as soon as they are applied to an
invariant subset by theorem `coverEntropyInf_eq_coverEntropy`. We choose the default definition
to be the definition using a `limsup`, and give it the simpler name `coverEntropy` (instead of
`coverEntropySup`). Theorems about the topological entropy of invariant subsets will be stated
using only `coverEntropy`.

## Main results
- `IsDynCoverOf.iterate_le_pow`: given a dynamical cover at time `n`, creates dynamical covers
  at all iterates `n * m` with controlled cardinality.
- `IsDynCoverOf.coverEntropyEntourage_le_log_card_div`: upper bound on `coverEntropyEntourage`
  given any dynamical cover.
- `coverEntropyInf_eq_coverEntropy`: equality between the notions of topological entropy defined
  with a `liminf` and a `limsup`.

## Tags
cover, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

@[expose] public section

open Set SetRel Uniformity UniformSpace
open scoped Finset

namespace Dynamics

variable {X : Type*} {T : X → X} {U V : SetRel X X} {n : ℕ} {F s : Set X} {m n : ℕ}

/-! ### Dynamical covers -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` is a `(U, n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an orbit of length `n`
of a point in `s`. -/
/-
**Dynamics.IsDynCoverOf** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：IsDynCoverOf (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) (s : Set 
X) : Prop
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` is a `(U, 
n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an o
rbit of length `n`
of a point in `s`.
-/
def IsDynCoverOf (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) (s : Set X) : Prop :=
  IsCover (dynEntourage T U n) F s
/-
**Dynamics.IsDynCoverOf.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F s : Set X} {m n : ℕ},   m
 ≤ n → Dynamics.IsDynCoverOf T F U n s → Dynamics.IsDynCoverOf T F U m s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.mono_entourage`：∀ {X : Type u_1} {U V : SetRel X X} {s N 
: Set X}, U ⊆ V → U.IsCover s N → V.IsCover s N
· 使用引理 `Dynamics.dynEntourage_mono`：dynEntourage_mono (hUV : U subseteq V) (hmn 
: m <= n) : dynEntourage T U n subseteq dynEntourage T V m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma IsDynCoverOf.of_le (m_n : m ≤ n) (h : IsDynCoverOf T F U n s) : IsDynCoverOf T F U m s :=
  h.mono_entourage <| by gcongr
/-
**Dynamics.IsDynCoverOf.of_entourage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.
IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U V : SetRel X X} {F s : Set X} {n : ℕ},   U
 ⊆ V → Dynamics.IsDynCoverOf T F U n s → Dynamics.IsDynCoverOf T F V n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.mono_entourage`：∀ {X : Type u_1} {U V : SetRel X X} {s N 
: Set X}, U ⊆ V → U.IsCover s N → V.IsCover s N
· 使用引理 `Dynamics.dynEntourage_mono`：dynEntourage_mono (hUV : U subseteq V) (hmn 
: m <= n) : dynEntourage T U n subseteq dynEntourage T V m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma IsDynCoverOf.of_entourage_subset (U_V : U ⊆ V) (h : IsDynCoverOf T F U n s) :
    IsDynCoverOf T F V n s := h.mono_entourage <| by gcongr
/-
**Dynamics.isDynCoverOf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {s : Set X} {n : ℕ}, Dynamic
s.IsDynCoverOf T ∅ U n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.empty`：∀ {X : Type u_1} {U : SetRel X X} {N : Set X}, U.I
sCover ∅ N
-/
@[simp] lemma isDynCoverOf_empty : IsDynCoverOf T ∅ U n s := .empty
/-
**Dynamics.isDynCoverOf_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F : Set X} {n : ℕ}, Dynamic
s.IsDynCoverOf T F U n ∅ ↔ F = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isDynCoverOf_empty_right : IsDynCoverOf T F U n ∅ ↔ F = ∅ := by simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h
/-
**Dynamics.isDynCoverOf_zero** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：isDynCoverOf_zero (T : X -> X) (F : Set X) (U : SetRel X X) (h : s.Nonempt
y) : IsDynCoverOf T F U 0 s
参数：T : X -> X；F : Set X；U : SetRel X X；h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.dynEntourage_zero`：∀ {X : Type u_1} {T : X → X} {U : SetRel X X
}, Dynamics.dynEntourage T U 0 = Set.univ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isDynCoverOf_zero (T : X → X) (F : Set X) (U : SetRel X X) (h : s.Nonempty) :
    IsDynCoverOf T F U 0 s := by simp [IsDynCoverOf, h]
/-
**Dynamics.isDynCoverOf_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：isDynCoverOf_univ (T : X -> X) (F : Set X) (n : Nat) (h : s.Nonempty) : Is
DynCoverOf T F univ n s
参数：T : X -> X；F : Set X；n : Nat；h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Dynamics.dynEntourage_univ`：dynEntourage_univ {T : X -> X} {n : Nat} : d
ynEntourage T univ n = univ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isDynCoverOf_univ (T : X → X) (F : Set X) (n : ℕ) (h : s.Nonempty) :
    IsDynCoverOf T F univ n s := by simp [IsDynCoverOf, h]
/-
**Dynamics.IsDynCoverOf.nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDyn
CoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F : Set X} {n : ℕ} [U.IsSym
m] {s : Finset X},   Dynamics.IsDynCoverOf T F U n ↑s →     ∃ t,       Dynamics.
IsDynCoverOf T F U n ↑t ∧         t.card ≤ s.card ∧ ∀ x ∈ t, (UniformSpace.ball 
x (Dynamics.dynEntourage T U n) ∩ F).Nonempty
参数：UniformSpace.ball x (Dynamics.dynEntourage T U n) ∩ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
-/
lemma IsDynCoverOf.nonempty_inter [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s) :
    ∃ t : Finset X, IsDynCoverOf T F U n t ∧ #t ≤ #s ∧
      ∀ x ∈ t, (ball x (dynEntourage T U n) ∩ F).Nonempty := by
  classical
  use {x ∈ s | (ball x (dynEntourage T U n) ∩ F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F ↦ ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, (dynEntourage T U n).symm y_Bz, y_F⟩, y_Bz⟩

/-- From a dynamical cover `s` with entourage `U` and time `m`, we construct covers with entourage
`U ○ U` and any multiple `m * n` of `m` with controlled cardinality. This lemma is the first step
in a submultiplicative-like property of `coverMincard`, with consequences such as explicit bounds
for the topological entropy (`coverEntropyInfEntourage_le_card_div`) and an equality between
two notions of topological entropy (`coverEntropyInf_eq_coverEntropySup_of_inv`). -/
/-
**Dynamics.IsDynCoverOf.iterate_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDyn
CoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F : Set X} {m : ℕ},   Set.M
apsTo T F F →     ∀ [U.IsSymm] (n : ℕ) {s : Finset X},       Dynamics.IsDynCover
Of T F U m ↑s → ∃ t, Dynamics.IsDynCoverOf T F (U.comp U) (m * n) ↑t ∧ t.card ≤ 
s.card ^ n
参数：n : ℕ；U.comp U；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Dynamics.IsDynCoverOf.nonempty`：∀ {X : Type u_1} {T : X → X} {U : SetRel
 X X} {F s : Set X} {n : ℕ},   F.Nonempty → Dynamics.IsDynCoverOf T F U n s → s.
Nonempty
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `Dynamics.isDynCoverOf_zero`：isDynCoverOf_zero (T : X -> X) (F : Set X) (
U : SetRel X X) (h : s.Nonempty) : IsDynCoverOf T F U 0 s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.div_lt_of_lt_mul`：∀ {m n k : ℕ}, m < n * k → m / n < k
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
From a dynamical cover `s` with entourage `U` and time `m`, we construct covers 
with entourage
`U ○ U` and any multiple `m * n` of `m` with controlled cardinality. This lemma 
is the first step
in a submultiplicative-like property of `coverMincard`, with consequences such a
s explicit bounds
for the topological entropy (`coverEntropyInfEntourage_le_card_div`) and an equa
lity between
two notions of topological entropy (`coverEntropyInf_eq_coverEntropySup_of_inv`)
.
-/
lemma IsDynCoverOf.iterate_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (n : ℕ) {s : Finset X}
    (h : IsDynCoverOf T F U m s) :
    ∃ t : Finset X, IsDynCoverOf T F (U ○ U) (m * n) t ∧ t.card ≤ s.card ^ n := by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := F_nemp.nonempty
  have s_nemp := h.nonempty F_nemp
  obtain ⟨x, x_F⟩ := F_nemp
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact ⟨isDynCoverOf_zero T F (U ○ U) (singleton_nonempty x),
      one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n⟩
  -- The proof goes as follows. Given an orbit of length `(m * n)` starting from `y`, each of its
  -- iterates `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to a point of `s`.
  -- Conversely, given a sequence `t 0`, `t 1`, `t 2` of points in `s`, we choose a point
  -- `z = dyncover t` such that  `z`, `T^[m] z`, `T^[m]^[2] z` ... are `(dynEntourage T U m)`-close
  --  to `t 0`, `t 1`, `t 2`... Then  `y`, `T^[m] y`, `T^[m]^[2] y` ... are
  -- `(dynEntourage T (U ○ U) m)`-close to `z`, `T^[m] z`, `T^[m]^[2] z`, so that the union of such
  -- `z` provides the desired cover. Since there are at most `s.card ^ n` sequences of
  -- length `n` with values in `s`, we get the upper bound we want on the cardinality.
  -- First step: construct `dyncover`. Given `t 0`, `t 1`, `t 2`, if we cannot find such a point
  -- `dyncover t`, we use the dummy `x`.
  have (t : Fin n → s) : ∃ y : X, (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)) ⊆
      ball y (dynEntourage T (U ○ U) (m * n)) := by
    rcases (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)).eq_empty_or_nonempty
      with inter_empt | inter_nemp
    · exact inter_empt ▸ ⟨x, empty_subset _⟩
    · obtain ⟨y, y_int⟩ := inter_nemp
      refine ⟨y, fun z z_int ↦ ?_⟩
      simp only [ball, dynEntourage, Prod.map_iterate, mem_iInter, Set.mem_preimage, Prod.map_apply,
        mem_comp] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball y_int z_int
  choose! dyncover h_dyncover using this
  -- The cover we want is the set of all `dyncover t`, that is, `range dyncover`. We need to check
  -- that it is indeed a `(U ○ U, m * n)` cover, and that its cardinality is at most `card s ^ n`.
  -- Only the first point requires significant work.
  let sn := range dyncover
  refine ⟨sn.toFinset, ?_, ?_⟩
  · -- We implement the argument at the beginning: given `y ∈ F`, we extract `t 0`, `t 1`, `t 2`
    -- such that `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to `t 0`, `t 1`,
    -- `t 2`... Then `dyncover t` is a point of `range dyncover` which satisfies the conclusion
    -- of the lemma.
    rw [Finset.coe_nonempty] at s_nemp
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nemp
    intro y y_F
    have key : ∀ k : Fin n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (dynEntourage T U m) := by
      intro k
      have := h (MapsTo.iterate F_inv (m * k) y_F)
      simp only [Finset.mem_coe] at this
      obtain ⟨z, z_s, hz⟩ := this
      exact ⟨⟨z, z_s⟩, (dynEntourage T U m).symm hz⟩
    choose! t ht using key
    simp only [toFinset_range, Finset.coe_image, Finset.coe_univ, image_univ, mem_range,
      exists_exists_eq_and, sn]
    refine ⟨t, (dynEntourage T (U ○ U) (m * n)).symm <| h_dyncover t <| by simpa using ht⟩
  · rw [toFinset_card]
    apply (Fintype.card_range_le dyncover).trans
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]
/-
**Dynamics.exists_isDynCoverOf_of_isCompact_uniformContinuous** 是 Mathlib 中的一个引理
，位于命名空间 `Dynamics`。
形式化陈述：exists_isDynCoverOf_of_isCompact_uniformContinuous [UniformSpace X] (F_com
p : IsCompact F) (h : UniformContinuous T) (U_uni : U in 𝓤 X) (n : Nat) : exists
 s : Finset X, IsDynCoverOf T F U n s
参数：F_comp : IsCompact F；h : UniformContinuous T；U_uni : U in 𝓤 X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of_uniformity`：symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) 
: exists t in 𝓤 α, SetRel.IsSymm t ∧ t subseteq s
· 使用引理 `Dynamics.dynEntourage_mem_uniformity`：dynEntourage_mem_uniformity [Unifo
rmSpace X] (h : UniformContinuous T) (U_uni : U in 𝓤 X) (n : Nat) : dynEntourage
 T U n in 𝓤 X
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Dynamics.IsDynCoverOf.of_entourage_subset`：∀ {X : Type u_1} {T : X → X} 
{U V : SetRel X X} {F s : Set X} {n : ℕ},   U ⊆ V → Dynamics.IsDynCoverOf T F U 
n s → Dynamics.IsDynCoverOf T F…
· 使用定理 `SetRel.IsCover.of_subset_iUnion_ball`：∀ {β : Type ub} {U : SetRel β β} [
U.IsSymm] {s N : Set β}, s ⊆ ⋃ y ∈ N, UniformSpace.ball y U → U.IsCover s N
-/
lemma exists_isDynCoverOf_of_isCompact_uniformContinuous [UniformSpace X]
    (F_comp : IsCompact F) (h : UniformContinuous T) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), hV, hVsymm, hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ ↦ ball_mem_nhds x uni_ite
  exact ⟨s, .of_entourage_subset hVU <| .of_subset_iUnion_ball s_cover⟩
/-
**Dynamics.exists_isDynCoverOf_of_isCompact_invariant** 是 Mathlib 中的一个引理，位于命名空间 
`Dynamics`。
形式化陈述：exists_isDynCoverOf_of_isCompact_invariant [UniformSpace X] (F_comp : IsCo
mpact F) (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) (n : Nat) : exists s : Finset
 X, IsDynCoverOf T F U n s
参数：F_comp : IsCompact F；F_inv : MapsTo T F F；U_uni : U in 𝓤 X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用定理 `IsCompact.elim_nhds_subcover`：IsCompact.elim_nhds_subcover (hs : IsCompa
ct s) (U : X -> Set X) (hU : forall x in s, U x in 𝓝 x) : exists t : Finset X, (
forall x in t, x i…
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `SetRel.IsCover.of_subset_iUnion_ball`：∀ {β : Type ub} {U : SetRel β β} [
U.IsSymm] {s N : Set β}, s ⊆ ⋃ y ∈ N, UniformSpace.ball y U → U.IsCover s N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Dynamics.dynEntourage_one`：∀ {X : Type u_1} {T : X → X} {U : SetRel X X}
, Dynamics.dynEntourage T U 1 = U
· 使用定理 `Dynamics.IsDynCoverOf.iterate_le_pow`：∀ {X : Type u_1} {T : X → X} {U : 
SetRel X X} {F : Set X} {m : ℕ},   Set.MapsTo T F F →     ∀ [U.IsSymm] (n : ℕ) {
s : Finset X},       Dynam…
· 使用定理 `Dynamics.IsDynCoverOf.of_entourage_subset`：∀ {X : Type u_1} {T : X → X} 
{U V : SetRel X X} {F s : Set X} {n : ℕ},   U ⊆ V → Dynamics.IsDynCoverOf T F U 
n s → Dynamics.IsDynCoverOf T F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma exists_isDynCoverOf_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover (ball · V)
    fun (x : X) _ ↦ ball_mem_nhds x V_uni
  have : IsDynCoverOf T F V 1 s := .of_subset_iUnion_ball <| by simpa using s_cover
  obtain ⟨t, t_dyncover, t_card⟩ := this.iterate_le_pow F_inv n
  rw [one_mul n] at t_dyncover
  exact ⟨t, t_dyncover.of_entourage_subset V_U⟩

/-! ### Minimal cardinality of dynamical covers -/

/-- The smallest cardinality of a `(U, n)`-dynamical cover of `F`. Takes values in `ℕ∞`, and is
  infinite if and only if `F` admits no finite dynamical cover. -/
/-
**Dynamics.coverMincard** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverMincard (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat) : Nat∞
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest cardinality of a `(U, n)`-dynamical cover of `F`. Takes values in `
ℕ∞`, and is
  infinite if and only if `F` admits no finite dynamical cover.
-/
noncomputable def coverMincard (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : ℕ∞)
/-
**Dynamics.IsDynCoverOf.coverMincard_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics
.IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F : Set X} {n : ℕ} {s : Fin
set X},   Dynamics.IsDynCoverOf T F U n ↑s → Dynamics.coverMincard T F U n ≤ ↑s.
card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma IsDynCoverOf.coverMincard_le_card {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverMincard T F U n ≤ s.card :=
  iInf₂_le s h
/-
**Dynamics.coverMincard_monotone_time** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_monotone_time (T : X -> X) (F : Set X) (U : SetRel X X) : Mon
otone fun n : Nat => coverMincard T F U n
参数：T : X -> X；F : Set X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `Dynamics.IsDynCoverOf.of_le`：∀ {X : Type u_1} {T : X → X} {U : SetRel X 
X} {F s : Set X} {m n : ℕ},   m ≤ n → Dynamics.IsDynCoverOf T F U n s → Dynamics
.IsDynCoverOf T F…
-/
lemma coverMincard_monotone_time (T : X → X) (F : Set X) (U : SetRel X X) :
    Monotone fun n : ℕ ↦ coverMincard T F U n :=
  fun _ _ m_n ↦ biInf_mono fun _ h ↦ h.of_le m_n
/-
**Dynamics.coverMincard_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_antitone (T : X -> X) (F : Set X) (n : Nat) : Antitone fun U 
: SetRel X X => coverMincard T F U n
参数：T : X -> X；F : Set X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `Dynamics.IsDynCoverOf.of_entourage_subset`：∀ {X : Type u_1} {T : X → X} 
{U V : SetRel X X} {F s : Set X} {n : ℕ},   U ⊆ V → Dynamics.IsDynCoverOf T F U 
n s → Dynamics.IsDynCoverOf T F…
-/
lemma coverMincard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone fun U : SetRel X X ↦ coverMincard T F U n :=
  fun _ _ U_V ↦ biInf_mono fun _ h ↦ h.of_entourage_subset U_V
/-
**Dynamics.coverMincard_finite_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_finite_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat
) : coverMincard T F U n < ⊤ ↔ exists s : Finset X, IsDynCoverOf T F U n s ∧ s.c
ard = coverMincard T F U n
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
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `Dynamics.coverMincard.eq_1`：∀ {X : Type u_1} (T : X → X) (F : Set X) (U 
: SetRel X X) (n : ℕ),   Dynamics.coverMincard T F U n = ⨅ s, ⨅ (_ : Dynamics.Is
DynCoverOf T F U…
· 使用定理 `iInf₂_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLattice α] {f : (i : ι) → κ i → α},   ⨅ i, ⨅ j, f i j = ⊤ ↔ ∀ (i : ι) (
j …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `ciInf_mem`：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
lemma coverMincard_finite_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynCoverOf T F U n s ∧ s.card = coverMincard T F U n := by
  refine ⟨fun h_fin ↦ ?_, fun ⟨s, _, s_coverMincard⟩ ↦ s_coverMincard ▸ WithTop.coe_lt_top s.card⟩
  obtain ⟨k, k_min⟩ := ENat.ne_top_iff_exists.mp h_fin.ne
  rw [← k_min]
  simp only [Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.natCast_ne_top k
    rw [k_min, coverMincard, iInf₂_eq_top]
    simp only [ENat.natCast_ne_top, imp_false]
    rw [nonempty_subtype, not_exists] at h
    exact h
  have key := ciInf_mem fun s : {s : Finset X // IsDynCoverOf T F U n s} ↦ (s.val.card : ℕ∞)
  rw [coverMincard, iInf_subtype'] at k_min
  rw [← k_min, mem_range, Subtype.exists] at key
  simp only [Nat.cast_inj, exists_prop] at key
  exact key

@[simp]
/-
**Dynamics.coverMincard_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_empty : coverMincard T ∅ U n = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma coverMincard_empty : coverMincard T ∅ U n = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact sInf_le (by simp [IsDynCoverOf])
/-
**Dynamics.coverMincard_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_eq_zero_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Na
t) : coverMincard T F U n = 0 ↔ F = ∅
参数：T : X -> X；F : Set X；U : SetRel X X；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coverMincard_eq_zero_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T F U n = 0 ↔ F = ∅ := by
  simp [coverMincard, ENat.iInf_eq_zero]
/-
**Dynamics.one_le_coverMincard_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：one_le_coverMincard_iff (T : X -> X) (F : Set X) (U : SetRel X X) (n : Nat
) : 1 <= coverMincard T F U n ↔ F.Nonempty
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
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `Dynamics.coverMincard_eq_zero_iff`：coverMincard_eq_zero_iff (T : X -> X)
 (F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n = 0 ↔ F = ∅
-/
lemma one_le_coverMincard_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    1 ≤ coverMincard T F U n ↔ F.Nonempty := by
  rw [Order.one_le_iff_ne_zero, nonempty_iff_ne_empty, not_iff_not]
  exact coverMincard_eq_zero_iff T F U n
/-
**Dynamics.coverMincard_zero** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_zero (T : X -> X) (h : F.Nonempty) (U : SetRel X X) : coverMi
ncard T F U 0 = 1
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Dynamics.isDynCoverOf_zero`：isDynCoverOf_zero (T : X -> X) (F : Set X) (
U : SetRel X X) (h : s.Nonempty) : IsDynCoverOf T F U 0 s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Dynamics.one_le_coverMincard_iff`：one_le_coverMincard_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : 1 <= coverMincard T F U n ↔ F.Nonempty
-/
lemma coverMincard_zero (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    coverMincard T F U 0 = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]
/-
**Dynamics.coverMincard_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_univ (T : X -> X) (h : F.Nonempty) (n : Nat) : coverMincard T
 F univ n = 1
参数：T : X -> X；h : F.Nonempty；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Dynamics.isDynCoverOf_univ`：isDynCoverOf_univ (T : X -> X) (F : Set X) (
n : Nat) (h : s.Nonempty) : IsDynCoverOf T F univ n s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Dynamics.one_le_coverMincard_iff`：one_le_coverMincard_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : 1 <= coverMincard T F U n ↔ F.Nonempty
-/
lemma coverMincard_univ (T : X → X) (h : F.Nonempty) (n : ℕ) : coverMincard T F univ n = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]
/-
**Dynamics.coverMincard_mul_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_mul_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m n : Nat) : co
verMincard T F (U ○ U) (m * n) <= coverMincard T F U m ^ n
参数：F_inv : MapsTo T F F；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Dynamics.coverMincard_empty`：coverMincard_empty : coverMincard T ∅ U n =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Dynamics.coverMincard_zero`：coverMincard_zero (T : X -> X) (h : F.Nonemp
ty) (U : SetRel X X) : coverMincard T F U 0 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `ENat.top_pow`：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `Dynamics.IsDynCoverOf.iterate_le_pow`：∀ {X : Type u_1} {T : X → X} {U : 
SetRel X X} {F : Set X} {m : ℕ},   Set.MapsTo T F F →     ∀ [U.IsSymm] (n : ℕ) {
s : Finset X},       Dynam…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
lemma coverMincard_mul_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m n : ℕ) :
    coverMincard T F (U ○ U) (m * n) ≤ coverMincard T F U m ^ n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · simp
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · simp [*]
  · obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U m).1 h
    obtain ⟨t, t_cover, t_sn⟩ := s_cover.iterate_le_pow F_inv n
    rw [← s_coverMincard]
    exact t_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 t_sn)
/-
**Dynamics.coverMincard_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m_pos : 0 < m) (n :
 Nat) : coverMincard T F (U ○ U) n <= coverMincard T F U m ^ (n / m + 1)
参数：F_inv : MapsTo T F F；m_pos : 0 < m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverMincard_monotone_time`：coverMincard_monotone_time (T : X -
> X) (F : Set X) (U : SetRel X X) : Monotone fun n : Nat => coverMincard T F U n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_mul_div_succ`：∀ {b : ℕ} (a : ℕ), 0 < b → a < b * (a / b + 1)
· 使用引理 `Dynamics.coverMincard_mul_le_pow`：coverMincard_mul_le_pow (F_inv : MapsT
o T F F) [U.IsSymm] (m n : Nat) : coverMincard T F (U ○ U) (m * n) <= coverMinca
rd T F U m ^ n
-/
lemma coverMincard_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m_pos : 0 < m) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ coverMincard T F U m ^ (n / m + 1) :=
  (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv m (n / m + 1))
/-
**Dynamics.coverMincard_finite_of_isCompact_uniformContinuous** 是 Mathlib 中的一个引理
，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_finite_of_isCompact_uniformContinuous [UniformSpace X] (F_com
p : IsCompact F) (h : UniformContinuous T) (U_uni : U in 𝓤 X) (n : Nat) : coverM
incard T F U n < ⊤
参数：F_comp : IsCompact F；h : UniformContinuous T；U_uni : U in 𝓤 X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Dynamics.exists_isDynCoverOf_of_isCompact_uniformContinuous`：exists_isDy
nCoverOf_of_isCompact_uniformContinuous [UniformSpace X] (F_comp : IsCompact F) 
(h : UniformContinuous T) (U_uni : U in 𝓤 X) (n :…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
lemma coverMincard_finite_of_isCompact_uniformContinuous [UniformSpace X] (F_comp : IsCompact F)
    (h : UniformContinuous T) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)
/-
**Dynamics.coverMincard_finite_of_isCompact_invariant** 是 Mathlib 中的一个引理，位于命名空间 
`Dynamics`。
形式化陈述：coverMincard_finite_of_isCompact_invariant [UniformSpace X] (F_comp : IsCo
mpact F) (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) (n : Nat) : coverMincard T F 
U n < ⊤
参数：F_comp : IsCompact F；F_inv : MapsTo T F F；U_uni : U in 𝓤 X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Dynamics.exists_isDynCoverOf_of_isCompact_invariant`：exists_isDynCoverOf
_of_isCompact_invariant [UniformSpace X] (F_comp : IsCompact F) (F_inv : MapsTo 
T F F) (U_uni : U in 𝓤 X) (n : Nat) : exi…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
lemma coverMincard_finite_of_isCompact_invariant [UniformSpace X] (F_comp : IsCompact F)
    (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

/-- All dynamical balls of a minimal dynamical cover of `F` intersect `F`. This lemma is the key
  to relate Bowen-Dinaburg's definition of topological entropy with covers and their definition
  of topological entropy with nets. -/
/-
**Dynamics.nonempty_inter_of_coverMincard** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：nonempty_inter_of_coverMincard [U.IsSymm] {s : Finset X} (h : IsDynCoverOf
 T F U n s) (h' : #s = coverMincard T F U n) : forall x in s, (F inter ball x (d
ynEntourage T U n)).Nonempty
参数：h : IsDynCoverOf T F U n s；h' : #s = coverMincard T F U n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Finset.card_erase_lt_of_mem`：card_erase_lt_of_mem : a in s -> #(s.erase 
a) < #s

--- 原说明 ---
All dynamical balls of a minimal dynamical cover of `F` intersect `F`. This lemm
a is the key
  to relate Bowen-Dinaburg's definition of topological entropy with covers and t
heir definition
  of topological entropy with nets.
-/
lemma nonempty_inter_of_coverMincard [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s)
    (h' : #s = coverMincard T F U n) :
    ∀ x ∈ s, (F ∩ ball x (dynEntourage T U n)).Nonempty := by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (s.erase x) := by
    intro y y_F
    specialize h y_F
    simp only [s.mem_coe] at h
    simp only [s.coe_erase, mem_sdiff, s.mem_coe, mem_singleton_iff]
    obtain ⟨z, z_s, hz⟩ := h
    refine ⟨z, ⟨z_s, fun z_x ↦ notMem_empty y ?_⟩, hz⟩
    rw [← ball_empt]
    rw [z_x] at hz
    exact mem_inter y_F <| (dynEntourage T U n).symm hz
  apply smaller_cover.coverMincard_le_card.not_gt
  rw [← h']
  exact_mod_cast s.card_erase_lt_of_mem x_s

/-! ### Cover entropy of entourages -/

open ENNReal EReal ExpGrowth Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This first version uses a `limsup`, and is chosen as the default definition. -/
/-
**Dynamics.coverEntropyEntourage** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X)
参数：T : X -> X；F : Set X；U : SetRel X X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of an entourage `U`, defined as the exponential rate of growth of th
e size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of ex
tended real numbers
  `[-∞, +∞]`. This first version uses a `limsup`, and is chosen as the default d
efinition.
-/
noncomputable def coverEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthSup fun n : ℕ ↦ coverMincard T F U n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This second version uses a `liminf`, and is chosen as an alternative definition. -/
/-
**Dynamics.coverEntropyInfEntourage** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage (T : X -> X) (F : Set X) (U : SetRel X X)
参数：T : X -> X；F : Set X；U : SetRel X X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of an entourage `U`, defined as the exponential rate of growth of th
e size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of ex
tended real numbers
  `[-∞, +∞]`. This second version uses a `liminf`, and is chosen as an alternati
ve definition.
-/
noncomputable def coverEntropyInfEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthInf fun n : ℕ ↦ coverMincard T F U n
/-
**Dynamics.coverEntropyInfEntourage_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics
`。
形式化陈述：coverEntropyInfEntourage_antitone (T : X -> X) (F : Set X) : Antitone fun 
U : SetRel X X => coverEntropyInfEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_antitone`：coverMincard_antitone (T : X -> X) (F : 
Set X) (n : Nat) : Antitone fun U : SetRel X X => coverMincard T F U n
-/
lemma coverEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ coverEntropyInfEntourage T F U :=
  fun _ _ U_V ↦ expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_antitone T F n U_V)
/-
**Dynamics.coverEntropyEntourage_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_antitone (T : X -> X) (F : Set X) : Antitone fun U :
 SetRel X X => coverEntropyEntourage T F U
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_antitone`：coverMincard_antitone (T : X -> X) (F : 
Set X) (n : Nat) : Antitone fun U : SetRel X X => coverMincard T F U n
-/
lemma coverEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ coverEntropyEntourage T F U :=
  fun _ _ U_V ↦ expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_antitone T F n U_V)
/-
**Dynamics.coverEntropyInfEntourage_le_coverEntropyEntourage** 是 Mathlib 中的一个引理，
位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X)
 (U : SetRel X X) : coverEntropyInfEntourage T F U <= coverEntropyEntourage T F 
U
参数：T : X -> X；F : Set X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_le_expGrowthSup`：expGrowthInf_le_expGrowthSup : e
xpGrowthInf u <= expGrowthSup u
-/
lemma coverEntropyInfEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :
    coverEntropyInfEntourage T F U ≤ coverEntropyEntourage T F U :=
  expGrowthInf_le_expGrowthSup

@[simp]
/-
**Dynamics.coverEntropyEntourage_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_empty : coverEntropyEntourage T ∅ U = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.coverMincard_empty`：coverMincard_empty : coverMincard T ∅ U n =
 0
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
-/
lemma coverEntropyEntourage_empty : coverEntropyEntourage T ∅ U = ⊥ := by
  simp only [coverEntropyEntourage, coverMincard_empty]
  rw [ENat.toENNReal_zero, ← Pi.zero_def, expGrowthSup_zero]

@[simp]
/-
**Dynamics.coverEntropyInfEntourage_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_empty : coverEntropyInfEntourage T ∅ U = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_coverEntropyEntourage`：coverEntropy
InfEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) 
: coverEntropyInfEntourage T F U <= coverEntropy…
· 使用引理 `Dynamics.coverEntropyEntourage_empty`：coverEntropyEntourage_empty : cove
rEntropyEntourage T ∅ U = ⊥
-/
lemma coverEntropyInfEntourage_empty : coverEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty
/-
**Dynamics.coverEntropyInfEntourage_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel 
X X) : 0 <= coverEntropyInfEntourage T F U
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.expGrowthInf_nonneg`：∀ {u : ℕ → ENNReal}, Monotone u → u ≠ 0 → 
0 ≤ ExpGrowth.expGrowthInf u
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_monotone_time`：coverMincard_monotone_time (T : X -
> X) (F : Set X) (U : SetRel X X) : Monotone fun n : Nat => coverMincard T F U n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Dynamics.coverMincard_zero`：coverMincard_zero (T : X -> X) (h : F.Nonemp
ty) (U : SetRel X X) : coverMincard T F U 0 = 1
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
lemma coverEntropyInfEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ coverEntropyInfEntourage T F U := by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [coverMincard_zero T h U, Pi.zero_apply, ENat.toENNReal_one]
    exact one_ne_zero
/-
**Dynamics.coverEntropyEntourage_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_nonneg (T : X -> X) (h : F.Nonempty) (U : SetRel X X
) : 0 <= coverEntropyEntourage T F U
参数：T : X -> X；h : F.Nonempty；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInfEntourage_nonneg`：coverEntropyInfEntourage_nonne
g (T : X -> X) (h : F.Nonempty) (U : SetRel X X) : 0 <= coverEntropyInfEntourage
 T F U
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_coverEntropyEntourage`：coverEntropy
InfEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) 
: coverEntropyInfEntourage T F U <= coverEntropy…
-/
lemma coverEntropyEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ coverEntropyEntourage T F U :=
  (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)
/-
**Dynamics.coverEntropyEntourage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_univ (T : X -> X) (h : F.Nonempty) : coverEntropyEnt
ourage T F univ = 0
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
· 使用定理 `Dynamics.coverEntropyEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F : S
et X) (U : SetRel X X),   Dynamics.coverEntropyEntourage T F U = ExpGrowth.expGr
owthSup fun n => ↑(Dynami…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.coverMincard_univ`：coverMincard_univ (T : X -> X) (h : F.Nonemp
ty) (n : Nat) : coverMincard T F univ n = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coverEntropyEntourage_univ (T : X → X) (h : F.Nonempty) :
    coverEntropyEntourage T F univ = 0 := by
  rw [← expGrowthSup_const one_ne_zero one_ne_top, coverEntropyEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]
/-
**Dynamics.coverEntropyInfEntourage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_univ (T : X -> X) (h : F.Nonempty) : coverEntropy
InfEntourage T F univ = 0
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
· 使用定理 `Dynamics.coverEntropyInfEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F 
: Set X) (U : SetRel X X),   Dynamics.coverEntropyInfEntourage T F U = ExpGrowth
.expGrowthInf fun n => ↑(Dyn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dynamics.coverMincard_univ`：coverMincard_univ (T : X -> X) (h : F.Nonemp
ty) (n : Nat) : coverMincard T F univ n = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coverEntropyInfEntourage_univ (T : X → X) (h : F.Nonempty) :
    coverEntropyInfEntourage T F univ = 0 := by
  rw [← expGrowthInf_const one_ne_zero one_ne_top, coverEntropyInfEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]
/-
**Dynamics.coverEntropyEntourage_le_log_coverMincard_div** 是 Mathlib 中的一个引理，位于命名
空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.Is
Symm] (n_pos : n != 0) : coverEntropyEntourage T F (U ○ U) <= log (coverMincard 
T F U n) / n
参数：F_inv : MapsTo T F F；n_pos : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_monotone_time`：coverMincard_monotone_time (T : X -
> X) (F : Set X) (U : SetRel X X) : Monotone fun n : Nat => coverMincard T F U n
· 使用定理 `Monotone.expGrowthSup_comp_mul`：∀ {u : ℕ → ENNReal} {m : ℕ},   Monotone 
u → m ≠ 0 → (ExpGrowth.expGrowthSup fun n => u (m * n)) = ↑m * ExpGrowth.expGrow
thSup u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dynamics.coverEntropyEntourage.eq_1`：∀ {X : Type u_1} (T : X → X) (F : S
et X) (U : SetRel X X),   Dynamics.coverEntropyEntourage T F U = ExpGrowth.expGr
owthSup fun n => ↑(Dynami…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.div_eq_iff`：div_eq_iff (hbot : b != ⊥) (htop : b != ⊤) (hzero : b 
!= 0) : c / b = a ↔ c = a * b
· 使用定理 `EReal.natCast_ne_bot`：natCast_ne_bot (n : Nat) : (n : EReal) != ⊥
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用引理 `ExpGrowth.expGrowthSup_pow`：expGrowthSup_pow : expGrowthSup (fun n => b 
^ n) = log b
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_pow`：toENNReal_pow (x : Nat∞) (n : Nat) : (x ^ n : Nat∞) 
= (x : Real>=0∞) ^ n
· 使用引理 `Dynamics.coverMincard_mul_le_pow`：coverMincard_mul_le_pow (F_inv : MapsT
o T F F) [U.IsSymm] (m n : Nat) : coverMincard T F (U ○ U) (m * n) <= coverMinca
rd T F U m ^ n
-/
lemma coverEntropyEntourage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n ≠ 0) :
    coverEntropyEntourage T F (U ○ U) ≤ log (coverMincard T F U n) / n := by
  have cv_mono : Monotone fun m ↦ (coverMincard T F (U ○ U) m).toENNReal :=
    fun _ _ k_m ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F (U ○ U) k_m)
  have h := cv_mono.expGrowthSup_comp_mul n_pos
  rw [mul_comm, ← div_eq_iff (natCast_ne_bot n) (natCast_ne_top n) (Nat.cast_ne_zero.2 n_pos)] at h
  rw [coverEntropyEntourage, ← h]
  apply monotone_div_right_of_nonneg n.cast_nonneg'
  rw [← expGrowthSup_pow]
  refine expGrowthSup_monotone fun m ↦ ?_
  rw [← ENat.toENNReal_pow]
  exact ENat.toENNReal_mono (coverMincard_mul_le_pow F_inv n m)
/-
**Dynamics.IsDynCoverOf.coverEntropyEntourage_le_log_card_div** 是 Mathlib 中的一个定理
，位于命名空间 `Dynamics.IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {U : SetRel X X} {F : Set X} {n : ℕ},   Set.M
apsTo T F F →     ∀ [U.IsSymm],       n ≠ 0 →         ∀ {s : Finset X},         
  Dynamics.IsDynCoverOf T F U n ↑s → Dynamics.coverEntropyEntourage T F (U.comp 
U) ≤ (↑s.card).log / ↑n
参数：U.comp U；↑s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_le_log_coverMincard_div`：coverEntropyEnto
urage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.IsSymm] (n_pos : n != 0)
 : coverEntropyEntourage T F (U ○ U) <= log …
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
-/
lemma IsDynCoverOf.coverEntropyEntourage_le_log_card_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n ≠ 0) {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) ≤ log s.card / n := by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv n_pos).trans
  apply monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact_mod_cast coverMincard_le_card h
/-
**Dynamics.coverEntropyEntourage_le_coverEntropyInfEntourage** 是 Mathlib 中的一个引理，
位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_le_coverEntropyInfEntourage (F_inv : MapsTo T F F) [
U.IsSymm] : coverEntropyEntourage T F (U ○ U) <= coverEntropyInfEntourage T F U
参数：F_inv : MapsTo T F F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Dynamics.coverEntropyEntourage_le_log_coverMincard_div`：coverEntropyEnto
urage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.IsSymm] (n_pos : n != 0)
 : coverEntropyEntourage T F (U ○ U) <= log …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma coverEntropyEntourage_le_coverEntropyInfEntourage (F_inv : MapsTo T F F) [U.IsSymm] :
    coverEntropyEntourage T F (U ○ U) ≤ coverEntropyInfEntourage T F U := by
  refine (le_liminf_of_le) (eventually_atTop.2 ⟨1, fun m m_pos ↦ ?_⟩)
  exact coverEntropyEntourage_le_log_coverMincard_div F_inv (Nat.one_le_iff_ne_zero.1 m_pos)
/-
**Dynamics.coverEntropyEntourage_finite_of_isCompact_invariant** 是 Mathlib 中的一个引
理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_finite_of_isCompact_invariant [UniformSpace X] (F_co
mp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U in 𝓤 X) : coverEntropyEntour
age T F U < ⊤
参数：F_comp : IsCompact F；F_inv : MapsTo T F F；U_uni : U in 𝓤 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用引理 `Dynamics.exists_isDynCoverOf_of_isCompact_invariant`：exists_isDynCoverOf
_of_isCompact_invariant [UniformSpace X] (F_comp : IsCompact F) (F_inv : MapsTo 
T F F) (U_uni : U in 𝓤 X) (n : Nat) : exi…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Dynamics.coverEntropyEntourage_antitone`：coverEntropyEntourage_antitone 
(T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyEntourage 
T F U
· 使用定理 `Dynamics.IsDynCoverOf.coverEntropyEntourage_le_log_card_div`：∀ {X : Type
 u_1} {T : X → X} {U : SetRel X X} {F : Set X} {n : ℕ},   Set.MapsTo T F F →    
 ∀ [U.IsSymm],       n ≠ 0 →         ∀ {s : Finse…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `ENNReal.log_lt_top_iff`：∀ {x : ENNReal}, x.log < ⊤ ↔ x < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.toENNReal_top`：toENNReal_top : ((⊤ : Nat∞) : Real>=0∞) = ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
lemma coverEntropyEntourage_finite_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U < ⊤ := by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv one_ne_zero).trans_lt
  rw [Nat.cast_one, div_one, log_lt_top_iff, ← ENat.toENNReal_top]
  exact_mod_cast (ENat.natCast_ne_top (Finset.card s)).lt_top

/-! ### Cover entropy -/

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyEntourage` over entourages. Note that this supremum is approached by taking small
  entourages. This first version uses a `limsup`, and is chosen as the default definition
  for topological entropy. -/
/-
**Dynamics.coverEntropy** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy [UniformSpace X] (T : X -> X) (F : Set X)
参数：T : X -> X；F : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyEntourage` over entourages. Note that this supremum is approac
hed by taking small
  entourages. This first version uses a `limsup`, and is chosen as the default d
efinition
  for topological entropy.
-/
noncomputable def coverEntropy [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, coverEntropyEntourage T F U

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyInfEntourage` over entourages. Note that this supremum is approached by taking
  small entourages. This second version uses a `liminf`, and is chosen as an alternative
  definition for topological entropy. -/
/-
**Dynamics.coverEntropyInf** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf [UniformSpace X] (T : X -> X) (F : Set X)
参数：T : X -> X；F : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyInfEntourage` over entourages. Note that this supremum is appr
oached by taking
  small entourages. This second version uses a `liminf`, and is chosen as an alt
ernative
  definition for topological entropy.
-/
noncomputable def coverEntropyInf [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, coverEntropyInfEntourage T F U
/-
**Dynamics.coverEntropyInf_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_antitone (T : X -> X) (F : Set X) : Antitone fun (u : Unif
ormSpace X) => @coverEntropyInf X u T F
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma coverEntropyInf_antitone (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @coverEntropyInf X u T F :=
  fun _ _ h ↦ iSup₂_mono' fun U U_uni ↦ ⟨U, (le_def.1 h) U U_uni, le_refl _⟩
/-
**Dynamics.coverEntropy_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_antitone (T : X -> X) (F : Set X) : Antitone fun (u : Uniform
Space X) => @coverEntropy X u T F
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma coverEntropy_antitone (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @coverEntropy X u T F :=
  fun _ _ h ↦ iSup₂_mono' fun U U_uni ↦ ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

variable [UniformSpace X]
/-
**Dynamics.coverEntropyEntourage_le_coverEntropy** 是 Mathlib 中的一个引理，位于命名空间 `Dyna
mics`。
形式化陈述：coverEntropyEntourage_le_coverEntropy (T : X -> X) (F : Set X) (h : U in 𝓤
 X) : coverEntropyEntourage T F U <= coverEntropy T F
参数：T : X -> X；F : Set X；h : U in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma coverEntropyEntourage_le_coverEntropy (T : X → X) (F : Set X)
    (h : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U ≤ coverEntropy T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ coverEntropyEntourage T F U) U h
/-
**Dynamics.coverEntropyInfEntourage_le_coverEntropyInf** 是 Mathlib 中的一个引理，位于命名空间
 `Dynamics`。
形式化陈述：coverEntropyInfEntourage_le_coverEntropyInf (T : X -> X) (F : Set X) (h : 
U in 𝓤 X) : coverEntropyInfEntourage T F U <= coverEntropyInf T F
参数：T : X -> X；F : Set X；h : U in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma coverEntropyInfEntourage_le_coverEntropyInf (T : X → X) (F : Set X)
    (h : U ∈ 𝓤 X) :
    coverEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ coverEntropyInfEntourage T F U) U h
/-
**Dynamics.coverEntropy_eq_iSup_basis** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_eq_iSup_basis {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel X 
X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) : coverEntropy T F = ⨆ (i :
 ι) (_ : p i), coverEntropyEntourage T F (s i)
参数：h : (𝓤 X).HasBasis p s；T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_antitone`：coverEntropyEntourage_antitone 
(T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyEntourage 
T F U
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma coverEntropy_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), coverEntropyEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyEntourage T F (s i)) i h_i)
/-
**Dynamics.coverEntropyInf_eq_iSup_basis** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_eq_iSup_basis {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel
 X X} (h : (𝓤 X).HasBasis p s) (T : X -> X) (F : Set X) : coverEntropyInf T F = 
⨆ (i : ι) (_ : p i), coverEntropyInfEntourage T F (s i)
参数：h : (𝓤 X).HasBasis p s；T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInfEntourage_antitone`：coverEntropyInfEntourage_ant
itone (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyInfE
ntourage T F U
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_mono'`：iSup₂_mono' {f : forall i, κ i -> α} {g : forall i', κ' i' 
-> α} (h : forall i j, exists i' j', f i j <= g i' j') : ⨆ (i) (j), f i j <= ⨆ (
i…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma coverEntropyInf_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), coverEntropyInfEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyInfEntourage T F (s i)) i h_i)
/-
**Dynamics.coverEntropyInf_le_coverEntropy** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_le_coverEntropy (T : X -> X) (F : Set X) : coverEntropyInf
 T F <= coverEntropy T F
参数：T : X -> X；F : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_coverEntropyEntourage`：coverEntropy
InfEntourage_le_coverEntropyEntourage (T : X -> X) (F : Set X) (U : SetRel X X) 
: coverEntropyInfEntourage T F U <= coverEntropy…
-/
lemma coverEntropyInf_le_coverEntropy (T : X → X) (F : Set X) :
    coverEntropyInf T F ≤ coverEntropy T F :=
  iSup₂_mono fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]
/-
**Dynamics.coverEntropy_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_empty : coverEntropy T ∅ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Dynamics.coverEntropyEntourage_empty`：coverEntropyEntourage_empty : cove
rEntropyEntourage T ∅ U = ⊥
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coverEntropy_empty : coverEntropy T ∅ = ⊥ := by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]
/-
**Dynamics.coverEntropyInf_empty** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_empty : coverEntropyInf T ∅ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Dynamics.coverEntropyInfEntourage_empty`：coverEntropyInfEntourage_empty 
: coverEntropyInfEntourage T ∅ U = ⊥
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coverEntropyInf_empty : coverEntropyInf T ∅ = ⊥ := by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]
/-
**Dynamics.coverEntropyInf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_nonneg (T : X -> X) (h : F.Nonempty) : 0 <= coverEntropyIn
f T F
参数：T : X -> X；h : F.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用引理 `Dynamics.coverEntropyInfEntourage_le_coverEntropyInf`：coverEntropyInfEnt
ourage_le_coverEntropyInf (T : X -> X) (F : Set X) (h : U in 𝓤 X) : coverEntropy
InfEntourage T F U <= coverEntropyInf T F
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用引理 `Dynamics.coverEntropyInfEntourage_univ`：coverEntropyInfEntourage_univ (T
 : X -> X) (h : F.Nonempty) : coverEntropyInfEntourage T F univ = 0
-/
lemma coverEntropyInf_nonneg (T : X → X) (h : F.Nonempty) : 0 ≤ coverEntropyInf T F :=
  (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h)
/-
**Dynamics.coverEntropy_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_nonneg (T : X -> X) (h : F.Nonempty) : 0 <= coverEntropy T F
参数：T : X -> X；h : F.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInf_nonneg`：coverEntropyInf_nonneg (T : X -> X) (h 
: F.Nonempty) : 0 <= coverEntropyInf T F
· 使用引理 `Dynamics.coverEntropyInf_le_coverEntropy`：coverEntropyInf_le_coverEntrop
y (T : X -> X) (F : Set X) : coverEntropyInf T F <= coverEntropy T F
-/
lemma coverEntropy_nonneg (T : X → X) (h : F.Nonempty) : 0 ≤ coverEntropy T F :=
  (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)
/-
**Dynamics.coverEntropyInf_eq_coverEntropy** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_eq_coverEntropy (T : X -> X) (h : MapsTo T F F) : coverEnt
ropyInf T F = coverEntropy T F
参数：T : X -> X；h : MapsTo T F F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Dynamics.coverEntropyInf_le_coverEntropy`：coverEntropyInf_le_coverEntrop
y (T : X -> X) (F : Set X) : coverEntropyInf T F <= coverEntropy T F
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
· 使用引理 `Dynamics.coverEntropyEntourage_le_coverEntropyInfEntourage`：coverEntropy
Entourage_le_coverEntropyInfEntourage (F_inv : MapsTo T F F) [U.IsSymm] : coverE
ntropyEntourage T F (U ○ U) <= coverEntropyInfEn…
-/
lemma coverEntropyInf_eq_coverEntropy (T : X → X) (h : MapsTo T F F) :
    coverEntropyInf T F = coverEntropy T F := by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni ↦ ?_)
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  exact (coverEntropyEntourage_antitone T F V_U).trans <| le_iSup₂_of_le V V_uni <|
     coverEntropyEntourage_le_coverEntropyInfEntourage h

end Dynamics

