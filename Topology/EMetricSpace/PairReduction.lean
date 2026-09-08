/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, David Ledvinka
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Order.CompletePartialOrder

/-!
# Pair Reduction

The goal of this file is to prove the theorem `pair_reduction`. This is essentially Lemma 6.1 in
[kratschmer_urusov2023] which is an extension of Lemma B.2.7. in [talagrand2014].
Given pseudometric spaces `T` and `E`, `c ≥ 0`, and a finite subset `J` of `T` such that
`|J| ≤ aⁿ` for some `a ≥ 0` and `n : ℕ`, `pair_reduction` states that there exists a set `K ⊆ J²`
such that for any function `f : T → E`:

1. `|K| ≤ a|J|`
2. `∀ (s, t) ∈ K, d(s, t) ≤ cn`
3. `sup_{s, t ∈ J : d(s, t) ≤ c} d(f(s), f(t)) ≤ 2 sup_{(s, t) ∈ K} d(f(s), f(t))`

When applying the chaining technique for bounding the supremum of the increments of stochastic
processes, `pair_reduction` is used to reduce the order of the dependence of the bound on the
covering numbers of the pseudometric space. As a simple example of how it could be used, suppose
`T` has an `ε`-covering number `N` and suppose `J` is an `ε`-covering of `T` with `|J| = N`.
Let `f : Ω → T → E` be any stochastic process such that `𝔼 d(f(s), f(t)) ≤ d (s, t)` for all
`s, t ∈ T`. Then naively
```
  𝔼[sup_{(s, t) ∈ J} : d(s, t) ≤ c} d(f(s), f(t))]
    ≤ ∑_{(s, t) ∈ J² : d(s, t) ≤ c} 𝔼[d(f(s), f(t))]
    ≤ |J|² c
    = c N²
```
but applying `pair_reduction` with `n = log |J|` we get
```
  𝔼[sup_{(s, t) ∈ J : d(s, t) ≤ c} d(f(s), f(t))]
    ≤ 2 𝔼[sup_{(s, t) ∈ K} d(f(s), f(t))]
    ≤ 2 ∑_{(s, t) ∈ K} 𝔼[d(f(s), f(t))]
    ≤ 2 a |J| c log |J|
    ≤ 2 a c N log N
```
`pair_reduction` is used in [kratschmer_urusov2023] to prove a form of the Kolmogorov-Chentsov
theorem that applies to stochastic processes which satisfy the Kolmogorov condition but works
on very general metric spaces.

## Implementation

In this section we sketch a proof of `pair_reduction` with references to the corresponding steps
in the lean code.

For any `V : Finset T` and `t : T` we define the log-size radius of `t` in `V` to be the smallest
natural number `k` greater than zero such that `|{x ∈ V | d(t, x) ≤ kc}| ≤ aᵏ`.
(see `logSizeRadius`)

We construct a sequence `Vᵢ` of subsets of `J`, a sequence `tᵢ ∈ Vᵢ` and a sequence of `rᵢ : ℕ`
inductively as follows (see `logSizeBallSeq`):

* `V₀ = J`, `t₀` is chosen arbitrarily in `J`, `r₀` is the log-size radius of `t₀` in `V₀`
* `Vᵢ₊₁ = Vᵢ \ Bᵢ` where `Bᵢ := {x ∈ V | d(t, x) ≤ (rᵢ - 1) c}`, `tᵢ₊₁` is chosen arbitrarily in
  `Vᵢ₊₁` (if it is nonempty), `rᵢ₊₁` is the log-size radius of `tᵢ₊₁` in `Vᵢ₊₁`.

Then `Vᵢ` is a strictly decreasing sequence (see `card_finset_logSizeBallSeq_add_one_lt`) until
`Vᵢ` is empty. In particular `Vᵢ = ∅` for `i ≥ |J|`
(see `card_finset_logSizeBallSeq_card_eq_zero`).

We will show that `K = ⋃_{i=1}^|J| {tᵢ} × {x ∈ Vᵢ | d(tᵢ, x) ≤ crᵢ}` suffices
(see `pairSet` and `pairSetSeq`).

To prove (1) we have that
```
  |K| ≤ ∑_{i=0}^|J| |{x ∈ Vᵢ : d(t, x) ≤ crᵢ}|
      ≤ ∑_{i=0}^|J| a ^ rᵢ  (by definition of `rᵢ`)
      = a ∑_{i=0}^|J| a ^ (rᵢ - 1)
      ≤ a ∑_{i=0}^|J| |Bᵢ| (by definition of `rᵢ`)
      ≤ a |J| (since the `Bᵢ` are disjoint (see `disjoint_smallBall_logSizeBallSeq`))
```
(see `card_pairSet_le`).

(2) follows easily from the definition of K and the fact that `rᵢ ≤ n` for each `i`
(see `edist_le_of_mem_pairSet` and `radius_logSizeBallSeq_le`)

Finally we prove (3). Let `s, t ∈ J` such that `d(s, t) ≤ c`. Let `i` be the largest integer
such that both `s, t ∈ Vᵢ`. WLOG suppose `s ∉ Vᵢ₊₁` so that in particular `s ∈ Bᵢ` which means
by definition that `d(tᵢ, s) ≤ (rᵢ - 1)c`. Then we also have
```
d(tᵢ, t) ≤ d(tᵢ, s) + d(s, t) ≤ (rᵢ - 1)c + c = rᵢc
```
hence `(tᵢ, s), (tᵢ, t) ∈ K`. Furthermore
```
d(f(s), f(t)) ≤ d(f(tᵢ), f(s)) + d(f(tᵢ), f(t))
```
taking supremums completes the proof (see `iSup_edist_pairSet`).

## References

* [V. Krätschmer, M. Urusov, *A Kolmogorov–Chentsov Type Theorem on General Metric Spaces with
  Applications to Limit Theorems for Banach-Valued Processes*][kratschmer_urusov2023]
* [M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*][talagrand2014]

-/

@[expose] public section

open scoped ENNReal NNReal Finset

variable {T : Type*} [PseudoEMetricSpace T] {a c : ℝ≥0∞} {n : ℕ} {V J : Finset T} {t : T}

namespace PairReduction

/-
**PairReduction.exists_radius_le** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`。
形式化陈述：exists_radius_le (t : T) (V : Finset T) (ha : 1 < a) (c : Real>=0∞) : exis
ts r : Nat, 1 <= r ∧ #(V.filter fun x => edist t x <= r * c) <= a ^ r
参数：t : T；V : Finset T；ha : 1 < a；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nat`：tendsto_nhds_top_iff_nat {m : α -> Rea
l>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall n : Nat, forallᶠ a in f, ↑n <
 m a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `ENNReal.tendsto_rpow_atTop_of_one_lt_base`：tendsto_rpow_atTop_of_one_lt_
base {b : Real>=0∞} (hb : 1 < b) : Filter.Tendsto (b ^ · : Real -> Real>=0∞) Fil
ter.atTop (𝓝 ⊤)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
lemma exists_radius_le (t : T) (V : Finset T) (ha : 1 < a) (c : ℝ≥0∞) :
    ∃ r : ℕ, 1 ≤ r ∧ #(V.filter fun x ↦ edist t x ≤ r * c) ≤ a ^ r := by
  have := ENNReal.tendsto_nhds_top_iff_nat.1
    ((ENNReal.tendsto_rpow_atTop_of_one_lt_base ha).comp tendsto_natCast_atTop_atTop) #V
  simp only [Function.comp_apply, ENNReal.rpow_natCast, Filter.eventually_atTop] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨max r 1, le_max_right r 1,
    le_trans (mod_cast Finset.card_filter_le V _) (hr (max r 1) (le_max_left r 1)).le⟩

/-- The log-size radius of `t` in `V` is the smallest natural number n greater than zero such that
`|{x ∈ V | d(t, x) ≤ nc}| ≤ aⁿ`. -/
noncomputable
/-
**PairReduction.logSizeRadius** 是 Mathlib 中的一个定义，位于命名空间 `PairReduction`。
形式化陈述：logSizeRadius (t : T) (V : Finset T) (a c : Real>=0∞) : Nat
参数：t : T；V : Finset T；a c : Real>=0∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.exists_radius_le`：exists_radius_le (t : T) (V : Finset T) 
(ha : 1 < a) (c : Real>=0∞) : exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist
 t x <= r * c) <= a …
-/
def logSizeRadius (t : T) (V : Finset T) (a c : ℝ≥0∞) : ℕ :=
  if h : 1 < a then Nat.find (exists_radius_le t V h c) else 0
/-
**PairReduction.one_le_logSizeRadius** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`。
形式化陈述：one_le_logSizeRadius (ha : 1 < a) : 1 <= logSizeRadius t V a c
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.exists_radius_le`：exists_radius_le (t : T) (V : Finset T) 
(ha : 1 < a) (c : Real>=0∞) : exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist
 t x <= r * c) <= a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PairReduction.logSizeRadius.eq_1`：∀ {T : Type u_1} [inst : PseudoEMetric
Space T] (t : T) (V : Finset T) (a c : ENNReal),   PairReduction.logSizeRadius t
 V a c = if h : 1 < a …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
lemma one_le_logSizeRadius (ha : 1 < a) :
    1 ≤ logSizeRadius t V a c := by
  rw [logSizeRadius, dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).1
/-
**PairReduction.card_le_logSizeRadius_le_pow_logSizeRadius** 是 Mathlib 中的一个引理，位于
命名空间 `PairReduction`。
形式化陈述：card_le_logSizeRadius_le_pow_logSizeRadius (ha : 1 < a) : #(V.filter fun x
 => edist t x <= logSizeRadius t V a c * c) <= a ^ (logSizeRadius t V a c)
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.exists_radius_le`：exists_radius_le (t : T) (V : Finset T) 
(ha : 1 < a) (c : Real>=0∞) : exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist
 t x <= r * c) <= a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PairReduction.logSizeRadius.eq_1`：∀ {T : Type u_1} [inst : PseudoEMetric
Space T] (t : T) (V : Finset T) (a c : ENNReal),   PairReduction.logSizeRadius t
 V a c = if h : 1 < a …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
lemma card_le_logSizeRadius_le_pow_logSizeRadius (ha : 1 < a) :
    #(V.filter fun x ↦ edist t x ≤ logSizeRadius t V a c * c) ≤ a ^ (logSizeRadius t V a c) := by
  rw [logSizeRadius, dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).2
/-
**PairReduction.pow_logSizeRadius_le_card_le_logSizeRadius** 是 Mathlib 中的一个引理，位于
命名空间 `PairReduction`。
形式化陈述：pow_logSizeRadius_le_card_le_logSizeRadius (ha : 1 < a) (ht : t in V) : a 
^ (logSizeRadius t V a c - 1) <= #(V.filter fun x => edist t x <= (logSizeRadius
 t V a c - 1) * c)
参数：ha : 1 < a；ht : t in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `PairReduction.exists_radius_le`：exists_radius_le (t : T) (V : Finset T) 
(ha : 1 < a) (c : Real>=0∞) : exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist
 t x <= r * c) <= a …
· 使用定理 `PairReduction.logSizeRadius.eq_1`：∀ {T : Type u_1} [inst : PseudoEMetric
Space T] (t : T) (V : Finset T) (a c : ENNReal),   PairReduction.logSizeRadius t
 V a c = if h : 1 < a …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 38 条，此处仅展示前 30 条）
-/
lemma pow_logSizeRadius_le_card_le_logSizeRadius (ha : 1 < a) (ht : t ∈ V) :
    a ^ (logSizeRadius t V a c - 1)
      ≤ #(V.filter fun x ↦ edist t x ≤ (logSizeRadius t V a c - 1) * c) := by
  by_cases h_one : logSizeRadius t V a c = 1
  · simp only [h_one, tsub_self, pow_zero, Nat.cast_one, zero_mul, nonpos_iff_eq_zero,
      Nat.one_le_cast, Finset.one_le_card]
    exact ⟨t, by simpa⟩
  rw [logSizeRadius, dif_pos ha] at h_one ⊢
  have : Nat.find (exists_radius_le t V ha c) - 1 < Nat.find (exists_radius_le t V ha c) := by
    simp
  have h := Nat.find_min (exists_radius_le t V ha c) this
  simp only [ENNReal.natCast_sub, Nat.cast_one, not_and, not_le] at h
  exact (h (by lia)).le

/-- A structure for carrying the data of `logSizeBallSeq` -/
/-
**PairReduction.logSizeBallStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `PairReduction`。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure for carrying the data of `logSizeBallSeq`
-/
structure logSizeBallStruct (T : Type*) where
  /-- The underlying finite set of a `logSizeBallStruct` -/
  finset : Finset T
  /-- The underlying point of a `logSizeBallStruct` (typically a point in the underlying finite
  set) -/
  point : T
  /-- The underlying radius of a `logSizeBallStruct` (typically the log-size radius of the
  underlying point in the underlying finite set) -/
  radius : ℕ

/-- If `(V, t, r)` is a `logSizeBallStruct` then `logSizeBallStruct.smallBall`
  is `{x ∈ V | d(t, x) ≤ (r - 1)c}`. -/
noncomputable
/-
**PairReduction.logSizeBallStruct.smallBall** 是 Mathlib 中的一个定义，位于命名空间 `PairReduc
tion.logSizeBallStruct`。
形式化陈述：{T : Type u_1} → [PseudoEMetricSpace T] → PairReduction.logSizeBallStruct 
T → ENNReal → Finset T
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def logSizeBallStruct.smallBall (struct : logSizeBallStruct T) (c : ℝ≥0∞) :
    Finset T :=
  struct.finset.filter fun x ↦ edist struct.point x ≤ (struct.radius - 1) * c

/-- If `(V, t, r)` is a `logSizeBallStruct` then `logSizeBallStruct.ball`
  is `{x ∈ V | d(t, x) ≤ rc}`. -/
noncomputable
/-
**PairReduction.logSizeBallStruct.ball** 是 Mathlib 中的一个定义，位于命名空间 `PairReduction.
logSizeBallStruct`。
形式化陈述：{T : Type u_1} → [PseudoEMetricSpace T] → PairReduction.logSizeBallStruct 
T → ENNReal → Finset T
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def logSizeBallStruct.ball (struct : logSizeBallStruct T) (c : ℝ≥0∞) :
    Finset T :=
  struct.finset.filter fun x ↦ edist struct.point x ≤ struct.radius * c

variable [DecidableEq T]

/-- We recursively define a log-size ball sequence `(Vᵢ, tᵢ, rᵢ)` by
  * `V₀ = J`, `t₀` is chosen arbitrarily in `J`, `r₀` is the log-size radius of `t₀` in `V₀`
  * `Vᵢ₊₁ = Vᵢ \ {x ∈ V | d(t, x) ≤ (rᵢ - 1)c}`, `tᵢ₊₁` is chosen arbitrarily in `Vᵢ₊₁`, `rᵢ₊₁` is
    the log-size radius of `tᵢ₊₁` in `Vᵢ₊₁`. -/
noncomputable
/-
**PairReduction.logSizeBallSeq** 是 Mathlib 中的一个定义，位于命名空间 `PairReduction`。
形式化陈述：logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a c : Real>=0∞) : Nat -> 
logSizeBallStruct T | 0 => { finset
参数：J : Finset T；hJ : J.Nonempty；a c : Real>=0∞。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a c : ℝ≥0∞) : ℕ → logSizeBallStruct T
  | 0 => { finset := J, point := hJ.choose, radius := logSizeRadius hJ.choose J a c }
  | n + 1 =>
    let V' := (logSizeBallSeq J hJ a c n).finset \ ((logSizeBallSeq J hJ a c n).smallBall c)
    let t' := if hV' : V'.Nonempty then hV'.choose else (logSizeBallSeq J hJ a c n).point
    { finset := V',
      point := t',
      radius := logSizeRadius t' V' a c }
/-
**PairReduction.finset_logSizeBallSeq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PairReduct
ion`。
形式化陈述：finset_logSizeBallSeq_zero (hJ : J.Nonempty) : (logSizeBallSeq J hJ a c 0)
.finset = J
参数：hJ : J.Nonempty。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finset_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).finset = J := rfl
/-
**PairReduction.point_logSizeBallSeq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PairReducti
on`。
形式化陈述：point_logSizeBallSeq_zero (hJ : J.Nonempty) : (logSizeBallSeq J hJ a c 0).
point = hJ.choose
参数：hJ : J.Nonempty。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma point_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).point = hJ.choose := rfl
/-
**PairReduction.radius_logSizeBallSeq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PairReduct
ion`。
形式化陈述：radius_logSizeBallSeq_zero (hJ : J.Nonempty) : (logSizeBallSeq J hJ a c 0)
.radius = logSizeRadius hJ.choose J a c
参数：hJ : J.Nonempty。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma radius_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).radius = logSizeRadius hJ.choose J a c := rfl
/-
**PairReduction.finset_logSizeBallSeq_add_one** 是 Mathlib 中的一个引理，位于命名空间 `PairRed
uction`。
形式化陈述：finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) : (logSizeBallSe
q J hJ a c (i + 1)).finset = (logSizeBallSeq J hJ a c i).finset \ (logSizeBallSe
q J hJ a c i).smallBall c
参数：hJ : J.Nonempty；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).finset =
      (logSizeBallSeq J hJ a c i).finset \ (logSizeBallSeq J hJ a c i).smallBall c := rfl
/-
**PairReduction.point_logSizeBallSeq_add_one** 是 Mathlib 中的一个引理，位于命名空间 `PairRedu
ction`。
形式化陈述：point_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) : (logSizeBallSeq
 J hJ a c (i + 1)).point = if hV' : (logSizeBallSeq J hJ a c (i + 1)).finset.Non
empty then hV'.choose else (logSizeBallSeq J hJ a c i).point
参数：hJ : J.Nonempty；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma point_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).point
      = if hV' : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty then hV'.choose
        else (logSizeBallSeq J hJ a c i).point := rfl
/-
**PairReduction.radius_logSizeBallSeq_add_one** 是 Mathlib 中的一个引理，位于命名空间 `PairRed
uction`。
形式化陈述：radius_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) : (logSizeBallSe
q J hJ a c (i + 1)).radius = logSizeRadius (logSizeBallSeq J hJ a c (i + 1)).poi
nt (logSizeBallSeq J hJ a c (i + 1)).finset a c
参数：hJ : J.Nonempty；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma radius_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).radius
      = logSizeRadius (logSizeBallSeq J hJ a c (i + 1)).point
          (logSizeBallSeq J hJ a c (i + 1)).finset a c := rfl
/-
**PairReduction.finset_logSizeBallSeq_add_one_subset** 是 Mathlib 中的一个引理，位于命名空间 `
PairReduction`。
形式化陈述：finset_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) (i : Nat) : (logSiz
eBallSeq J hJ a c (i + 1)).finset subseteq (logSizeBallSeq J hJ a c i).finset
参数：hJ : J.Nonempty；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma finset_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c (i + 1)).finset ⊆ (logSizeBallSeq J hJ a c i).finset := by
  simp [finset_logSizeBallSeq_add_one]
/-
**PairReduction.antitone_logSizeBallSeq_add_one_subset** 是 Mathlib 中的一个引理，位于命名空间
 `PairReduction`。
形式化陈述：antitone_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) : Antitone (fun i
 => (logSizeBallSeq J hJ a c i).finset)
参数：hJ : J.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用引理 `PairReduction.finset_logSizeBallSeq_add_one_subset`：finset_logSizeBallSe
q_add_one_subset (hJ : J.Nonempty) (i : Nat) : (logSizeBallSeq J hJ a c (i + 1))
.finset subseteq (logSizeBallSeq J hJ a …
-/
lemma antitone_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) :
    Antitone (fun i ↦ (logSizeBallSeq J hJ a c i).finset) :=
  antitone_nat_of_succ_le (finset_logSizeBallSeq_add_one_subset hJ)
/-
**PairReduction.finset_logSizeBallSeq_subset_logSizeBallSeq_init** 是 Mathlib 中的一
个引理，位于命名空间 `PairReduction`。
形式化陈述：finset_logSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : Na
t) : (logSizeBallSeq J hJ a c i).finset subseteq J
参数：hJ : J.Nonempty；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `PairReduction.antitone_logSizeBallSeq_add_one_subset`：antitone_logSizeBa
llSeq_add_one_subset (hJ : J.Nonempty) : Antitone (fun i => (logSizeBallSeq J hJ
 a c i).finset)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma finset_logSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c i).finset ⊆ J := by
  apply subset_trans <| antitone_logSizeBallSeq_add_one_subset hJ zero_le
  simp [finset_logSizeBallSeq_zero]
/-
**PairReduction.radius_logSizeBallSeq_le** 是 Mathlib 中的一个引理，位于命名空间 `PairReductio
n`。
形式化陈述：radius_logSizeBallSeq_le (hJ : J.Nonempty) (ha : 1 < a) (hn : 1 <= n) (hJ_
card : #J <= a ^ n) (i : Nat) : (logSizeBallSeq J hJ a c i).radius <= n
参数：hJ : J.Nonempty；ha : 1 < a；hn : 1 <= n；hJ_card : #J <= a ^ n；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.exists_radius_le`：exists_radius_le (t : T) (V : Finset T) 
(ha : 1 < a) (c : Real>=0∞) : exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist
 t x <= r * c) <= a …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `PairReduction.finset_logSizeBallSeq_subset_logSizeBallSeq_init`：finset_l
ogSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) : (logSizeB
allSeq J hJ a c i).finset subseteq J
-/
lemma radius_logSizeBallSeq_le (hJ : J.Nonempty) (ha : 1 < a) (hn : 1 ≤ n) (hJ_card : #J ≤ a ^ n)
    (i : ℕ) : (logSizeBallSeq J hJ a c i).radius ≤ n := by
  match i with
  | 0 =>
    simp only [radius_logSizeBallSeq_zero, logSizeRadius, ha, ↓reduceDIte]
    exact Nat.find_min' _ ⟨hn, le_trans (by gcongr; apply Finset.filter_subset) hJ_card⟩
  | i + 1 =>
    simp only [radius_logSizeBallSeq_add_one, logSizeRadius, ha, ↓reduceDIte]
    refine Nat.find_min' _ ⟨hn, le_trans ?_ hJ_card⟩
    gcongr
    exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)
/-
**PairReduction.one_le_radius_logSizeBallSeq** 是 Mathlib 中的一个引理，位于命名空间 `PairRedu
ction`。
形式化陈述：one_le_radius_logSizeBallSeq (hJ : J.Nonempty) (ha : 1 < a) (i : Nat) : 1 
<= (logSizeBallSeq J hJ a c i).radius
参数：hJ : J.Nonempty；ha : 1 < a；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.one_le_logSizeRadius`：one_le_logSizeRadius (ha : 1 < a) : 
1 <= logSizeRadius t V a c
-/
lemma one_le_radius_logSizeBallSeq (hJ : J.Nonempty) (ha : 1 < a) (i : ℕ) :
    1 ≤ (logSizeBallSeq J hJ a c i).radius := by
  match i with
  | 0 => exact one_le_logSizeRadius ha
  | i + 1 => exact one_le_logSizeRadius ha

set_option backward.isDefEq.respectTransparency false in
/-
**PairReduction.point_mem_finset_logSizeBallSeq** 是 Mathlib 中的一个引理，位于命名空间 `PairR
eduction`。
形式化陈述：point_mem_finset_logSizeBallSeq (hJ : J.Nonempty) (i : Nat) (h : (logSizeB
allSeq J hJ a c i).finset.Nonempty) : (logSizeBallSeq J hJ a c i).point in (logS
izeBallSeq J hJ a c i).finset
参数：hJ : J.Nonempty；i : Nat；h : (logSizeBallSeq J hJ a c i).finset.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma point_mem_finset_logSizeBallSeq (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    (logSizeBallSeq J hJ a c i).point ∈ (logSizeBallSeq J hJ a c i).finset := by
  match i with
  | 0 => simp [point_logSizeBallSeq_zero, finset_logSizeBallSeq_zero, Exists.choose_spec]
  | i + 1 => simp [point_logSizeBallSeq_add_one, h, Exists.choose_spec]
/-
**PairReduction.point_mem_logSizeBallSeq_init** 是 Mathlib 中的一个引理，位于命名空间 `PairRed
uction`。
形式化陈述：point_mem_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) : (logSizeBallSe
q J hJ a c i).point in J
参数：hJ : J.Nonempty；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PairReduction.point_mem_finset_logSizeBallSeq`：point_mem_finset_logSizeB
allSeq (hJ : J.Nonempty) (i : Nat) (h : (logSizeBallSeq J hJ a c i).finset.Nonem
pty) : (logSizeBallSeq J hJ a c i).…
· 使用定理 `Finset.mem_of_subset`：mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subs
eteq s₂ -> a in s₁ -> a in s₂
· 使用引理 `PairReduction.finset_logSizeBallSeq_subset_logSizeBallSeq_init`：finset_l
ogSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) : (logSizeB
allSeq J hJ a c i).finset subseteq J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma point_mem_logSizeBallSeq_init (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c i).point ∈ J := by
  induction i with
  | zero => exact point_mem_finset_logSizeBallSeq hJ 0 hJ
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · refine Finset.mem_of_subset ?_ (point_mem_finset_logSizeBallSeq hJ (i + 1) h)
      apply finset_logSizeBallSeq_subset_logSizeBallSeq_init
    simp [point_logSizeBallSeq_add_one, ih, h]
/-
**PairReduction.point_notMem_finset_logSizeBallSeq_add_one** 是 Mathlib 中的一个引理，位于
命名空间 `PairReduction`。
形式化陈述：point_notMem_finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) : (
logSizeBallSeq J hJ a c i).point ∉ (logSizeBallSeq J hJ a c (i + 1)).finset
参数：hJ : J.Nonempty；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma point_notMem_finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : ℕ) :
    (logSizeBallSeq J hJ a c i).point ∉ (logSizeBallSeq J hJ a c (i + 1)).finset := by
  simp [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall]
/-
**PairReduction.finset_logSizeBallSeq_add_one_ssubset** 是 Mathlib 中的一个引理，位于命名空间 
`PairReduction`。
形式化陈述：finset_logSizeBallSeq_add_one_ssubset (hJ : J.Nonempty) (i : Nat) (h : (lo
gSizeBallSeq J hJ a c i).finset.Nonempty) : (logSizeBallSeq J hJ a c (i + 1)).fi
nset ⊂ (logSizeBallSeq J hJ a c i).finset
参数：hJ : J.Nonempty；i : Nat；h : (logSizeBallSeq J hJ a c i).finset.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ssubset_of_subset_not_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder 
α] [inst : Preorder α] {a b : α}, a ⊆ b → ¬b ⊆ a → a ⊂ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用引理 `PairReduction.point_mem_finset_logSizeBallSeq`：point_mem_finset_logSizeB
allSeq (hJ : J.Nonempty) (i : Nat) (h : (logSizeBallSeq J hJ a c i).finset.Nonem
pty) : (logSizeBallSeq J hJ a c i).…
· 使用引理 `PairReduction.point_notMem_finset_logSizeBallSeq_add_one`：point_notMem_f
inset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) : (logSizeBallSeq J hJ 
a c i).point ∉ (logSizeBallSeq J hJ a c (i + 1…
-/
lemma finset_logSizeBallSeq_add_one_ssubset (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    (logSizeBallSeq J hJ a c (i + 1)).finset ⊂ (logSizeBallSeq J hJ a c i).finset := by
    apply ssubset_of_subset_not_subset
    · simp [finset_logSizeBallSeq_add_one]
    refine Set.not_subset.mpr ⟨(logSizeBallSeq J hJ a c i).point, ?_, ?_⟩
    · exact point_mem_finset_logSizeBallSeq hJ i h
    · exact point_notMem_finset_logSizeBallSeq_add_one hJ i
/-
**PairReduction.card_finset_logSizeBallSeq_add_one_lt** 是 Mathlib 中的一个引理，位于命名空间 
`PairReduction`。
形式化陈述：card_finset_logSizeBallSeq_add_one_lt (hJ : J.Nonempty) (i : Nat) (h : (lo
gSizeBallSeq J hJ a c i).finset.Nonempty) : #(logSizeBallSeq J hJ a c (i + 1)).f
inset < #(logSizeBallSeq J hJ a c i).finset
参数：hJ : J.Nonempty；i : Nat；h : (logSizeBallSeq J hJ a c i).finset.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `PairReduction.finset_logSizeBallSeq_add_one_ssubset`：finset_logSizeBallS
eq_add_one_ssubset (hJ : J.Nonempty) (i : Nat) (h : (logSizeBallSeq J hJ a c i).
finset.Nonempty) : (logSizeBallSeq J hJ a…
-/
lemma card_finset_logSizeBallSeq_add_one_lt (hJ : J.Nonempty) (i : ℕ)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    #(logSizeBallSeq J hJ a c (i + 1)).finset < #(logSizeBallSeq J hJ a c i).finset := by
  simp [Finset.card_lt_card, finset_logSizeBallSeq_add_one_ssubset hJ i h]
/-
**PairReduction.card_finset_logSizeBallSeq_le** 是 Mathlib 中的一个引理，位于命名空间 `PairRed
uction`。
形式化陈述：card_finset_logSizeBallSeq_le (hJ : J.Nonempty) (i : Nat) : #(logSizeBallS
eq J hJ a c i).finset <= #J - i
参数：hJ : J.Nonempty；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `PairReduction.card_finset_logSizeBallSeq_add_one_lt`：card_finset_logSize
BallSeq_add_one_lt (hJ : J.Nonempty) (i : Nat) (h : (logSizeBallSeq J hJ a c i).
finset.Nonempty) : #(logSizeBallSeq J hJ …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `PairReduction.finset_logSizeBallSeq_add_one_subset`：finset_logSizeBallSe
q_add_one_subset (hJ : J.Nonempty) (i : Nat) : (logSizeBallSeq J hJ a c (i + 1))
.finset subseteq (logSizeBallSeq J hJ a …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Finset.card_ne_zero`：card_ne_zero : #s != 0 ↔ s.Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma card_finset_logSizeBallSeq_le (hJ : J.Nonempty) (i : ℕ) :
    #(logSizeBallSeq J hJ a c i).finset ≤ #J - i := by
  induction i with
  | zero => simp [finset_logSizeBallSeq_zero]
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c i).finset.Nonempty
    · have := card_finset_logSizeBallSeq_add_one_lt hJ i h
      lia
    apply le_trans <| Finset.card_le_card (finset_logSizeBallSeq_add_one_subset hJ i)
    suffices #(logSizeBallSeq J hJ a c i).finset = 0 by simp [this]
    rwa [← not_ne_iff, Finset.card_ne_zero.not]
/-
**PairReduction.card_finset_logSizeBallSeq_card_eq_zero** 是 Mathlib 中的一个引理，位于命名空
间 `PairReduction`。
形式化陈述：card_finset_logSizeBallSeq_card_eq_zero (hJ : J.Nonempty) : #(logSizeBallS
eq J hJ a c #J).finset = 0
参数：hJ : J.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用引理 `PairReduction.card_finset_logSizeBallSeq_le`：card_finset_logSizeBallSeq_
le (hJ : J.Nonempty) (i : Nat) : #(logSizeBallSeq J hJ a c i).finset <= #J - i
-/
lemma card_finset_logSizeBallSeq_card_eq_zero (hJ : J.Nonempty) :
    #(logSizeBallSeq J hJ a c #J).finset = 0 := by
  rw [← Nat.le_zero, ← tsub_self #J]
  exact card_finset_logSizeBallSeq_le hJ #J
/-
**PairReduction.disjoint_smallBall_logSizeBallSeq** 是 Mathlib 中的一个引理，位于命名空间 `Pai
rReduction`。
形式化陈述：disjoint_smallBall_logSizeBallSeq (hJ : J.Nonempty) {i j : Nat} (hij : i !
= j) : Disjoint ((logSizeBallSeq J hJ a c i).smallBall c) ((logSizeBallSeq J hJ 
a c j).smallBall c)
参数：hJ : J.Nonempty；hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finset.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subsete
q u) (d : Disjoint s u) : Disjoint s t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用引理 `PairReduction.antitone_logSizeBallSeq_add_one_subset`：antitone_logSizeBa
llSeq_add_one_subset (hJ : J.Nonempty) : Antitone (fun i => (logSizeBallSeq J hJ
 a c i).finset)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
-/
lemma disjoint_smallBall_logSizeBallSeq (hJ : J.Nonempty) {i j : ℕ} (hij : i ≠ j) :
    Disjoint
      ((logSizeBallSeq J hJ a c i).smallBall c) ((logSizeBallSeq J hJ a c j).smallBall c) := by
  wlog! h : i < j generalizing i j
  · exact Disjoint.symm <| this hij.symm <| (ne_iff_lt_iff_le.mpr h).mp hij.symm
  apply Finset.disjoint_of_subset_right
  · exact (Finset.filter_subset _ _).trans (antitone_logSizeBallSeq_add_one_subset hJ h)
  simp [finset_logSizeBallSeq_add_one, Finset.disjoint_sdiff]

/-- Given a log-size ball sequence `(Vᵢ, tᵢ, rᵢ)`, we define the pair set sequence by
`Kᵢ = {tᵢ} × {x ∈ Vᵢ | dist(tᵢ, x) ≤ rᵢc}`. -/
noncomputable
/-
**PairReduction.pairSetSeq** 是 Mathlib 中的一个定义，位于命名空间 `PairReduction`。
形式化陈述：pairSetSeq (J : Finset T) (a c : Real>=0∞) (n : Nat) : Finset (T × T)
参数：J : Finset T；a c : Real>=0∞；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pairSetSeq (J : Finset T) (a c : ℝ≥0∞) (n : ℕ) : Finset (T × T) :=
  if hJ : J.Nonempty then
    Finset.product {(logSizeBallSeq J hJ a c n).point} ((logSizeBallSeq J hJ a c n).ball c)
  else ∅

/-- Given the pair set sequence Kᵢ we define the pair set `K` by `K = ⋃ i, Kᵢ`. -/
noncomputable
/-
**PairReduction.pairSet** 是 Mathlib 中的一个定义，位于命名空间 `PairReduction`。
形式化陈述：pairSet (J : Finset T) (a c : Real>=0∞) : Finset (T × T)
参数：J : Finset T；a c : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pairSet (J : Finset T) (a c : ℝ≥0∞) : Finset (T × T) :=
  Finset.biUnion (Finset.range #J) (pairSetSeq J a c)
/-
**PairReduction.pairSet_empty_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`
。
形式化陈述：pairSet_empty_eq_empty (a c : Real>=0∞) : pairSet (∅ : Finset T) a c = ∅
参数：a c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pairSet_empty_eq_empty (a c : ℝ≥0∞) : pairSet (∅ : Finset T) a c = ∅ := rfl
/-
**PairReduction.pairSet_subset** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`。
形式化陈述：pairSet_subset : pairSet J a c subseteq J ×ˢ J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.biUnion_subset_iff_forall_subset`：biUnion_subset_iff_forall_subse
t {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β} {f : α -> Finset β
} : s.biUnion f subseteq t ↔ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用引理 `PairReduction.point_mem_logSizeBallSeq_init`：point_mem_logSizeBallSeq_in
it (hJ : J.Nonempty) (i : Nat) : (logSizeBallSeq J hJ a c i).point in J
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用引理 `PairReduction.finset_logSizeBallSeq_subset_logSizeBallSeq_init`：finset_l
ogSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) : (logSizeB
allSeq J hJ a c i).finset subseteq J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma pairSet_subset : pairSet J a c ⊆ J ×ˢ J := by
  unfold pairSet
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i hi
  by_cases hJ : J.Nonempty
  · simp only [pairSetSeq, hJ, ↓reduceDIte]
    apply Finset.product_subset_product
    · exact Finset.singleton_subset_iff.mpr (point_mem_logSizeBallSeq_init hJ _)
    exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)
  simp [pairSetSeq, hJ]
/-
**PairReduction.card_pairSetSeq_le_logSizeRadius_mul** 是 Mathlib 中的一个引理，位于命名空间 `
PairReduction`。
形式化陈述：card_pairSetSeq_le_logSizeRadius_mul (hJ : J.Nonempty) (i : Nat) (ha : 1 <
 a) : ↑(#(pairSetSeq J a c i)) <= (if (logSizeBallSeq J hJ a c i).finset.Nonempt
y then 1 else 0) * a ^ (logSizeBallSeq J hJ a c i).radius
参数：hJ : J.Nonempty；i : Nat；ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `PairReduction.card_le_logSizeRadius_le_pow_logSizeRadius`：card_le_logSiz
eRadius_le_pow_logSizeRadius (ha : 1 < a) : #(V.filter fun x => edist t x <= log
SizeRadius t V a c * c) <= a ^ (logSizeRadius …
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Finset.product_empty`：product_empty (s : Finset α) : s ×ˢ (∅ : Finset β)
 = ∅
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma card_pairSetSeq_le_logSizeRadius_mul (hJ : J.Nonempty) (i : ℕ) (ha : 1 < a) :
    ↑(#(pairSetSeq J a c i)) ≤ (if (logSizeBallSeq J hJ a c i).finset.Nonempty then 1 else 0)
    * a ^ (logSizeBallSeq J hJ a c i).radius := by
  induction i with
  | zero =>
    simpa [pairSetSeq, hJ, finset_logSizeBallSeq_zero, logSizeBallStruct.ball,
      radius_logSizeBallSeq_zero] using! card_le_logSizeRadius_le_pow_logSizeRadius ha
  | succ i ih =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [pairSetSeq, logSizeBallStruct.ball, h, hJ]
        using! card_le_logSizeRadius_le_pow_logSizeRadius ha
    simp [pairSetSeq, logSizeBallStruct.ball, h, hJ]
/-
**PairReduction.logSizeRadius_le_card_smallBall** 是 Mathlib 中的一个引理，位于命名空间 `PairR
eduction`。
形式化陈述：logSizeRadius_le_card_smallBall (hJ : J.Nonempty) (i : Nat) (ha : 1 < a) :
 (if (logSizeBallSeq J hJ a c i).finset.Nonempty then 1 else 0) * a ^ ((logSizeB
allSeq J hJ a c i).radius - 1) <= #((logSizeBallSeq J hJ a c i).smallBall c)
参数：hJ : J.Nonempty；i : Nat；ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `PairReduction.pow_logSizeRadius_le_card_le_logSizeRadius`：pow_logSizeRad
ius_le_card_le_logSizeRadius (ha : 1 < a) (ht : t in V) : a ^ (logSizeRadius t V
 a c - 1) <= #(V.filter fun x => edist t x <= …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `PairReduction.point_mem_finset_logSizeBallSeq`：point_mem_finset_logSizeB
allSeq (hJ : J.Nonempty) (i : Nat) (h : (logSizeBallSeq J hJ a c i).finset.Nonem
pty) : (logSizeBallSeq J hJ a c i).…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma logSizeRadius_le_card_smallBall (hJ : J.Nonempty) (i : ℕ) (ha : 1 < a) :
    (if (logSizeBallSeq J hJ a c i).finset.Nonempty then 1 else 0) *
    a ^ ((logSizeBallSeq J hJ a c i).radius - 1) ≤ #((logSizeBallSeq J hJ a c i).smallBall c) := by
  match i with
  | 0 =>
    simpa [finset_logSizeBallSeq_zero, hJ, logSizeBallStruct.smallBall, radius_logSizeBallSeq_zero]
      using! pow_logSizeRadius_le_card_le_logSizeRadius ha (Exists.choose_spec hJ)
  | i + 1 =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [h, logSizeBallStruct.smallBall, radius_logSizeBallSeq_add_one] using!
        pow_logSizeRadius_le_card_le_logSizeRadius ha
          (point_mem_finset_logSizeBallSeq hJ _ h)
    simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**PairReduction.card_pairSet_le** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`。
形式化陈述：card_pairSet_le (ha : 1 < a) : #(pairSet J a c) <= a * #J
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用引理 `PairReduction.card_pairSetSeq_le_logSizeRadius_mul`：card_pairSetSeq_le_l
ogSizeRadius_mul (hJ : J.Nonempty) (i : Nat) (ha : 1 < a) : ↑(#(pairSetSeq J a c
 i)) <= (if (logSizeBallSeq J hJ a c i).…
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用引理 `PairReduction.logSizeRadius_le_card_smallBall`：logSizeRadius_le_card_sma
llBall (hJ : J.Nonempty) (i : Nat) (ha : 1 < a) : (if (logSizeBallSeq J hJ a c i
).finset.Nonempty then 1 else 0) * …
（共 45 条，此处仅展示前 30 条）
-/
lemma card_pairSet_le (ha : 1 < a) : #(pairSet J a c) ≤ a * #J := by
  wlog hJ : J.Nonempty
  · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]
  unfold pairSet
  grw [Finset.card_biUnion_le, Nat.cast_sum,
    Finset.sum_le_sum fun i _ ↦ card_pairSetSeq_le_logSizeRadius_mul hJ i ha,
    Finset.sum_le_sum fun _ _ ↦ mul_le_mul_right (pow_le_pow_right₀ ha.le le_tsub_add) _]
  conv_lhs => enter [2]; ext _; rw [pow_add, pow_one, ← mul_assoc, mul_comm]
  grw [← Finset.mul_sum]
  gcongr
  grw [Finset.sum_le_sum fun i _ ↦ logSizeRadius_le_card_smallBall hJ i ha, ← Nat.cast_sum,
    ← Finset.card_biUnion fun _ _ _ _ ↦ disjoint_smallBall_logSizeBallSeq hJ]
  gcongr
  unfold logSizeBallStruct.smallBall
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i _
  exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)
/-
**PairReduction.edist_le_of_mem_pairSet** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction
`。
形式化陈述：edist_le_of_mem_pairSet (ha : 1 < a) (hJ_card : #J <= a ^ n) {s t : T} (h 
: (s, t) in pairSet J a c) : edist s t <= n * c
参数：ha : 1 < a；hJ_card : #J <= a ^ n；h : (s, t) in pairSet J a c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用引理 `PairReduction.radius_logSizeBallSeq_le`：radius_logSizeBallSeq_le (hJ : J
.Nonempty) (ha : 1 < a) (hn : 1 <= n) (hJ_card : #J <= a ^ n) (i : Nat) : (logSi
zeBallSeq J hJ a c i).radius…
· 使用定理 `Finset.mem_product`：mem_product {p : α × β} : p in s ×ˢ t ↔ p.1 in s ∧ p
.2 in t
· 使用引理 `PairReduction.pairSet_subset`：pairSet_subset : pairSet J a c subseteq J 
×ˢ J
· 使用定理 `Finset.card_le_one_iff`：card_le_one_iff : #s <= 1 ↔ forall {a b}, a in s
 -> b in s -> a = b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
（共 35 条，此处仅展示前 30 条）
-/
lemma edist_le_of_mem_pairSet (ha : 1 < a) (hJ_card : #J ≤ a ^ n) {s t : T}
    (h : (s, t) ∈ pairSet J a c) : edist s t ≤ n * c := by
  obtain ⟨i, hiJ, h'⟩ : ∃ i < #J, (s, t) ∈ pairSetSeq J a c i := by simpa [pairSet] using h
  have hJ : J.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hiJ)
  wlog! hn : 1 ≤ n
  · suffices s = t by simp [this]
    simp only [Nat.lt_one_iff.mp hn, pow_zero, Nat.cast_le_one] at hJ_card
    have ⟨hs, ht⟩ := Finset.mem_product.mp (pairSet_subset h)
    exact Finset.card_le_one_iff.mp hJ_card hs ht
  simp only [pairSetSeq, hJ, ↓reduceDIte, logSizeBallStruct.ball, Finset.product_eq_sprod,
    Finset.singleton_product, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk,
    Prod.mk.injEq, exists_eq_right_right] at h'
  obtain ⟨⟨ht, hdist⟩, rfl⟩ := h'
  grw [hdist, radius_logSizeBallSeq_le hJ ha hn hJ_card i]
/-
**PairReduction.iSup_edist_pairSet** 是 Mathlib 中的一个引理，位于命名空间 `PairReduction`。
形式化陈述：iSup_edist_pairSet {E : Type*} [PseudoEMetricSpace E] (ha : 1 < a) (f : T 
-> E) : ⨆ (s : J) (t : { t : J // edist s t <= c}), edist (f s) (f t) <= 2 * ⨆ p
 : pairSet J a c, edist (f p.1.1) (f p.1.2)
参数：ha : 1 < a；f : T -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 78 条，此处仅展示前 30 条）
-/
lemma iSup_edist_pairSet {E : Type*} [PseudoEMetricSpace E] (ha : 1 < a) (f : T → E) :
    ⨆ (s : J) (t : { t : J // edist s t ≤ c}), edist (f s) (f t)
        ≤ 2 * ⨆ p : pairSet J a c, edist (f p.1.1) (f p.1.2) := by
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; rintro ⟨⟨t, ht⟩, hst⟩
  have hJ : J.Nonempty := ⟨s, hs⟩
  let P (l : ℕ) := s ∈ (logSizeBallSeq J hJ a c l).finset ∧ t ∈ (logSizeBallSeq J hJ a c l).finset
  let l := Nat.findGreatest P (#J - 1)
  obtain ⟨hsV, htV⟩ : P l := by
    apply Nat.findGreatest_spec zero_le
    simpa [P, finset_logSizeBallSeq_zero] using ⟨hs, ht⟩
  wlog h : s ∉ (logSizeBallSeq J hJ a c (l + 1)).finset generalizing s t
  · have h' : t ∉ (logSizeBallSeq J hJ a c (l + 1)).finset := by
      have hl : l < #J - 1 := by
        by_contra hl
        simp only [not_lt, tsub_le_iff_right] at hl
        have hlJ : l + 1 = #J := by
          refine Nat.le_antisymm_iff.mpr ⟨?_, hl⟩
          dsimp [l]
          grw [← Nat.sub_add_cancel <| Order.one_le_iff_pos.mpr (Finset.card_pos.mpr hJ),
            Nat.findGreatest_le]
          rfl
        apply h
        suffices h_emp : (logSizeBallSeq J hJ a c (l + 1)).finset = ∅ from by simp [h_emp]
        rw [← Finset.card_eq_zero, ← Nat.le_zero, ← Nat.sub_self #J, hlJ]
        apply card_finset_logSizeBallSeq_le
      simp only [Decidable.not_not] at h
      have hP := Nat.findGreatest_is_greatest (lt_add_one l) (Nat.add_one_le_of_lt hl)
      simpa [P, h] using hP
    have hts : edist t s ≤ c := by rw [edist_comm]; exact hst
    rw [edist_comm]
    have hP : P = (fun l ↦
      t ∈ (logSizeBallSeq J hJ a c l).finset ∧ s ∈ (logSizeBallSeq J hJ a c l).finset) := by
        ext; simp [P, and_comm]
    simp only [hP, l] at htV hsV h'
    exact this t ht s hs hts htV hsV h'
  simp only [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall, Finset.mem_sdiff, hsV,
    Finset.mem_filter, true_and, not_le, not_lt] at h
  have hsB : s ∈ (logSizeBallSeq J hJ a c l).ball c := by
    simp only [logSizeBallStruct.ball, Finset.mem_filter, hsV, true_and]
    grw [h, tsub_le_self]
  have htB : t ∈ (logSizeBallSeq J hJ a c l).ball c := by
    simp only [logSizeBallStruct.ball, Finset.mem_filter, htV, true_and]
    apply le_trans (edist_triangle _ s _)
    apply le_of_le_of_eq (add_le_add h hst)
    nth_rw 3 [← one_mul c]
    rw [← add_mul]
    congr
    rw [ENNReal.sub_add_eq_add_sub _ (ENNReal.one_ne_top),
      ENNReal.add_sub_cancel_right (ENNReal.one_ne_top)]
    rw [← Nat.cast_one]
    gcongr
    exact one_le_radius_logSizeBallSeq hJ ha l
  have hsP : ((logSizeBallSeq J hJ a c l).point, s) ∈ pairSetSeq J a c l := by
    simp [pairSetSeq, hJ, hsB]
  have htP : ((logSizeBallSeq J hJ a c l).point, t) ∈ pairSetSeq J a c l := by
    simp [pairSetSeq, hJ, htB]
  have sup_bound {x y : T} (hxy : (x, y) ∈ pairSetSeq J a c l) :
    edist (f x) (f y) ≤ ⨆ p : pairSet J a c, edist (f p.1.1) (f p.1.2) := by
    simp only [iSup_subtype]
    apply le_iSup_of_le (i := (x, y))
    apply le_iSup_of_le
    · exact le_rfl
    refine Finset.mem_biUnion.mpr ⟨l, ?_, hxy⟩
    refine Finset.mem_range.mpr <| lt_of_le_of_lt (Nat.findGreatest_le (#J - 1)) ?_
    exact Nat.sub_lt (Finset.card_pos.mpr hJ) zero_lt_one
  rw [two_mul]
  apply le_trans (edist_triangle _ (f (logSizeBallSeq J hJ a c l).point) _)
  rw [edist_comm]
  apply add_le_add (sup_bound hsP) (sup_bound htP)

end PairReduction

open PairReduction in
/-- **Pair Reduction**: Given pseudometric spaces `T` and `E`, `c ≥ 0`, and a finite subset `J` of
`T` such that `|J| ≤ aⁿ` for some `a ≥ 0` and `n : ℕ`, `pair_reduction` states that there exists a
set `K ⊆ J²` such that for any function `f : T → E`:
1. `|K| ≤ a|J|`
2. `∀ (s, t) ∈ K, d(s, t) ≤ cn`
3. `sup_{s, t ∈ J : d(s, t) ≤ c} d(f(s), f(t)) ≤ 2 sup_{(s, t) ∈ K} d(f(s), f(t))`
-/
/-
**EMetric.pair_reduction** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EMetric.pair_reduction (hJ_card : #J <= a ^ n) (c : Real>=0∞) (E : Type*) 
[PseudoEMetricSpace E] : exists K : Finset (T × T), K subseteq J ×ˢ J ∧ #K <= a 
* #J ∧ (forall s t, (s, t) in K -> edist s t <= n * c) ∧ (forall f : T -> E, ⨆ (
s : J) (t : { t : J // edist s t <= c}), edist (f s) (f t) <= 2 * ⨆ p : K, edist
 (f p.1.1) (f p.1.2))
参数：hJ_card : #J <= a ^ n；c : Real>=0∞；E : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.product_empty`：product_empty (s : Finset α) : s ×ˢ (∅ : Finset β)
 = ∅
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ENNReal.pow_le_pow_left`：∀ {a b : ENNReal} {n : ℕ}, a ≤ b → a ^ n ≤ b ^ 
n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
**Pair Reduction**: Given pseudometric spaces `T` and `E`, `c ≥ 0`, and a finite
 subset `J` of
`T` such that `|J| ≤ aⁿ` for some `a ≥ 0` and `n : ℕ`, `pair_reduction` states t
hat there exists a
set `K ⊆ J²` such that for any function `f : T → E`:
1. `|K| ≤ a|J|`
2. `∀ (s, t) ∈ K, d(s, t) ≤ cn`
3. `sup_{s, t ∈ J : d(s, t) ≤ c} d(f(s), f(t)) ≤ 2 sup_{(s, t) ∈ K} d(f(s), f(t)
)`
-/
theorem EMetric.pair_reduction
    (hJ_card : #J ≤ a ^ n) (c : ℝ≥0∞) (E : Type*) [PseudoEMetricSpace E] :
    ∃ K : Finset (T × T), K ⊆ J ×ˢ J
      ∧ #K ≤ a * #J
      ∧ (∀ s t, (s, t) ∈ K → edist s t ≤ n * c)
      ∧ (∀ f : T → E,
        ⨆ (s : J) (t : { t : J // edist s t ≤ c}), edist (f s) (f t)
        ≤ 2 * ⨆ p : K, edist (f p.1.1) (f p.1.2)) := by
  classical
  rcases le_or_gt a 1 with ha1 | ha1
  · rcases isEmpty_or_nonempty J with hJ | hJ
    · simp only [Finset.isEmpty_coe_sort] at hJ
      simp [hJ]
    obtain ⟨x₀, rfl⟩ : ∃ x₀, J = {x₀} := by
      rw [← Finset.card_eq_one]
      refine le_antisymm ?_ ?_
      · suffices (#J : ENNReal) ≤ 1 by norm_cast at this
        refine hJ_card.trans ?_
        conv_rhs => rw [← one_pow n]
        exact ENNReal.pow_le_pow_left ha1
      · rwa [Finset.one_le_card, ← Finset.nonempty_coe_sort]
    simp_all
  · exact ⟨pairSet J a c, pairSet_subset, card_pairSet_le ha1,
      fun _ _ ↦ edist_le_of_mem_pairSet ha1 hJ_card, iSup_edist_pairSet ha1⟩
