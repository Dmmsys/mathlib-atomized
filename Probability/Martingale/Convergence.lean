/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Martingale.Upcrossing

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale. It also contains the L¹ martingale convergence theorem which provides
an L¹ limit to a uniformly integrable submartingale. Finally, it also contains the Lévy upwards
theorems.

## Main results

* `MeasureTheory.Submartingale.ae_tendsto_limitProcess`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere to its limit process.
* `MeasureTheory.Submartingale.memLp_limitProcess`: the limit process of an Lᵖ-bounded
  submartingale is Lᵖ.
* `MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere and in L¹ to an integrable function which is measurable with respect
  to the σ-algebra `⨆ n, ℱ n`.
* `MeasureTheory.Martingale.ae_eq_condExp_limitProcess`: part b the L¹ martingale convergence
  theorem: if `f` is a uniformly integrable martingale strongly adapted to the filtration `ℱ`, then
  `f n` equals `𝔼[g | ℱ n]` almost everywhere where `g` is the limiting process of `f`.
* `MeasureTheory.Integrable.tendsto_ae_condExp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges
  almost everywhere to `g`.
* `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges in
  L¹ to `g`.

-/

public section


open TopologicalSpace Filter MeasureTheory.Filtration

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}

section AeConvergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E} \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

In terms of implementation, we have `tendsto_of_no_upcrossings` which shows that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $|f_n(\omega)|$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

Furthermore, we introduce `Filtration.limitProcess` which chooses the limiting random variable
of a stochastic process if it exists, otherwise returning 0. Hence, instead of showing an
existence statement, we phrase the a.e. martingale convergence theorem by showing that a
submartingale converges to its `limitProcess` almost everywhere.

-/


/-- If a stochastic process has a finite number of upcrossings from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
/-
**MeasureTheory.not_frequently_of_upcrossings_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f
 ω != ∞) : ¬((existsᶠ n in atTop, f n ω < a) ∧ existsᶠ n in atTop, b < f n ω)
参数：hab : a < b；hω : upcrossings a b f ω != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upcrossings_lt_top_iff`：upcrossings_lt_top_iff : upcrossin
gs a b f ω < ∞ ↔ exists k, forall N, upcrossingsBefore a b f N ω <= k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing`：upcrossingsBefo
re_lt_of_exists_upcrossing (hab : a < b) {N₁ N₂ : Nat} (hN₁ : N <= N₁) (hN₁' : f
 N₁ ω < a) (hN₂ : N₁ <= N₂) (hN₂' : b < f N₂ …

--- 原说明 ---
If a stochastic process has a finite number of upcrossings from below `a` to abo
ve `b`,
then it does not frequently visit both below `a` and above `b`.
-/
theorem not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
    ¬((∃ᶠ n in atTop, f n ω < a) ∧ ∃ᶠ n in atTop, b < f n ω) := by
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω
  replace hω : ∃ k, ∀ N, upcrossingsBefore a b f N ω < k := by
    obtain ⟨k, hk⟩ := hω
    exact ⟨k + 1, fun N => lt_of_le_of_lt (hk N) k.lt_succ_self⟩
  rintro ⟨h₁, h₂⟩
  rw [frequently_atTop] at h₁ h₂
  refine Classical.not_not.2 hω ?_
  push Not
  intro k
  induction k with
  | zero => simp only [zero_le, exists_const]
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact ⟨N₂ + 1, Nat.succ_le_of_lt <|
      lt_of_le_of_lt hN (upcrossingsBefore_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩

/-- A stochastic process that frequently visits below `a` and above `b` has infinite upcrossings. -/
/-
**MeasureTheory.upcrossings_eq_top_of_frequently_lt** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : existsᶠ n in atTop
, f n ω < a) (h₂ : existsᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞
参数：hab : a < b；h₁ : existsᶠ n in atTop, f n ω < a；h₂ : existsᶠ n in atTop, b < f
 n ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `MeasureTheory.not_frequently_of_upcrossings_lt_top`：not_frequently_of_up
crossings_lt_top (hab : a < b) (hω : upcrossings a b f ω != ∞) : ¬((existsᶠ n in
 atTop, f n ω < a) ∧ existsᶠ n in atTop,…

--- 原说明 ---
A stochastic process that frequently visits below `a` and above `b` has infinite
 upcrossings.
-/
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in atTop, f n ω < a)
    (h₂ : ∃ᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞ :=
  by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩

/-- A realization of a stochastic process with bounded upcrossings and bounded limit inferiors is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
/-
**MeasureTheory.tendsto_of_uncrossing_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_of_uncrossing_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : Real>=0∞)
) atTop < ∞) (hf₂ : forall a b : Rat, a < b -> upcrossings a b f ω < ∞) : exists
 c, Tendsto (fun n => f n ω) atTop (𝓝 c)
参数：hf₁ : liminf (fun n => (‖f n ω‖₊ : Real>=0∞)) atTop < ∞；hf₂ : forall a b : Ra
t, a < b -> upcrossings a b f ω < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_no_upcrossings`：tendsto_of_no_upcrossings [DenselyOrdered α] 
{f : Filter β} {u : β -> α} {s : Set α} (hs : Dense s) (H : forall a in s, foral
l b in s, a < b…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Rat.denseRange_cast`：Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [
IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜] : 
DenseRang…
· 使用定理 `MeasureTheory.not_frequently_of_upcrossings_lt_top`：not_frequently_of_up
crossings_lt_top (hab : a < b) (hω : upcrossings a b f ω != ∞) : ¬((existsᶠ n in
 atTop, f n ω < a) ∧ existsᶠ n in atTop,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.isBoundedUnder_le_abs`：isBoundedUnder_le_abs [AddCommGroup α] [Li
nearOrder α] [IsOrderedAddMonoid α] {f : Filter β} {u : β -> α} : (f.IsBoundedUn
der (· <= ·) fun a…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.exists_upcrossings_of_not_bounded_under`：exists_upcrossings_of_n
ot_bounded_under {ι : Type*} {l : Filter ι} {x : ι -> Real} (hf : liminf (fun i 
=> (Real.nnabs (x i) : Real>=0∞)) l !…
· 使用定理 `MeasureTheory.upcrossings_eq_top_of_frequently_lt`：upcrossings_eq_top_of
_frequently_lt (hab : a < b) (h₁ : existsᶠ n in atTop, f n ω < a) (h₂ : existsᶠ 
n in atTop, b < f n ω) : upcrossings a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A realization of a stochastic process with bounded upcrossings and bounded limit
 inferiors is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since
 it is not as easy
to change `<` to `≠` under binders.
-/
theorem tendsto_of_uncrossing_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).ne
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact
      False.elim ((hf₂ a b hab).ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
/-
**MeasureTheory.Submartingale.upcrossings_ae_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0} {a b : ℝ}   {f : ℕ → Ω → ℝ} {R : NNReal} [Meas
ureTheory.IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ (n : 
ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R) → a < b → ∀ᵐ (ω : Ω) ∂μ, MeasureTheory
.upcrossings a b f ω < ⊤
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R；ω : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `MeasureTheory.StronglyAdapted.measurable_upcrossings`：∀ {Ω : Type u_1} {
m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {ℱ : MeasureTheory.Filtration 
ℕ m0},   MeasureTheory.StronglyAdapted ℱ f…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_p
art`：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f 
: ℕ → Ω → ℝ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTheory…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_lt_top`：div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y < ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
· 使用定理 `nnnorm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E),
 ‖a + b‖₊ ≤ ‖a‖₊ + ‖b‖₊
· 使用定理 `MeasureTheory.lintegral_add_right`：lintegral_add_right (f : α -> Real>=0
∞) {g : α -> Real>=0∞} (hg : Measurable g) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ +
 ∫⁻ a, g a ∂μ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
An L¹-bounded submartingale has bounded upcrossings almost everywhere.
-/
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine ae_lt_top (hf.stronglyAdapted.measurable_upcrossings hab) ?_
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at this
  · refine (lt_of_le_of_lt this (ENNReal.div_lt_top ?_ ?_)).ne
    · have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ Set.univ := by
        simp_rw [eLpNorm_one_eq_lintegral_enorm] at hbdd
        intro n
        refine (lintegral_mono ?_ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans ?_
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ENNReal.coe_add, ENNReal.coe_le_coe]
          exact nnnorm_add_le _ _
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add (hbdd _) le_rfl
      refine ne_of_lt (iSup_lt_iff.2 ⟨R + ‖a‖₊ * μ Set.univ, ENNReal.add_lt_top.2
        ⟨ENNReal.coe_lt_top, by finiteness⟩,
        fun n => le_trans ?_ (hR' n)⟩)
      refine lintegral_mono fun ω => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
      · by_cases! hnonneg : 0 ≤ f n ω - a
        · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        · rw [posPart_eq_zero.2 hnonneg.le]
          exact norm_nonneg _
      · finiteness
    · simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · left; simp only [hab, Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
  · left; finiteness
/-
**MeasureTheory.Submartingale.upcrossings_ae_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ (n : ℕ), Measur
eTheory.eLpNorm (f n) 1 μ ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, ∀ (a b : ℚ), a < b → Meas
ureTheory.upcrossings (↑a) (↑b) f ω < ⊤
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R；ω : Ω；a b : ℚ；↑a；↑b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.Submartingale.upcrossings_ae_lt_top'`：∀ {Ω : Type u_1} {m0
 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtratio
n ℕ m0} {a b : ℝ}   {f : ℕ → Ω → ℝ} {R :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
-/
theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)

/-- An L¹-bounded submartingale converges almost everywhere. -/
/-
**MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ (n : ℕ), Measur
eTheory.eLpNorm (f n) 1 μ ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, ∃ c, Filter.Tendsto (fun 
n => f n ω) Filter.atTop (nhds c)
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R；ω : Ω；fun n => f n ω；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_bdd_liminf_atTop_of_eLpNorm_bdd`：ae_bdd_liminf_atTop_of
_eLpNorm_bdd {p : Real>=0∞} (hp : p != 0) {f : Nat -> α -> E} (hfmeas : forall n
, Measurable (f n)) (hbdd : forall n, …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Submartingale.upcrossings_ae_lt_top`：∀ {Ω : Type u_1} {m0 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration
 ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.tendsto_of_uncrossing_lt_top`：tendsto_of_uncrossing_lt_top
 (hf₁ : liminf (fun n => (‖f n ω‖₊ : Real>=0∞)) atTop < ∞) (hf₂ : forall a b : R
at, a < b -> upcrossings a b f ω…

--- 原说明 ---
An L¹-bounded submartingale converges almost everywhere.
-/
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero
    (fun n => (hf.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂
  exact tendsto_of_uncrossing_lt_top h₂ h₁
/-
**MeasureTheory.Submartingale.exists_ae_trim_tendsto_of_bdd** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ (n : ℕ), Measur
eTheory.eLpNorm (f n) 1 μ ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ.trim ⋯, ∃ c, Filter.Tendst
o (fun n => f n ω) Filter.atTop (nhds c)
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R；ω : Ω；fun n => f n ω；nhds c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.measurableSet_exists_tendsto`：MeasureTheory.measurableSet_
exists_tendsto [TopologicalSpace γ] [IsCompletelyPseudoMetrizableSpace γ] [Secon
dCountableTopology γ] [Measurabl…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`：∀ {Ω : Type u_1} {
m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrat
ion ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
-/
theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _ : ⨆ n, ℱ n ≤ m0),
      ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  let := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
  · exact MeasurableSet.compl <| measurableSet_exists_tendsto
      fun n => (hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩) le_rfl

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
/-
**MeasureTheory.Submartingale.ae_tendsto_limitProcess** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} [MeasureTheory.
IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     (∀ (n : ℕ), Measur
eTheory.eLpNorm (f n) 1 μ ≤ ↑R) →       ∀ᵐ (ω : Ω) ∂μ, Filter.Tendsto (fun n => 
f n ω) Filter.atTop (nhds (MeasureTheory.Filtration.limitProcess f ℱ μ ω))
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) 1 μ ≤ ↑R；ω : Ω；fun n => f n ω；nhds (Me
asureTheory.Filtration.limitProcess f ℱ μ ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Submartingale.exists_ae_trim_tendsto_of_bdd`：∀ {Ω : Type u
_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Fi
ltration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae'`：aemeasurable_of_tendsto_metrizab
le_ae' {μ : Measure α} {f : Nat -> α -> β} {g : α -> β} (hf : forall n, AEMeasur
able (f n) μ) (h_ae_tendsto …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
· 使用定理 `MeasureTheory.Filtration.limitProcess.eq_1`：∀ {Ω : Type u_1} {ι : Type u
_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {E : Type u_4} [inst_1 : Zero E]
   [inst_2 : TopologicalSpace E]…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**Almost everywhere martingale convergence theorem**: An L¹-bounded submartingal
e converges
almost everywhere to a `⨆ n, ℱ n`-measurable function.
-/
theorem Submartingale.ae_tendsto_limitProcess [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  suffices
      ∃ g, StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) by
    rw [limitProcess, dif_pos this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω => if h : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, ℱ n] g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n => ((hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
/-
**MeasureTheory.Submartingale.memLp_limitProcess** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} {p : ENNReal}, 
  MeasureTheory.Submartingale f ℱ μ →     (∀ (n : ℕ), MeasureTheory.eLpNorm (f n
) p μ ≤ ↑R) →       MeasureTheory.MemLp (MeasureTheory.Filtration.limitProcess f
 ℱ μ) p μ
参数：∀ (n : ℕ), MeasureTheory.eLpNorm (f n) p μ ≤ ↑R；MeasureTheory.Filtration.limi
tProcess f ℱ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd`：memLp_limitP
rocess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGro
up F] {ℱ : Filtration Nat m} {f : Nat -> Ω -> F}…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m

--- 原说明 ---
The limiting process of an Lᵖ-bounded submartingale is Lᵖ.
-/
theorem Submartingale.memLp_limitProcess {p : ℝ≥0∞} (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : MemLp (ℱ.limitProcess f μ) p μ :=
  memLp_limitProcess_of_eLpNorm_bdd
    (fun n => ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) hbdd

end AeConvergence

section L1Convergence

variable [IsFiniteMeasure μ] {g : Ω → ℝ}

/-!

### L¹ martingale convergence theorem

We will now prove the L¹ martingale convergence theorems.

The L¹ martingale convergence theorem states that:
(a) if `f` is a uniformly integrable (in the probability sense) submartingale strongly adapted to
  the filtration `ℱ`, it converges in L¹ to an integrable function `g` which is measurable with
  respect to `ℱ∞ := ⨆ n, ℱ n` and
(b) if `f` is actually a martingale, `f n = 𝔼[g | ℱ n]` almost everywhere.
(c) Finally, if `h` is integrable and measurable with respect to `ℱ∞`, `(𝔼[h | ℱ n])ₙ` is a
  uniformly integrable martingale which converges to `h` almost everywhere and in L¹.

The proof is quite simple. (a) follows directly from the a.e. martingale convergence theorem
and the Vitali convergence theorem as our definition of uniform integrability (in the probability
sense) directly implies L¹-uniform boundedness. We note that our definition of uniform
integrability is slightly non-standard but is equivalent to the usual literary definition. This
equivalence is provided by `MeasureTheory.uniformIntegrable_iff`.

(b) follows since given $n$, we have for all $m \ge n$,
$$
  \|f_n - \mathbb{E}[g \mid \mathcal{F}_n]\|_1 =
    \|\mathbb{E}[f_m - g \mid \mathcal{F}_n]\|_1 \le \|f_m - g\|_1.
$$
Thus, taking $m \to \infty$ provides the almost everywhere equality.

Finally, to prove (c), we define $f_n := \mathbb{E}[h \mid \mathcal{F}_n]$. It is clear that
$(f_n)_n$ is a martingale by the tower property for conditional expectations. Furthermore,
$(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
uniformly integrable in the measure theory sense, for all $\epsilon > 0$, there exists some
$\delta > 0$ such that for all measurable set $A$ with $\mu(A) < δ$, we have
$\mathbb{E}|h|\mathbf{1}_A < \epsilon$. So, since for sufficiently large $\lambda$, by the Markov
inequality, we have for all $n$,
$$
  \mu(|f_n| \ge \lambda) \le \lambda^{-1}\mathbb{E}|f_n| \le \lambda^{-1}\mathbb{E}|h| < \delta,
$$
we have for sufficiently large $\lambda$, for all $n$,
$$
  \mathbb{E}|f_n|\mathbf{1}_{|f_n| \ge \lambda} \le
    \mathbb{E}|h|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon,
$$
implying $(f_n)_n$ is uniformly integrable. Now, to prove $f_n \to h$ almost everywhere and in
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (b) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}[\mathbb{E}[g \mid \mathcal{F}_n]\mathbf{1}_s] =
    \mathbb{E}[\mathbb{E}[h \mid \mathcal{F}_n]\mathbf{1}_s] = \mathbb{E}h\mathbf{1}_s
$$
where $\mathbb{E}[g \mid \mathcal{F}_n] = \mathbb{E}[h \mid \mathcal{F}_n]$ almost everywhere
by part (b); the equality also holds for all $s \in \mathcal{F}_\infty$ by Dynkin's theorem.
Thus, as both $h$ and $g$ are $\mathcal{F}_\infty$-measurable, $h = g$ almost everywhere as
required.

Similar to the a.e. martingale convergence theorem, rather than showing the existence of the
limiting process, we phrase the L¹-martingale convergence theorem by proving that a submartingale
does converge in L¹ to its `limitProcess`. However, in contrast to the a.e. martingale convergence
theorem, we do not need to introduce an L¹ version of `Filtration.limitProcess` as the L¹ limit
and the a.e. limit of a submartingale coincide.

-/


/-- Part a of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
strongly adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
/-
**MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Submartingale f ℱ μ →     MeasureTheory.UniformIntegrable
 f 1 μ →       Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - MeasureTheo
ry.Filtration.limitProcess f ℱ μ) 1 μ)         Filter.atTop (nhds 0)
参数：fun n => MeasureTheory.eLpNorm (f n - MeasureTheory.Filtration.limitProcess f
 ℱ μ) 1 μ；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Submartingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Ty
pe u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : Measu
reTheory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`：tendsto_Lp_finite_o
f_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall
 n, AEStronglyMeasurable (f n) μ) (hg : M…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd`：memLp_limitP
rocess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGro
up F] {ℱ : Filtration Nat m} {f : Nat -> Ω -> F}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_ae`：tendstoInMeasure_of_tendst
o_ae [IsFiniteMeasure μ] (hf : forall n, AEStronglyMeasurable (f n) μ) (hfg : fo
rallᵐ x ∂μ, Tendsto (fun n => f n …
· 使用定理 `MeasureTheory.Submartingale.ae_tendsto_limitProcess`：∀ {Ω : Type u_1} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […

--- 原说明 ---
Part a of the **L¹ martingale convergence theorem**: a uniformly integrable subm
artingale
strongly adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable
 function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`.
-/
theorem Submartingale.tendsto_eLpNorm_one_limitProcess (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hunif.2.2
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hf.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_limitProcess_of_eLpNorm_bdd hmeas hR) hunif.2.1
    (tendstoInMeasure_of_tendsto_ae hmeas <| hf.ae_tendsto_limitProcess hR)
/-
**MeasureTheory.Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Submartingale f ℱ μ →     MeasureTheory.UniformIntegrable
 f 1 μ →       ∀ᵐ (ω : Ω) ∂μ, Filter.Tendsto (fun n => f n ω) Filter.atTop (nhds
 (MeasureTheory.Filtration.limitProcess f ℱ μ ω))
参数：ω : Ω；fun n => f n ω；nhds (MeasureTheory.Filtration.limitProcess f ℱ μ ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Submartingale.ae_tendsto_limitProcess`：∀ {Ω : Type u_1} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} {R : NNReal} […
-/
theorem Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  let ⟨_, hR⟩ := hunif.2.2
  hf.ae_tendsto_limitProcess hR

/-- If a martingale `f` strongly adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is
almost everywhere equal to `𝔼[g | ℱ n]`. -/
/-
**MeasureTheory.Martingale.eq_condExp_of_tendsto_eLpNorm** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ℕ 
m0} {f : ℕ → Ω → ℝ} {g : Ω → ℝ}   {μ : MeasureTheory.Measure Ω},   MeasureTheory
.Martingale f ℱ μ →     MeasureTheory.Integrable g μ →       Filter.Tendsto (fun
 n => MeasureTheory.eLpNorm (f n - g) 1 μ) Filter.atTop (nhds 0) →         ∀ (n 
: ℕ), f n =ᵐ[μ] μ[g | ↑ℱ n]
参数：fun n => MeasureTheory.eLpNorm (f n - g) 1 μ；nhds 0；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_iff`：eLpNorm_eq_zero_iff {f : α -> ε} (hf 
: AEStronglyMeasurable f μ) (h0 : p != 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.Martingale.stronglyMeasurable`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.eLpNorm_condExp_le_eLpNorm`：eLpNorm_condExp_le_eLpNorm (f 
: α -> E) {p : Real>=0∞} (hp : 1 <= p) : eLpNorm (μ[f | m]) p μ <= eLpNorm f p μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.condExp_sub`：condExp_sub (hf : Integrable f μ) (hg : Integ
rable g μ) (m : MeasurableSpace α) : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m]
· 使用定理 `MeasureTheory.Martingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} {ι 
: Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Me
asure Ω} [inst_1 : Normed…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If a martingale `f` strongly adapted to `ℱ` converges in L¹ to `g`, then for all
 `n`, `f n` is
almost everywhere equal to `𝔼[g | ℱ n]`.
-/
theorem Martingale.eq_condExp_of_tendsto_eLpNorm {μ : Measure Ω} (hf : Martingale f ℱ μ)
    (hg : Integrable g μ) (hgtends : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) (n : ℕ) :
    f n =ᵐ[μ] μ[g | ℱ n] := by
  rw [← sub_ae_eq_zero, ← eLpNorm_eq_zero_iff (((hf.stronglyMeasurable n).mono (ℱ.le _)).sub
    (stronglyMeasurable_condExp.mono (ℱ.le _))).aestronglyMeasurable one_ne_zero]
  have ht : Tendsto (fun m => eLpNorm (μ[f m - g | ℱ n]) 1 μ) atTop (𝓝 0) :=
    haveI hint : ∀ m, Integrable (f m - g) μ := fun m => (hf.integrable m).sub hg
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (fun m => zero_le)
      fun m => eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hev : ∀ m ≥ n, eLpNorm (μ[f m - g | ℱ n]) 1 μ = eLpNorm (f n - μ[g | ℱ n]) 1 μ := by
    refine fun m hm => eLpNorm_congr_ae ((condExp_sub (hf.integrable m) hg _).trans ?_)
    filter_upwards [hf.2 n m hm] with x hx
    simp only [hx, Pi.sub_apply]
  exact tendsto_nhds_unique (tendsto_atTop_of_eventually_const hev) ht

/-- Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integrable martingale
strongly adapted to the filtration `ℱ`, then for all `n`, `f n` is almost everywhere equal to the
conditional expectation of its limiting process w.r.t. `ℱ n`. -/
/-
**MeasureTheory.Martingale.ae_eq_condExp_limitProcess** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Martingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Martingale f ℱ μ →     MeasureTheory.UniformIntegrable f 
1 μ → ∀ (n : ℕ), f n =ᵐ[μ] μ[MeasureTheory.Filtration.limitProcess f ℱ μ | ↑ℱ n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Martingale.eq_condExp_of_tendsto_eLpNorm`：∀ {Ω : Type u_1}
 {m0 : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ℕ m0} {f : ℕ → Ω → ℝ} {g
 : Ω → ℝ}   {μ : MeasureTheory.Measure Ω},  …
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd`：memLp_limitP
rocess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGro
up F] {ℱ : Filtration Nat m} {f : Nat -> Ω -> F}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess`：∀ {Ω : Typ
e u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory
.Filtration ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory…
· 使用定理 `MeasureTheory.Martingale.submartingale`：submartingale [Preorder E] (hf :
 Martingale f ℱ μ) : Submartingale f ℱ μ

--- 原说明 ---
Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integ
rable martingale
strongly adapted to the filtration `ℱ`, then for all `n`, `f n` is almost everyw
here equal to the
conditional expectation of its limiting process w.r.t. `ℱ n`.
-/
theorem Martingale.ae_eq_condExp_limitProcess (hf : Martingale f ℱ μ)
    (hbdd : UniformIntegrable f 1 μ) (n : ℕ) : f n =ᵐ[μ] μ[ℱ.limitProcess f μ | ℱ n] :=
  let ⟨_, hR⟩ := hbdd.2.2
  hf.eq_condExp_of_tendsto_eLpNorm ((memLp_limitProcess_of_eLpNorm_bdd hbdd.1 hR).integrable le_rfl)
    (hf.submartingale.tendsto_eLpNorm_one_limitProcess hbdd) n

/-- Part c of the **L¹ martingale convergence theorem**: Given an integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges almost everywhere to `g`.

This martingale also converges to `g` in L¹ and this result is provided by
`MeasureTheory.Integrable.tendsto_eLpNorm_condExp` -/
/-
**MeasureTheory.Integrable.tendsto_ae_condExp** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Integrable`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.IsFiniteMeasure μ] {g : Ω → ℝ
},   MeasureTheory.Integrable g μ →     MeasureTheory.StronglyMeasurable g →    
   ∀ᵐ (x : Ω) ∂μ, Filter.Tendsto (fun n => μ[g | ↑ℱ n] x) Filter.atTop (nhds (g 
x))
参数：x : Ω；fun n => μ[g | ↑ℱ n] x；nhds (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.Integrable.uniformIntegrable_condExp_filtration`：∀ {Ω : Ty
pe u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {μ : MeasureT
heory.Measure Ω}   [MeasureTheory.IsFiniteMeasure μ…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd`：memLp_limitP
rocess_of_eLpNorm_bdd {R : Real>=0} {p : Real>=0∞} {F : Type*} [NormedAddCommGro
up F] {ℱ : Filtration Nat m} {f : Nat -> Ω -> F}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_condExp`：setIntegral_condExp (hm : m <= m₀) [S
igmaFinite (μ.trim hm)] (hf : Integrable f μ) (hs : MeasurableSet[m] s) : ∫ x in
 s, (μ[f | m]) x ∂μ = ∫…
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Martingale.ae_eq_condExp_limitProcess`：∀ {Ω : Type u_1} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtrati
on ℕ m0}   {f : ℕ → Ω → ℝ} [MeasureTheory…
· 使用定理 `MeasureTheory.martingale_condExp`：martingale_condExp [CompleteSpace E] (
f : Ω -> E) (ℱ : Filtration ι m0) (μ : Measure Ω) [SigmaFiniteFiltration μ ℱ] : 
Martingale (fun i => μ…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`：ae_eq_of_f
orall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)] {f
 g : α -> F'} (hf_int_finite : forall s, Measurabl…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `isPiSystem_iUnion_of_monotone`：isPiSystem_iUnion_of_monotone {α ι} [Semi
latticeSup ι] (p : ι -> Set (Set α)) (hp_pi : forall n, IsPiSystem (p n)) (hp_mo
no : Monotone p) : …
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `MeasurableSpace.measurableSpace_iSup_eq`：measurableSpace_iSup_eq (m : ι 
-> MeasurableSpace α) : ⨆ n, m n = generateFrom { s | exists n, MeasurableSet[m 
n] s }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Part c of the **L¹ martingale convergence theorem**: Given an integrable functio
n `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martinga
le defined by
`𝔼[g | ℱ n]` converges almost everywhere to `g`.

This martingale also converges to `g` in L¹ and this result is provided by
`MeasureTheory.Integrable.tendsto_eLpNorm_condExp`
-/
theorem Integrable.tendsto_ae_condExp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 (g x)) := by
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hunif : UniformIntegrable (fun n => μ[g | ℱ n]) 1 μ :=
    hg.uniformIntegrable_condExp_filtration
  obtain ⟨R, hR⟩ := hunif.2.2
  have hlimint : Integrable (ℱ.limitProcess (fun n => μ[g | ℱ n]) μ) μ :=
    (memLp_limitProcess_of_eLpNorm_bdd hunif.1 hR).integrable le_rfl
  suffices g =ᵐ[μ] ℱ.limitProcess (fun n x => (μ[g | ℱ n]) x) μ by
    filter_upwards [this, (martingale_condExp g ℱ μ).submartingale.ae_tendsto_limitProcess hR] with
      x heq ht
    rwa [heq]
  have : ∀ n s, MeasurableSet[ℱ n] s →
      ∫ x in s, g x ∂μ = ∫ x in s, ℱ.limitProcess (fun n x => (μ[g | ℱ n]) x) μ x ∂μ := by
    intro n s hs
    rw [← setIntegral_condExp (ℱ.le n) hg hs, ← setIntegral_condExp (ℱ.le n) hlimint hs]
    refine setIntegral_congr_ae (ℱ.le _ _ hs) ?_
    filter_upwards [(martingale_condExp g ℱ μ).ae_eq_condExp_limitProcess hunif n] with x hx _
    rw [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hle (fun s _ _ => hg.integrableOn)
    (fun s _ _ => hlimint.integrableOn) (fun s hs _ => ?_) hgmeas.aestronglyMeasurable
    stronglyMeasurable_limitProcess.aestronglyMeasurable
  have hpi : IsPiSystem {s | ∃ n, MeasurableSet[ℱ n] s} := by
    rw [Set.ofPred_exists]
    exact isPiSystem_iUnion_of_monotone _ (fun n ↦ (ℱ n).isPiSystem_measurableSet) fun _ _ ↦ ℱ.mono
  induction s, hs
    using MeasurableSpace.induction_on_inter (MeasurableSpace.measurableSpace_iSup_eq ℱ) hpi with
  | empty =>
    simp only [Measure.restrict_empty, integral_zero_measure]
  | basic s hs =>
    rcases hs with ⟨n, hn⟩
    exact this n _ hn
  | compl t htmeas ht =>
    have hgeq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas (hg.trim hle hgmeas)
    have hheq := @setIntegral_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ htmeas
      (hlimint.trim hle stronglyMeasurable_limitProcess)
    rw [setIntegral_trim hle hgmeas htmeas.compl,
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas.compl, hgeq, hheq, ←
      setIntegral_trim hle hgmeas htmeas, ←
      setIntegral_trim hle stronglyMeasurable_limitProcess htmeas, ← integral_trim hle hgmeas, ←
      integral_trim hle stronglyMeasurable_limitProcess, ← setIntegral_univ,
      this 0 _ MeasurableSet.univ, setIntegral_univ, ht (measure_lt_top _ _)]
  | iUnion f hf hfmeas heq =>
    rw [integral_iUnion (fun n => hle _ (hfmeas n)) hf hg.integrableOn,
      integral_iUnion (fun n => hle _ (hfmeas n)) hf hlimint.integrableOn]
    exact tsum_congr fun n => heq _ (measure_lt_top _ _)

/-- Part c of the **L¹ martingale convergence theorem**: Given an integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges in L¹ to `g`.

This martingale also converges to `g` almost everywhere and this result is provided by
`MeasureTheory.Integrable.tendsto_ae_condExp` -/
/-
**MeasureTheory.Integrable.tendsto_eLpNorm_condExp** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Integrable`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ
 : MeasureTheory.Filtration ℕ m0}   [MeasureTheory.IsFiniteMeasure μ] {g : Ω → ℝ
},   MeasureTheory.Integrable g μ →     MeasureTheory.StronglyMeasurable g →    
   Filter.Tendsto (fun n => MeasureTheory.eLpNorm (μ[g | ↑ℱ n] - g) 1 μ) Filter.
atTop (nhds 0)
参数：fun n => MeasureTheory.eLpNorm (μ[g | ↑ℱ n] - g) 1 μ；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`：tendsto_Lp_finite_o
f_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall
 n, AEStronglyMeasurable (f n) μ) (hg : M…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.uniformIntegrable_condExp_filtration`：∀ {Ω : Ty
pe u_1} {ι : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] {μ : MeasureT
heory.Measure Ω}   [MeasureTheory.IsFiniteMeasure μ…
· 使用定理 `MeasureTheory.tendstoInMeasure_of_tendsto_ae`：tendstoInMeasure_of_tendst
o_ae [IsFiniteMeasure μ] (hf : forall n, AEStronglyMeasurable (f n) μ) (hfg : fo
rallᵐ x ∂μ, Tendsto (fun n => f n …
· 使用定理 `MeasureTheory.Integrable.tendsto_ae_condExp`：∀ {Ω : Type u_1} {m0 : Meas
urableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℕ m0}
   [MeasureTheory.IsFiniteMeasure…

--- 原说明 ---
Part c of the **L¹ martingale convergence theorem**: Given an integrable functio
n `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martinga
le defined by
`𝔼[g | ℱ n]` converges in L¹ to `g`.

This martingale also converges to `g` almost everywhere and this result is provi
ded by
`MeasureTheory.Integrable.tendsto_ae_condExp`
-/
theorem Integrable.tendsto_eLpNorm_condExp (hg : Integrable g μ)
    (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - g) 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
    (memLp_one_iff_integrable.2 hg) hg.uniformIntegrable_condExp_filtration.2.1
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (stronglyMeasurable_condExp.mono (ℱ.le n)).aestronglyMeasurable)
      (hg.tendsto_ae_condExp hgmeas))

/-- **Lévy's upward theorem**, almost everywhere version: given a function `g` and a filtration
`ℱ`, the sequence defined by `𝔼[g | ℱ n]` converges almost everywhere to `𝔼[g | ⨆ n, ℱ n]`. -/
/-
**MeasureTheory.tendsto_ae_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_ae_condExp (g : Ω -> Real) : forallᵐ x ∂μ, Tendsto (fun n => (μ[g 
| ℱ n]) x) atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) x))
参数：g : Ω -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.tendsto_ae_condExp`：∀ {Ω : Type u_1} {m0 : Meas
urableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℕ m0}
   [MeasureTheory.IsFiniteMeasure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.condExp_condExp_of_le`：condExp_condExp_of_le {m₁ m₂ m₀ : M
easurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinit
e (μ.trim hm₂)] : μ[μ[f |…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…

--- 原说明 ---
**Lévy's upward theorem**, almost everywhere version: given a function `g` and a
 filtration
`ℱ`, the sequence defined by `𝔼[g | ℱ n]` converges almost everywhere to `𝔼[g | 
⨆ n, ℱ n]`.
-/
theorem tendsto_ae_condExp (g : Ω → ℝ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g | ℱ n]) x) atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) x)) := by
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[μ[g | ⨆ n, ℱ n] | ℱ n]) x)
      atTop (𝓝 ((μ[g | ⨆ n, ℱ n]) x)) :=
    integrable_condExp.tendsto_ae_condExp stronglyMeasurable_condExp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g | ⨆ n, ℱ n] | ℱ n]) x = (μ[g | ℱ n]) x := fun n =>
    condExp_condExp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  rw [← ae_all_iff] at heq
  filter_upwards [heq, ht] with x hxeq hxt
  exact hxt.congr hxeq

/-- **Lévy's upward theorem**, L¹ version: given a function `g` and a filtration `ℱ`, the
sequence defined by `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`. -/
/-
**MeasureTheory.tendsto_eLpNorm_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：tendsto_eLpNorm_condExp (g : Ω -> Real) : Tendsto (fun n => eLpNorm (μ[g |
 ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop (𝓝 0)
参数：g : Ω -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`：∀ {Ω : Type u_1} {m0 :
 MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration 
ℕ m0}   [MeasureTheory.IsFiniteMeasure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_condExp_of_le`：condExp_condExp_of_le {m₁ m₂ m₀ : M
easurableSpace α} {μ : Measure α} (hm₁₂ : m₁ <= m₂) (hm₂ : m₂ <= m₀) [SigmaFinit
e (μ.trim hm₂)] : μ[μ[f |…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Lévy's upward theorem**, L¹ version: given a function `g` and a filtration `ℱ`
, the
sequence defined by `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`.
-/
theorem tendsto_eLpNorm_condExp (g : Ω → ℝ) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => eLpNorm (μ[μ[g | ⨆ n, ℱ n] | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ)
      atTop (𝓝 0) :=
    integrable_condExp.tendsto_eLpNorm_condExp stronglyMeasurable_condExp
  have heq : ∀ n, ∀ᵐ x ∂μ, (μ[μ[g | ⨆ n, ℱ n] | ℱ n]) x = (μ[g | ℱ n]) x := fun n =>
    condExp_condExp_of_le (le_iSup _ n) (iSup_le fun n => ℱ.le n)
  refine ht.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [heq n] with x hxeq
  simp only [hxeq, Pi.sub_apply]

end L1Convergence

end MeasureTheory

