/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane.  Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

@[expose] public section

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {a : WithTop E}

variable (f a) in
/--
The Characteristic Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the characteristic function of `f`
is defined as the sum of two terms: the proximity function, which quantifies how close `f` gets to
`a` on the circle `∣z∣ = r`, and the logarithmic counting function, which counts the number times
that `f` attains the value `a` inside the disk `∣z∣ ≤ r`, weighted by multiplicity.
-/
/-
**ValueDistribution.characteristic** 是 Mathlib 中的一个定义，位于命名空间 `ValueDistribution`
。
形式化陈述：characteristic : Real -> Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ

--- 原说明 ---
The Characteristic Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the characterist
ic function of `f`
is defined as the sum of two terms: the proximity function, which quantifies how
 close `f` gets to
`a` on the circle `∣z∣ = r`, and the logarithmic counting function, which counts
 the number times
that `f` attains the value `a` inside the disk `∣z∣ ≤ r`, weighted by multiplici
ty.
-/
noncomputable def characteristic : ℝ → ℝ := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

/--
If two functions differ only on a discrete set, then their characteristic functions agree, except
perhaps at radius 0.
-/
/-
**ValueDistribution.characteristic_congr_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 `V
alueDistribution`。
形式化陈述：characteristic_congr_codiscrete {r : Real} (hfg : f =ᶠ[codiscrete Complex]
 g) (hr : r != 0) : characteristic f a r = characteristic g a r
参数：hfg : f =ᶠ[codiscrete Complex] g；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ValueDistribution.logCounting_congr_codiscrete`：logCounting_congr_codisc
rete [NormedSpace Complex E] {f g : Complex -> E} (hfg : f =ᶠ[codiscrete Complex
] g) : logCounting f = logCounting g
· 使用引理 `ValueDistribution.proximity_congr_codiscrete`：proximity_congr_codiscrete
 {f g : Complex -> E} {a : WithTop E} {r : Real} (hfg : f =ᶠ[codiscrete Complex]
 g) (hr : r != 0) : proximity f a …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two functions differ only on a discrete set, then their characteristic functi
ons agree, except
perhaps at radius 0.
-/
theorem characteristic_congr_codiscrete {r : ℝ} (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    characteristic f a r = characteristic g a r := by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

/--
The difference between the characteristic functions for the poles of `f` and `f - const` simplifies
to the difference between the proximity functions.
-/
@[simp]
/-
**ValueDistribution.characteristic_sub_characteristic_eq_proximity_sub_proximity
** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorp
hic f) (a₀ : E) : characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f
 ⊤ - proximity (f · - a₀) ⊤
参数：h : Meromorphic f；a₀ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `ValueDistribution.logCounting_sub_const`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {E : Type u_2}   [inst_2 : NormedA
ddCommGroup E] [inst_3 : Norm…
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The difference between the characteristic functions for the poles of `f` and `f 
- const` simplifies
to the difference between the proximity functions.
-/
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorphic f) (a₀ : E) :
    characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f ⊤ - proximity (f · - a₀) ⊤ := by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

/--
The characteristic function is even.
-/
/-
**ValueDistribution.characteristic_even** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribu
tion`。
形式化陈述：characteristic_even : (characteristic f a).Even
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Even.add`：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] [inst_
1 : Add β] {f g : α → β},   Function.Even f → Function.Even g → Function.Even (f
 + g)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `ValueDistribution.proximity_even`：proximity_even : (proximity f a).Even
· 使用定理 `ValueDistribution.logCounting_even`：logCounting_even {f : 𝕜 -> E} {e : W
ithTop E} : (logCounting f e).Even

--- 原说明 ---
The characteristic function is even.
-/
theorem characteristic_even :
    (characteristic f a).Even := proximity_even.add logCounting_even

/--
For `1 ≤ r`, the characteristic function is non-negative.
-/
/-
**ValueDistribution.characteristic_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistri
bution`。
形式化陈述：characteristic_nonneg {r : Real} (hr : 1 <= r) : 0 <= characteristic f a r
参数：hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `ValueDistribution.proximity_nonneg`：proximity_nonneg {a : WithTop E} : 0
 <= proximity f a
· 使用定理 `ValueDistribution.logCounting_nonneg`：logCounting_nonneg {r : Real} {f :
 𝕜 -> E} {e : WithTop E} (hr : 1 <= r) : 0 <= logCounting f e r

--- 原说明 ---
For `1 ≤ r`, the characteristic function is non-negative.
-/
theorem characteristic_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ characteristic f a r :=
  add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

/--
The characteristic function is asymptotically non-negative.
-/
/-
**ValueDistribution.characteristic_eventually_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
ValueDistribution`。
形式化陈述：characteristic_eventually_nonneg : 0 <=ᶠ[Filter.atTop] characteristic f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ValueDistribution.characteristic_nonneg`：characteristic_nonneg {r : Real
} (hr : 1 <= r) : 0 <= characteristic f a r

--- 原说明 ---
The characteristic function is asymptotically non-negative.
-/
theorem characteristic_eventually_nonneg :
    0 ≤ᶠ[Filter.atTop] characteristic f a := by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr ↦ by simp [characteristic_nonneg hr]

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the sum
of the characteristic functions of `f ·`, plus `log s.card`.
-/
/-
**ValueDistribution.characteristic_sum_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDi
stribution`。
形式化陈述：characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α -> Complex -> 
E) {r : Real} (hf : forall a in s, Meromorphic (f a)) (hr : 1 <= r) : characteri
stic (∑ a in s, f a) ⊤ r <= (∑ a in s, (characteristic (f a) ⊤)) r + log s.card
参数：s : Finset α；f : α -> Complex -> E；hf : forall a in s, Meromorphic (f a)；hr :
 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ValueDistribution.proximity_sum_top_le`：proximity_sum_top_le [NormedSpac
e Complex E] {α : Type*} (s : Finset α) (f : α -> Complex -> E) (hf : forall a i
n s, Meromorphic (f a)) : pr…
· 使用定理 `ValueDistribution.logCounting_sum_top_le`：logCounting_sum_top_le {α : Ty
pe*} (s : Finset α) (f : α -> 𝕜 -> E) {r : Real} (h₁f : forall a in s, Meromorph
ic (f a)) (hr : 1 <= r) : logC…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than
 or equal to the sum
of the characteristic functions of `f ·`, plus `log s.card`.
-/
theorem characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E) {r : ℝ}
    (hf : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    characteristic (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (characteristic (f a) ⊤)) r + log s.card := by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a ∈ s, f a) ⊤ r + logCounting (∑ a ∈ s, f a) ⊤ r
  _ ≤ ((∑ a ∈ s, proximity (f a) ⊤) r) + log s.card + (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · apply logCounting_sum_top_le s f hf hr
    _ = ((∑ a ∈ s, proximity (f a) ⊤) r) + (∑ a ∈ s, (logCounting (f a) ⊤)) r + log s.card := by
      ring
    _ = ∑ x ∈ s, (proximity (f x) ⊤ r + logCounting (f x) ⊤ r) + log s.card := by
      simp [Finset.sum_add_distrib]

/--
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the
sum of the characteristic functions of `f ·`.
-/
/-
**ValueDistribution.characteristic_sum_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空
间 `ValueDistribution`。
形式化陈述：characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α -> C
omplex -> E) (hf : forall a in s, Meromorphic (f a)) : characteristic (∑ a in s,
 f a) ⊤ <=ᶠ[Filter.atTop] ∑ a in s, (characteristic (f a) ⊤) + fun _ => log s.ca
rd
参数：s : Finset α；f : α -> Complex -> E；hf : forall a in s, Meromorphic (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.characteristic_sum_top_le`：characteristic_sum_top_le {
α : Type*} (s : Finset α) (f : α -> Complex -> E) {r : Real} (hf : forall a in s
, Meromorphic (f a)) (hr : 1 <= r…

--- 原说明 ---
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less t
han or equal to the
sum of the characteristic functions of `f ·`.
-/
theorem characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, Meromorphic (f a)) :
    characteristic (∑ a ∈ s, f a) ⊤
      ≤ᶠ[Filter.atTop] ∑ a ∈ s, (characteristic (f a) ⊤) + fun _ ↦ log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_sum_top_le s f hf hr

/--
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of the
characteristic functions of `f` and `g`, respectively, plus `log 2` (where `2` is the number of
summands).
-/
/-
**ValueDistribution.characteristic_add_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDi
stribution`。
形式化陈述：characteristic_add_top_le {f₁ f₂ : Complex -> E} {r : Real} (h₁f₁ : Meromo
rphic f₁) (h₁f₂ : Meromorphic f₂) (hr : 1 <= r) : characteristic (f₁ + f₂) ⊤ r <
= characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂；hr : 1 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `ValueDistribution.characteristic_sum_top_le`：characteristic_sum_top_le {
α : Type*} (s : Finset α) (f : α -> Complex -> E) {r : Real} (hf : forall a in s
, Meromorphic (f a)) (hr : 1 <= r…

--- 原说明 ---
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal
 to the sum of the
characteristic functions of `f` and `g`, respectively, plus `log 2` (where `2` i
s the number of
summands).
-/
theorem characteristic_add_top_le {f₁ f₂ : ℂ → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    characteristic (f₁ + f₂) ⊤ r ≤ characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2 := by
  have h_meromorphic : ∀ a ∈ Finset.univ, Meromorphic (![f₁, f₂] a) := by
    simpa using ⟨h₁f₁, h₁f₂⟩
  simpa using characteristic_sum_top_le Finset.univ ![f₁, f₂] h_meromorphic hr

/--
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of
the characteristic functions of `f` and `g`, respectively.
-/
/-
**ValueDistribution.characteristic_add_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空
间 `ValueDistribution`。
形式化陈述：characteristic_add_top_eventuallyLE {f₁ f₂ : Complex -> E} (h₁f₁ : Meromor
phic f₁) (h₁f₂ : Meromorphic f₂) : characteristic (f₁ + f₂) ⊤ <=ᶠ[Filter.atTop] 
characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ => log 2
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.characteristic_add_top_le`：characteristic_add_top_le {
f₁ f₂ : Complex -> E} {r : Real} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂)
 (hr : 1 <= r) : characteristic (…

--- 原说明 ---
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or eq
ual to the sum of
the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_add_top_eventuallyLE {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤
      ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ ↦ log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the characteristic function for the zeros of `f * g` is less than or equal to the sum
of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
/-
**ValueDistribution.characteristic_mul_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueD
istribution`。
形式化陈述：characteristic_mul_zero_le {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1
 <= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (
h₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : charact
eristic (f₁ * f₂) 0 r <= (characteristic f₁ 0 + characteristic f₂ 0) r
参数：hr : 1 <= r；h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z !=
 ⊤；h₁f₂ : Meromorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ValueDistribution.proximity_mul_zero_le`：proximity_mul_zero_le {f₁ f₂ : 
Complex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) : proximity 
(f₁ * f₂) 0 <= (proximity f₁ …
· 使用定理 `ValueDistribution.logCounting_mul_zero_le`：logCounting_mul_zero_le {f₁ f
₂ : 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, m
eromorphicOrderAt f₁ z != ⊤) (h…

--- 原说明 ---
For `1 ≤ r`, the characteristic function for the zeros of `f * g` is less than o
r equal to the sum
of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 r ≤ (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function for the zeros of `f * g` is less than or equal to the
sum of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
/-
**ValueDistribution.characteristic_mul_zero_eventuallyLE** 是 Mathlib 中的一个定理，位于命名
空间 `ValueDistribution`。
形式化陈述：characteristic_mul_zero_eventuallyLE {f₁ f₂ : Complex -> Complex} (h₁f₁ : 
Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorp
hic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : characteristic (f₁ * f
₂) 0 <=ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0
参数：h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤；h₁f₂ : Me
romorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.characteristic_mul_zero_le`：characteristic_mul_zero_le
 {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (
h₂f₁ : forall z, meromorphicOrderA…

--- 原说明 ---
Asymptotically, the characteristic function for the zeros of `f * g` is less tha
n or equal to the
sum of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the characteristic function for the poles of `f * g` is less than or equal to the sum
of the characteristic functions for the poles of `f` and `g`, respectively.
-/
/-
**ValueDistribution.characteristic_mul_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDi
stribution`。
形式化陈述：characteristic_mul_top_le {f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 
<= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h
₁f₂ : Meromorphic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : characte
ristic (f₁ * f₂) ⊤ r <= (characteristic f₁ ⊤ + characteristic f₂ ⊤) r
参数：hr : 1 <= r；h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z !=
 ⊤；h₁f₂ : Meromorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ValueDistribution.proximity_mul_top_le`：proximity_mul_top_le {f₁ f₂ : Co
mplex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) : proximity (f
₁ * f₂) ⊤ <= proximity f₁ ⊤ …
· 使用定理 `ValueDistribution.logCounting_mul_top_le`：logCounting_mul_top_le {f₁ f₂ 
: 𝕜 -> 𝕜} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (h₂f₁ : forall z, mer
omorphicOrderAt f₁ z != ⊤) (h₁…

--- 原说明 ---
For `1 ≤ r`, the characteristic function for the poles of `f * g` is less than o
r equal to the sum
of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ r ≤ (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function for the poles of `f * g` is less than or equal to the
sum of the characteristic functions for the poles of `f` and `g`, respectively.
-/
/-
**ValueDistribution.characteristic_mul_top_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空
间 `ValueDistribution`。
形式化陈述：characteristic_mul_top_eventuallyLE {f₁ f₂ : Complex -> Complex} (h₁f₁ : M
eromorphic f₁) (h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤) (h₁f₂ : Meromorph
ic f₂) (h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤) : characteristic (f₁ * f₂
) ⊤ <=ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤
参数：h₁f₁ : Meromorphic f₁；h₂f₁ : forall z, meromorphicOrderAt f₁ z != ⊤；h₁f₂ : Me
romorphic f₂；h₂f₂ : forall z, meromorphicOrderAt f₂ z != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ValueDistribution.characteristic_mul_top_le`：characteristic_mul_top_le {
f₁ f₂ : Complex -> Complex} {r : Real} (hr : 1 <= r) (h₁f₁ : Meromorphic f₁) (h₂
f₁ : forall z, meromorphicOrderAt…

--- 原说明 ---
Asymptotically, the characteristic function for the poles of `f * g` is less tha
n or equal to the
sum of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` equals `n` times the
characteristic counting function for the zeros of `f`.
-/
@[simp]
/-
**ValueDistribution.characteristic_pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDist
ribution`。
形式化陈述：characteristic_pow_zero {f : Complex -> Complex} {n : Nat} (hf : Meromorph
ic f) : characteristic (f ^ n) 0 = n • characteristic f 0
参数：hf : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValueDistribution.proximity_pow_zero`：∀ {f : ℂ → ℂ} {n : ℕ}, ValueDistri
bution.proximity (f ^ n) 0 = n • ValueDistribution.proximity f 0
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ValueDistribution.logCounting_pow_zero`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {f : 𝕜 → 𝕜} {n : ℕ},   Meromorphic 
f → ValueDistribution.logCou…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` eq
uals `n` times the
characteristic counting function for the zeros of `f`.
-/
theorem characteristic_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) 0 = n • characteristic f 0 := by
  simp_all [characteristic]

/--
For natural numbers `n`, the characteristic function for the poles of `f ^ n` equals `n` times the
characteristic function for the poles of `f`.
-/
@[simp]
/-
**ValueDistribution.characteristic_pow_top** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistr
ibution`。
形式化陈述：characteristic_pow_top {f : Complex -> Complex} {n : Nat} (hf : Meromorphi
c f) : characteristic (f ^ n) ⊤ = n • characteristic f ⊤
参数：hf : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValueDistribution.proximity_pow_top`：∀ {f : ℂ → ℂ} {n : ℕ}, ValueDistrib
ution.proximity (f ^ n) ⊤ = n • ValueDistribution.proximity f ⊤
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ValueDistribution.logCounting_pow_top`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : ProperSpace 𝕜] {f : 𝕜 → 𝕜} {n : ℕ},   Meromorphic f
 → ValueDistribution.logCou…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For natural numbers `n`, the characteristic function for the poles of `f ^ n` eq
uals `n` times the
characteristic function for the poles of `f`.
-/
theorem characteristic_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) ⊤ = n • characteristic f ⊤ := by
  simp_all [characteristic]

end ValueDistribution

