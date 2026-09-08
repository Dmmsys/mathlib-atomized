/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Euler Products

The main result in this file is `EulerProduct.eulerProduct_hasProd`, which says that
if `f : ℕ → R` is norm-summable, where `R` is a complete normed commutative ring and `f` is
multiplicative on coprime arguments with `f 0 = 0`, then
`∏' p : Primes, ∑' e : ℕ, f (p^e)` converges to `∑' n, f n`.

`ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd` is a version
for multiplicative arithmetic functions in the sense of
`ArithmeticFunction.IsMultiplicative`.

There is also a version `EulerProduct.eulerProduct_completely_multiplicative_hasProd`,
which states that `∏' p : Primes, (1 - f p)⁻¹` converges to `∑' n, f n`
when `f` is completely multiplicative with values in a complete normed field `F`
(implemented as `f : ℕ →*₀ F`).

There are variants stating the equality of the infinite product and the infinite sum
(`EulerProduct.eulerProduct_tprod`, `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod`,
`EulerProduct.eulerProduct_completely_multiplicative_tprod`) and also variants stating
the convergence of the sequence of partial products over primes `< n`
(`EulerProduct.eulerProduct`, `ArithmeticFunction.IsMultiplicative.eulerProduct`,
`EulerProduct.eulerProduct_completely_multiplicative`.)

An intermediate step is `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
(and its variant `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`),
which relates the finite product over primes `p ∈ s` to the sum of `f n` over `s`-factored `n`,
for `s : Finset ℕ`.

## Tags

Euler product, multiplicative function
-/

public section

/-- If `f` is multiplicative and summable, then its values at natural numbers `> 1`
have norm strictly less than `1`. -/
/-
**Summable.norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.norm_lt_one {F : Type*} [NormedDivisionRing F] [CompleteSpace F] 
{f : Nat ->* F} (hsum : Summable f) {p : Nat} (hp : 1 < p) : ‖f p‖ < 1
参数：hsum : Summable f；hp : 1 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_geometric_iff_norm_lt_one`：summable_geometric_iff_norm_lt_one :
 (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x

--- 原说明 ---
If `f` is multiplicative and summable, then its values at natural numbers `> 1`
have norm strictly less than `1`.
-/
lemma Summable.norm_lt_one {F : Type*} [NormedDivisionRing F] [CompleteSpace F] {f : ℕ →* F}
    (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_one.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp

open scoped Topology

open Nat Finset

section General

/-!
### General Euler Products

In this section we consider multiplicative (on coprime arguments) functions `f : ℕ → R`,
where `R` is a complete normed commutative ring. The main result is `EulerProduct.eulerProduct`.
-/

variable {R : Type*} [NormedCommRing R] {f : ℕ → R}

-- local instance to speed up typeclass search
/-
**instT0Space** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[local instance] private lemma instT0Space : T0Space R := MetricSpace.instT0Space

variable [CompleteSpace R]

namespace EulerProduct

variable (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

include hf₁ hmul in
/-- We relate a finite product over primes in `s` to an infinite sum over `s`-factored numbers. -/
/-
**EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum** 是 Ma
thlib 中的一个引理，位于命名空间 `EulerProduct`。
形式化陈述：summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum (hsum : forall 
{p : Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (s : Finset Nat) : 
Summable (fun m : factoredNumbers s => ‖f m‖) ∧ HasSum (fun m : factoredNumbers 
s => f m) (∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n))
参数：hsum : forall {p : Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)；s :
 Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.factoredNumbers_empty`：factoredNumbers_empty : factoredNumbers ∅ = {
1}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.Finite.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {s : Set β},   s.Finite → ∀ (f : β → α), Sum
mable (f …
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `hasSum_singleton`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] (m : β) (f : β → α),   HasSum ({m}.domRestrict 
f) (f …
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.factoredNumbers.map_prime_pow_mul`：∀ {F : Type u_1} [inst : Mul F] {
f : ℕ → F},   (∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n) →     ∀ {s : Fi
nset ℕ} {p : ℕ},       Nat.…
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `Summable.mul_of_nonneg`：Summable.mul_of_nonneg {f : ι -> Real} {g : ι' -
> Real} (hf : Summable f) (hg : Summable g) (hf' : 0 <= f) (hg' : 0 <= g) : Summ
able fun x :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
We relate a finite product over primes in `s` to an infinite sum over `s`-factor
ed numbers.
-/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m)
        (∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n)) := by
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [notMem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  | insert p s hp ih =>
    rw [filter_insert]
    split_ifs with hpp
    · constructor
      · simp only [← (equivProdNatFactoredNumbers hpp hp).summable_iff, Function.comp_def,
          equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_mul_le ..) ?_
        apply Summable.mul_of_nonneg (hsum hpp) ih.1 <;> exact fun n ↦ norm_nonneg _
      · have hp' : p ∉ {p ∈ s | p.Prime} := mt (mem_of_mem_filter p) hp
        rw [prod_insert hp', ← (equivProdNatFactoredNumbers hpp hp).hasSum_iff, Function.comp_def]
        conv =>
          enter [1, x]
          rw [equivProdNatFactoredNumbers_apply', factoredNumbers.map_prime_pow_mul hmul hpp hp]
        have : T3Space R := instT3Space -- speeds up the following
        apply (hsum hpp).of_norm.hasSum.mul ih.2
        -- `exact summable_mul_of_summable_norm (hsum hpp) ih.1` gives a time-out
        apply summable_mul_of_summable_norm (hsum hpp) ih.1
    · rwa [factoredNumbers_insert s hpp]

include hf₁ hmul in
/-- A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
in terms of the value of the series. -/
/-
**EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers** 是 Mathlib 中的一个引理
，位于命名空间 `EulerProduct`。
形式化陈述：prod_filter_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (
s : Finset Nat) : ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∑' m : factored
Numbers s, f m
参数：hsum : Summable (‖f ·‖)；s : Finset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
：summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum (hsum : forall {p : 
Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (s : …
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p

--- 原说明 ---
A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime
_tsum`
in terms of the value of the series.
-/
lemma prod_filter_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∑' m : factoredNumbers s, f m :=
  (summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- The following statement says that summing over `s`-factored numbers such that
`s` contains `primesBelow N` for large enough `N` gets us arbitrarily close to the sum
over all natural numbers (assuming `f` is summable and `f 0 = 0`; the latter since
`0` is not `s`-factored). -/
/-
**EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt** 是 Mathlib 中的一个引理，位于命名空间 `
EulerProduct`。
形式化陈述：norm_tsum_factoredNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) 
{ε : Real} (εpos : 0 < ε) : exists N : Nat, forall s : Finset Nat, primesBelow N
 <= s -> ‖(∑' m : Nat, f m) - ∑' m : factoredNumbers s, f m‖ < ε
参数：hsum : Summable f；hf₀ : f 0 = 0；εpos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_iff_nat_tsum_vanishing`：∀ {G : Type u_2} [inst : AddCommGroup G
] [inst_1 : UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G] {f : ℕ → G},
   Summable f ↔ ∀ e ∈…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Nat.factoredNumbers_compl`：factoredNumbers_compl {N : Nat} {s : Finset N
at} (h : primesBelow N <= s) : (factoredNumbers s)ᶜ \ {0} subseteq {n | N <= n}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_subtype_add_tsum_subtype_compl`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   
[CompleteSpace α] [T2Space α] {f :…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `tsum_eq_tsum_sdiff_singleton`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} (s : Set β) {b : β},   
f b = 0 → ∑' (a : …

--- 原说明 ---
The following statement says that summing over `s`-factored numbers such that
`s` contains `primesBelow N` for large enough `N` gets us arbitrarily close to t
he sum
over all natural numbers (assuming `f` is summable and `f 0 = 0`; the latter sin
ce
`0` is not `s`-factored).
-/
lemma norm_tsum_factoredNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : ℝ}
    (εpos : 0 < ε) :
    ∃ N : ℕ, ∀ s : Finset ℕ, primesBelow N ≤ s →
      ‖(∑' m : ℕ, f m) - ∑' m : factoredNumbers s, f m‖ < ε := by
  obtain ⟨N, hN⟩ :=
    summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) <| Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN
  refine ⟨N, fun s hs ↦ ?_⟩
  have := hN _ <| factoredNumbers_compl hs
  rwa [← hsum.tsum_subtype_add_tsum_subtype_compl (factoredNumbers s),
    add_sub_cancel_left, tsum_eq_tsum_sdiff_singleton (factoredNumbers s)ᶜ hf₀]

-- Versions of the three lemmas above for `smoothNumbers N`

include hf₁ hmul in
/-- We relate a finite product over primes to an infinite sum over smooth numbers. -/
/-
**EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum** 是 Mathl
ib 中的一个引理，位于命名空间 `EulerProduct`。
形式化陈述：summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (hsum : forall {p 
: Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (N : Nat) : Summable (
fun m : N.smoothNumbers => ‖f m‖) ∧ HasSum (fun m : N.smoothNumbers => f m) (∏ p
 in N.primesBelow, ∑' n : Nat, f (p ^ n))
参数：hsum : forall {p : Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)；N :
 Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Nat.primesBelow.eq_1`：∀ (n : ℕ), n.primesBelow = {p ∈ Finset.range n | N
at.Prime p}
· 使用引理 `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
：summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum (hsum : forall {p : 
Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (s : …

--- 原说明 ---
We relate a finite product over primes to an infinite sum over smooth numbers.
-/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n)) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁ hmul hsum _

include hf₁ hmul in
/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
in terms of the value of the series. -/
/-
**EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers** 是 Mathlib 中的一个引理，位于
命名空间 `EulerProduct`。
形式化陈述：prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N :
 Nat) : ∏ p in N.primesBelow, ∑' n : Nat, f (p ^ n) = ∑' m : N.smoothNumbers, f 
m
参数：hsum : Summable (‖f ·‖)；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`：su
mmable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (hsum : forall {p : Nat}, 
p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (N : Nat…
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p

--- 原说明 ---
A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_ts
um`
in terms of the value of the series.
-/
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N : ℕ) :
    ∏ p ∈ N.primesBelow, ∑' n : ℕ, f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- The following statement says that summing over `N`-smooth numbers
for large enough `N` gets us arbitrarily close to the sum over all natural numbers
(assuming `f` is norm-summable and `f 0 = 0`; the latter since `0` is not smooth). -/
/-
**EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt** 是 Mathlib 中的一个引理，位于命名空间 `Eu
lerProduct`。
形式化陈述：norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε
 : Real} (εpos : 0 < ε) : exists N₀ : Nat, forall N >= N₀, ‖(∑' m : Nat, f m) - 
∑' m : N.smoothNumbers, f m‖ < ε
参数：hsum : Summable f；hf₀ : f 0 = 0；εpos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用引理 `EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt`：norm_tsum_factoredNu
mbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : Real} (εpos : 0 < ε) 
: exists N : Nat, forall s : Finset Nat,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Nat.lt_of_mem_primesBelow`：lt_of_mem_primesBelow (h : p in n.primesBelow
) : p < n

--- 原说明 ---
The following statement says that summing over `N`-smooth numbers
for large enough `N` gets us arbitrarily close to the sum over all natural numbe
rs
(assuming `f` is norm-summable and `f 0 = 0`; the latter since `0` is not smooth
).
-/
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : ℕ, f m) - ∑' m : N.smoothNumbers, f m‖ < ε := by
  conv => enter [1, N₀, N]; rw [smoothNumbers_eq_factoredNumbers]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum hf₀ εpos
  refine ⟨N₀, fun N hN ↦ hN₀ (range N) fun p hp ↦ ?_⟩
  exact mem_range.mpr <| (lt_of_mem_primesBelow hp).trans_le hN


include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. This version is stated using `HasProd`. -/
/-
**EulerProduct.eulerProduct_hasProd** 是 Mathlib 中的一个定理，位于命名空间 `EulerProduct`。
形式化陈述：eulerProduct_hasProd (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (
fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f n)
参数：hsum : Summable (‖f ·‖)；hf₀ : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
· 使用定理 `HasProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasProd
 f…
· 使用定理 `SummationFilter.unconditional.eq_1`：∀ (β : Type u_2), SummationFilter.un
conditional β = { filter := Filter.atTop }
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt`：norm_tsum_factoredNu
mbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0) {ε : Real} (εpos : 0 < ε) 
: exists N : Nat, forall s : Finset Nat,…
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用引理 `Finset.prod_mulIndicator_eq_prod_filter`：prod_mulIndicator_eq_prod_filte
r (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ) [DecidablePred 
fun i => g i in t i] : ∏ i in…
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers`：prod_filter
_prime_tsum_eq_tsum_factoredNumbers (hsum : Summable (‖f ·‖)) (s : Finset Nat) :
 ∏ p in s with p.Prime, ∑' n : Nat, f (p ^ n) = ∑…
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用引理 `Nat.lt_of_mem_primesBelow`：lt_of_mem_primesBelow (h : p in n.primesBelow
) : p < n

--- 原说明 ---
The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1
 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. This version is stated using `
HasProd`.
-/
theorem eulerProduct_hasProd (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) := by
  let F : ℕ → R := fun n ↦ ∑' e, f (n ^ e)
  change HasProd (F ∘ Subtype.val (p := (· ∈ {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator, HasProd, SummationFilter.unconditional,
    Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := norm_tsum_factoredNumbers_sub_tsum_lt hsum.of_norm hf₀ hε
  refine ⟨range N₀, fun s hs ↦ ?_⟩
  have : ∏ p ∈ s, {p | Nat.Prime p}.mulIndicator F p = ∏ p ∈ s with p.Prime, F p :=
    prod_mulIndicator_eq_prod_filter s (fun _ ↦ F) _ id
  rw [this, dist_eq_norm, prod_filter_prime_tsum_eq_tsum_factoredNumbers hf₁ hmul hsum,
    norm_sub_rev]
  exact hN₀ s fun p hp ↦ hs <| mem_range.mpr <| lt_of_mem_primesBelow hp

include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : ℕ, if p.Prime then ∑' e, f (p ^ e) else 1 = ∑' n, f n`.
This version is stated using `HasProd` and `Set.mulIndicator`. -/
/-
**EulerProduct.eulerProduct_hasProd_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 `Eule
rProduct`。
形式化陈述：eulerProduct_hasProd_mulIndicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0
) : HasProd (Set.mulIndicator {p | Nat.Prime p} fun p => ∑' e, f (p ^ e)) (∑' n,
 f n)
参数：hsum : Summable (‖f ·‖)；hf₀ : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasProd_subtype_iff_mulIndicator`：hasProd_subtype_iff_mulIndicator {s : 
Set β} : HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a
· 使用定理 `EulerProduct.eulerProduct_hasProd`：eulerProduct_hasProd (hsum : Summable
 (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f
 n)

--- 原说明 ---
The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1
 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : ℕ, if p.Prime then ∑' e, f (p ^ e) else 1 = ∑' n, f n`.
This version is stated using `HasProd` and `Set.mulIndicator`.
-/
theorem eulerProduct_hasProd_mulIndicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    HasProd (Set.mulIndicator {p | Nat.Prime p} fun p ↦ ∑' e, f (p ^ e)) (∑' n, f n) := by
  rw [← hasProd_subtype_iff_mulIndicator]
  exact eulerProduct_hasProd hf₁ hmul hsum hf₀

open Filter in
include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
This is a version using convergence of finite partial products. -/
/-
**EulerProduct.eulerProduct** 是 Mathlib 中的一个定理，位于命名空间 `EulerProduct`。
形式化陈述：eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) : Tendsto (fun n : 
Nat => ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n))
参数：hsum : Summable (‖f ·‖)；hf₀ : f 0 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `EulerProduct.eulerProduct_hasProd_mulIndicator`：eulerProduct_hasProd_mul
Indicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (Set.mulIndicator 
{p | Nat.Prime p} fun p => ∑' e, f (…
· 使用引理 `Finset.prod_mulIndicator_eq_prod_filter`：prod_mulIndicator_eq_prod_filte
r (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ) [DecidablePred 
fun i => g i in t i] : ∏ i in…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1
 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
This is a version using convergence of finite partial products.
-/
theorem eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  have := (eulerProduct_hasProd_mulIndicator hf₁ hmul hsum hf₀).tendsto_prod_nat
  let F : ℕ → R := fun p ↦ ∑' (e : ℕ), f (p ^ e)
  have H (n : ℕ) : ∏ i ∈ range n, Set.mulIndicator {p | Nat.Prime p} F i =
                     ∏ p ∈ primesBelow n, ∑' (e : ℕ), f (p ^ e) :=
    prod_mulIndicator_eq_prod_filter (range n) (fun _ ↦ F) (fun _ ↦ {p | Nat.Prime p}) id
  simpa only [F, H]

include hf₁ hmul in
/-- The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`. -/
/-
**EulerProduct.eulerProduct_tprod** 是 Mathlib 中的一个定理，位于命名空间 `EulerProduct`。
形式化陈述：eulerProduct_tprod (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) : ∏' p : Prim
es, ∑' e, f (p ^ e) = ∑' n, f n
参数：hsum : Summable (‖f ·‖)；hf₀ : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `EulerProduct.eulerProduct_hasProd`：eulerProduct_hasProd (hsum : Summable
 (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f
 n)

--- 原说明 ---
The *Euler Product* for multiplicative (on coprime arguments) functions.

If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`, `f 1
 = 1`, `f` is
multiplicative on coprime arguments, and `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
-/
theorem eulerProduct_tprod (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  (eulerProduct_hasProd hf₁ hmul hsum hf₀).tprod_eq

end EulerProduct

/-!
### Versions for arithmetic functions
-/

namespace ArithmeticFunction

open EulerProduct

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in terms of `HasProd`. -/
nonrec theorem IsMultiplicative.eulerProduct_hasProd {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ ∑' e, f (p ^ e)) (∑' n, f n) :=
  eulerProduct_hasProd hf.1 hf.2 hsum f.map_zero

open Filter in
/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products. -/
nonrec theorem IsMultiplicative.eulerProduct {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) :=
  eulerProduct hf.1 hf.2 hsum f.map_zero

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n`. -/
nonrec theorem IsMultiplicative.eulerProduct_tprod {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  eulerProduct_tprod hf.1 hf.2 hsum f.map_zero

end ArithmeticFunction

end General

section CompletelyMultiplicative

/-!
### Euler Products for completely multiplicative functions

We now assume that `f` is completely multiplicative and has values in a complete normed field `F`.
Then we can use the formula for geometric series to simplify the statement. This leads to
`EulerProduct.eulerProduct_completely_multiplicative_hasProd` and variants.
-/

variable {F : Type*} [NormedField F] [CompleteSpace F]

namespace EulerProduct

-- a helper lemma that is useful below
/-
**EulerProduct.one_sub_inv_eq_geometric_of_summable_norm** 是 Mathlib 中的一个引理，位于命名
空间 `EulerProduct`。
形式化陈述：one_sub_inv_eq_geometric_of_summable_norm {f : Nat ->*₀ F} {p : Nat} (hp :
 p.Prime) (hsum : Summable fun x => ‖f x‖) : (1 - f p)⁻¹ = ∑' (e : Nat), f (p ^ 
e)
参数：hp : p.Prime；hsum : Summable fun x => ‖f x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_geometric_of_norm_lt_one`：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 
1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_geometric_iff_norm_lt_one`：summable_geometric_iff_norm_lt_one :
 (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
lemma one_sub_inv_eq_geometric_of_summable_norm {f : ℕ →*₀ F} {p : ℕ} (hp : p.Prime)
    (hsum : Summable fun x ↦ ‖f x‖) :
    (1 - f p)⁻¹ = ∑' (e : ℕ), f (p ^ e) := by
  simp only [map_pow]
  refine (tsum_geometric_of_norm_lt_one <| summable_geometric_iff_norm_lt_one.mp ?_).symm
  refine Summable.of_norm ?_
  simpa only [Function.comp_def, map_pow]
    using hsum.comp_injective <| Nat.pow_right_injective hp.one_lt

/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `s`-factored
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p ∈ s`. At the same time,
we show that the sum involved converges absolutely. -/
/-
**EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric**
 是 Mathlib 中的一个引理，位于命名空间 `EulerProduct`。
形式化陈述：summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : Nat -
>* F} (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (s : Finset Nat) : Summable (
fun m : factoredNumbers s => ‖f m‖) ∧ HasSum (fun m : factoredNumbers s => f m) 
(∏ p in s with p.Prime, (1 - f p)⁻¹)
参数：h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1；s : Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `tsum_geometric_of_norm_lt_one`：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 
1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_pow_le`：norm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖ <=
 ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_geometric_iff_norm_lt_one`：summable_geometric_iff_norm_lt_one :
 (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用引理 `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`
：summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum (hsum : forall {p : 
Nat}, p.Prime -> Summable (fun n : Nat => ‖f (p ^ n)‖)) (s : …
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1

--- 原说明 ---
Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed 
field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over a
ll `s`-factored
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p ∈ s`. At 
the same time,
we show that the sum involved converges absolutely.
-/
lemma summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (s : Finset ℕ) :
    Summable (fun m : factoredNumbers s ↦ ‖f m‖) ∧
      HasSum (fun m : factoredNumbers s ↦ f m) (∏ p ∈ s with p.Prime, (1 - f p)⁻¹) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have H₁ :
      ∏ p ∈ s with p.Prime, ∑' n : ℕ, f (p ^ n) = ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ := by
    refine prod_congr rfl fun p hp ↦ ?_
    simp only [map_pow]
    exact tsum_geometric_of_norm_lt_one <| h (mem_filter.mp hp).2
  have H₂ : ∀ {p : ℕ}, p.Prime → Summable fun n ↦ ‖f (p ^ n)‖ := by
    intro p hp
    simp only [map_pow]
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_pow_le ..) ?_
    exact summable_geometric_iff_norm_lt_one.mpr <| (norm_norm (f p)).symm ▸ h hp
  exact H₁ ▸ summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum f.map_one hmul H₂ s

/-- A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`
in terms of the value of the series. -/
/-
**EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers** 是 Mathlib 中
的一个引理，位于命名空间 `EulerProduct`。
形式化陈述：prod_filter_prime_geometric_eq_tsum_factoredNumbers {f : Nat ->* F} (hsum 
: Summable f) (s : Finset Nat) : ∏ p in s with p.Prime, (1 - f p)⁻¹ = ∑' m : fac
toredNumbers s, f m
参数：hsum : Summable f；s : Finset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geome
tric`：summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : Nat -
>* F} (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (s : Finset Nat…
· 使用引理 `Summable.norm_lt_one`：Summable.norm_lt_one {F : Type*} [NormedDivisionRi
ng F] [CompleteSpace F] {f : Nat ->* F} (hsum : Summable f) {p : Nat} (hp : 1 < 
p) : ‖f p‖…
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p

--- 原说明 ---
A version of `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime
_geometric`
in terms of the value of the series.
-/
lemma prod_filter_prime_geometric_eq_tsum_factoredNumbers {f : ℕ →* F} (hsum : Summable f)
    (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (1 - f p)⁻¹ = ∑' m : factoredNumbers s, f m := by
  refine (summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric ?_ s).2.tsum_eq.symm
  exact fun {_} hp ↦ hsum.norm_lt_one hp.one_lt

/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `N`-smooth
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p < N`. At the same time,
we show that the sum involved converges absolutely. -/
/-
**EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric** 是 
Mathlib 中的一个引理，位于命名空间 `EulerProduct`。
形式化陈述：summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : Nat ->* 
F} (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (N : Nat) : Summable (fun m : N.
smoothNumbers => ‖f m‖) ∧ HasSum (fun m : N.smoothNumbers => f m) (∏ p in N.prim
esBelow, (1 - f p)⁻¹)
参数：h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1；N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Nat.primesBelow.eq_1`：∀ (n : ℕ), n.primesBelow = {p ∈ Finset.range n | N
at.Prime p}
· 使用引理 `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geome
tric`：summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric {f : Nat -
>* F} (h : forall {p : Nat}, p.Prime -> ‖f p‖ < 1) (s : Finset Nat…

--- 原说明 ---
Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed 
field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over a
ll `N`-smooth
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p < N`. At 
the same time,
we show that the sum involved converges absolutely.
-/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p ∈ N.primesBelow, (1 - f p)⁻¹) := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric h _

/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`
in terms of the value of the series. -/
/-
**EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers** 是 Mathlib 中的一个
引理，位于命名空间 `EulerProduct`。
形式化陈述：prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : Nat ->* F} (hsum : S
ummable f) (N : Nat) : ∏ p in N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumber
s, f m
参数：hsum : Summable f；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Nat.primesBelow.eq_1`：∀ (n : ℕ), n.primesBelow = {p ∈ Finset.range n | N
at.Prime p}
· 使用引理 `EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers`：prod_f
ilter_prime_geometric_eq_tsum_factoredNumbers {f : Nat ->* F} (hsum : Summable f
) (s : Finset Nat) : ∏ p in s with p.Prime, (1 - f p)⁻…

--- 原说明 ---
A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_ge
ometric`
in terms of the value of the series.
-/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F} (hsum : Summable f) (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  rw [smoothNumbers_eq_factoredNumbers, primesBelow]
  exact prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum _

/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in terms of `HasProd`. -/
/-
**EulerProduct.eulerProduct_completely_multiplicative_hasProd** 是 Mathlib 中的一个定理
，位于命名空间 `EulerProduct`。
形式化陈述：eulerProduct_completely_multiplicative_hasProd {f : Nat ->*₀ F} (hsum : Su
mmable (‖f ·‖)) : HasProd (fun p : Primes => (1 - f p)⁻¹) (∑' n, f n)
参数：hsum : Summable (‖f ·‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `EulerProduct.one_sub_inv_eq_geometric_of_summable_norm`：one_sub_inv_eq_g
eometric_of_summable_norm {f : Nat ->*₀ F} {p : Nat} (hp : p.Prime) (hsum : Summ
able fun x => ‖f x‖) : (1 - f p)⁻¹ = ∑' (e :…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `EulerProduct.eulerProduct_hasProd`：eulerProduct_hasProd (hsum : Summable
 (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (fun p : Primes => ∑' e, f (p ^ e)) (∑' n, f
 n)
· 使用定理 `MonoidWithZeroHom.map_one`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 1 = 1
· 使用定理 `MonoidWithZeroHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β) (a b : α),   f (a * b) 
= f a * f b
· 使用定理 `MonoidWithZeroHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 0 = 0

--- 原说明 ---
The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, 
then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in terms of `HasProd`.
-/
theorem eulerProduct_completely_multiplicative_hasProd {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ (1 - f p)⁻¹) (∑' n, f n) := by
  have H : (fun p : Primes ↦ (1 - f p)⁻¹) = fun p : Primes ↦ ∑' (e : ℕ), f (p ^ e) :=
    funext <| fun p ↦ one_sub_inv_eq_geometric_of_summable_norm p.prop hsum
  simpa only [map_pow, H]
    using eulerProduct_hasProd f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum f.map_zero

/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`. -/
/-
**EulerProduct.eulerProduct_completely_multiplicative_tprod** 是 Mathlib 中的一个定理，位
于命名空间 `EulerProduct`。
形式化陈述：eulerProduct_completely_multiplicative_tprod {f : Nat ->*₀ F} (hsum : Summ
able (‖f ·‖)) : ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n
参数：hsum : Summable (‖f ·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative_hasProd`：eulerProduc
t_completely_multiplicative_hasProd {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
 HasProd (fun p : Primes => (1 - f p)⁻¹) (∑' n, f…

--- 原说明 ---
The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, 
then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
-/
theorem eulerProduct_completely_multiplicative_tprod {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (eulerProduct_completely_multiplicative_hasProd hsum).tprod_eq

open Filter in
/-- The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products. -/
/-
**EulerProduct.eulerProduct_completely_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 
`EulerProduct`。
形式化陈述：eulerProduct_completely_multiplicative {f : Nat ->*₀ F} (hsum : Summable (
‖f ·‖)) : Tendsto (fun n : Nat => ∏ p in primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑
' n, f n))
参数：hsum : Summable (‖f ·‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β) (a b : α),   f (a * b) 
= f a * f b
· 使用定理 `HasProd.tendsto_prod_nat`：HasProd.tendsto_prod_nat {f : Nat -> M} (h : H
asProd f m) : Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m)
· 使用定理 `EulerProduct.eulerProduct_hasProd_mulIndicator`：eulerProduct_hasProd_mul
Indicator (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) : HasProd (Set.mulIndicator 
{p | Nat.Prime p} fun p => ∑' e, f (…
· 使用定理 `MonoidWithZeroHom.map_one`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZe
roOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 1 = 1
· 使用定理 `MonoidWithZeroHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (f : α →*₀ β), f 0 = 0
· 使用引理 `Finset.prod_mulIndicator_eq_prod_filter`：prod_mulIndicator_eq_prod_filte
r (s : Finset ι) (f : ι -> κ -> β) (t : ι -> Set κ) (g : ι -> κ) [DecidablePred 
fun i => g i in t i] : ∏ i in…
· 使用引理 `Set.mulIndicator_congr`：mulIndicator_congr (h : EqOn f g s) : mulIndicat
or s f = mulIndicator s g
· 使用引理 `EulerProduct.one_sub_inv_eq_geometric_of_summable_norm`：one_sub_inv_eq_g
eometric_of_summable_norm {f : Nat ->*₀ F} {p : Nat} (hp : p.Prime) (hsum : Summ
able fun x => ‖f x‖) : (1 - f p)⁻¹ = ∑' (e :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
The *Euler Product* for completely multiplicative functions.

If `f : ℕ →*₀ F`, where `F` is a complete normed field and `‖f ·‖` is summable, 
then
`∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n`.
This version is stated in the form of convergence of finite partial products.
-/
theorem eulerProduct_completely_multiplicative {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  have := (eulerProduct_hasProd_mulIndicator f.map_one hmul hsum f.map_zero).tendsto_prod_nat
  have H (n : ℕ) : ∏ p ∈ range n, {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) p =
                     ∏ p ∈ primesBelow n, (1 - f p)⁻¹ :=
    prod_mulIndicator_eq_prod_filter
      (range n) (fun _ ↦ fun p ↦ (1 - f p)⁻¹) (fun _ ↦ {p | Nat.Prime p}) id
  have H' : {p | Nat.Prime p}.mulIndicator (fun p ↦ (1 - f p)⁻¹) =
              {p | Nat.Prime p}.mulIndicator (fun p ↦ ∑' e : ℕ, f (p ^ e)) :=
    Set.mulIndicator_congr fun p hp ↦ one_sub_inv_eq_geometric_of_summable_norm hp hsum
  simpa only [← H, H'] using this

end EulerProduct

end CompletelyMultiplicative

section PrimePow

/-! ### Reindexing infinite sums and products over prime powers -/

open Nat.Primes

variable {α : Type*} [CommGroup α] [UniformSpace α] [IsUniformGroup α] [CompleteSpace α] [T0Space α]
variable {f : ℕ → α}

@[to_additive tsum_primes_pow_eq]
/-
**tprod_primes_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tprod_primes_pow_eq (hf : Multipliable fun n : {n // IsPrimePow n} => f n.
1) : ∏' (p : Nat.Primes) (n : Nat), f (p ^ (n + 1)) = ∏' n : {n : Nat // IsPrime
Pow n}, f n
参数：hf : Multipliable fun n : {n // IsPrimePow n} => f n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Nat.add_one_pos`：∀ (n : ℕ), 0 < n + 1
· 使用引理 `Nat.Primes.prodNatEquiv_apply`：Nat.Primes.prodNatEquiv_apply (p : Nat.Pr
imes) (k : Nat) : prodNatEquiv (p, k) = ⟨p ^ (k + 1), p, k + 1, prime_iff.mp p.p
rop, k.add_one_pos,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.tprod_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : CommGroup α] [inst_1 : UniformSpace α] [IsUniformGroup α]   [CompleteSpa
ce α] [T0Spac…
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.tprod_eq`：Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) 
= ∏' b, f b
-/
theorem tprod_primes_pow_eq (hf : Multipliable fun n : {n // IsPrimePow n} ↦ f n.1) :
    ∏' (p : Nat.Primes) (n : ℕ), f (p ^ (n + 1)) = ∏' n : {n : ℕ // IsPrimePow n}, f n := calc
  _ = ∏' p : Nat.Primes × ℕ, f (prodNatEquiv p) := by
    simpa using (hf.comp_injective prodNatEquiv.injective).tprod_prod.symm
  _ = _ := by rw [← Equiv.tprod_eq prodNatEquiv]

@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
/-
**tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers (hfm : Multipliabl
e f) (hf : Function.mulSupport f subseteq {n | IsPrimePow n}) : ∏' n : Nat, f n 
= ∏' (p : Nat.Primes) (k : Nat), f (p ^ (k + 1))
参数：hfm : Multipliable f；hf : Function.mulSupport f subseteq {n | IsPrimePow n}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_primes_pow_eq`：tprod_primes_pow_eq (hf : Multipliable fun n : {n /
/ IsPrimePow n} => f n.1) : ∏' (p : Nat.Primes) (n : Nat), f (p ^ (n + 1)) = ∏' 
n : {n : …
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tprod_subtype_eq_of_mulSupport_subset`：tprod_subtype_eq_of_mulSupport_su
bset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) : ∏' x : s, f x = ∏
' x, f x
-/
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1)) := by
  rw [tprod_primes_pow_eq (hfm.subtype _)]
  exact (tprod_subtype_eq_of_mulSupport_subset hf).symm

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
/-
**tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers** 是 M
athlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers (
hfm : Multipliable f) (hf : Function.mulSupport f subseteq {n | IsPrimePow n}) :
 ∏' n : Nat, f n = (∏' p : Nat.Primes, f p) * ∏' (p : Nat.Primes) (k : Nat), f (
p ^ (k + 2))
参数：hfm : Multipliable f；hf : Function.mulSupport f subseteq {n | IsPrimePow n}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers`：tprod_eq_tprod_
primes_of_mulSupport_subset_prime_powers (hfm : Multipliable f) (hf : Function.m
ulSupport f subseteq {n | IsPrimePow n}) : ∏'…
· 使用定理 `Multipliable.comp_injective`：Multipliable.comp_injective {i : γ -> β} (h
f : Multipliable f) (hi : Injective i) : Multipliable (f ∘ i)
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用引理 `pow_lt_pow_right₀`：pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m <
 a ^ n
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multipliable.tprod_eq_zero_mul`：∀ {G : Type u_2} [inst : CommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {f : ℕ → G},   Mu
ltipliable f → ∏' (b…
· 使用定理 `IsUniformGroup.to_topologicalGroup`：∀ {α : Type u_1} [inst : UniformSpac
e α] [inst_1 : Group α] [IsUniformGroup α], IsTopologicalGroup α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Multipliable.subtype`：Multipliable.subtype (hf : Multipliable f) (p : β 
-> Prop) : Multipliable (f ∘ (↑) : Subtype p -> α)
（共 40 条，此处仅展示前 30 条）
-/
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = (∏' p : Nat.Primes, f p) * ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k ↦ f (p ^ (k + 1)) :=
    hfm.comp_injective <| (strictMono_nat_of_lt_succ
      (pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one <| · + 1)).injective
  simp only [(hfs' _).tprod_eq_zero_mul, zero_add, pow_one]
  apply (Multipliable.subtype hfm _).tprod_mul
  refine (hfm.comp_injective ?_).prod (f := fun (pk : Nat.Primes × ℕ) ↦ f (pk.1 ^ (pk.2 + 2)))
  exact Subtype.val_injective.comp prodNatEquiv.injective |>.comp <|
    Function.Injective.prodMap (fun ⦃_ _⦄ ↦ id) <| add_left_injective 1

end PrimePow

