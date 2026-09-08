/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.AddCircle
public import Mathlib.MeasureTheory.Covering.LiminfLimsup

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost everywhere with
respect to the Lebesgue measure.

Gallagher's theorem concerns the approximation of real numbers by rational numbers. The input is a
sequence of distances `δ₁, δ₂, ...`, and the theorem concerns the set of real numbers `x` for which
there are infinitely many solutions to:
$$
  |x - m/n| < δₙ,
$$
where the rational number `m/n` is in lowest terms. The result is that for any `δ`, this set is
either almost all `x` or almost no `x`.

This result was proved by Gallagher in 1959
[P. Gallagher, *Approximation by reduced fractions*][Gallagher1961]. It is formalised here as
`AddCircle.addWellApproximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*][KoukoulopoulosMaynard2020].
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

* `approxOrderOf`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ`
  is the set of elements within a distance `δ` of a point of order `n`.
* `wellApproximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
  `wellApproximable A δ` is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it
  is the set of points that lie in infinitely many of the sets `approxOrderOf A n δₙ`.
* `AddCircle.addWellApproximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
  the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
  `addWellApproximable 𝕊 δ` is almost empty or almost full.
* `NormedAddCommGroup.exists_norm_nsmul_le`: a general version of Dirichlet's approximation theorem
* `AddCircle.exists_norm_nsmul_le`: Dirichlet's approximation theorem

## TODO

The hypothesis `hδ` in `AddCircle.addWellApproximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`addWellApproximable 𝕊 δ = univ` (provided `δ` is non-negative).

Use `AddCircle.exists_norm_nsmul_le` to prove:
`addWellApproximable 𝕊 (fun n ↦ 1 / n^2) = { ξ | ¬ IsOfFinAddOrder ξ }`
(which is equivalent to `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`).
-/

@[expose] public section


open Set Filter Function Metric MeasureTheory

open scoped MeasureTheory Topology Pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive /-- In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,
`approxAddOrderOf A n δ` is the set of elements within a distance `δ` of a point of order `n`. -/]
/-
**approxOrderOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：approxOrderOf (A : Type*) [SeminormedGroup A] (n : Nat) (δ : Real) : Set A
参数：A : Type*；n : Nat；δ : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def approxOrderOf (A : Type*) [SeminormedGroup A] (n : ℕ) (δ : ℝ) : Set A :=
  thickening δ {y | orderOf y = n}

@[to_additive mem_approx_add_orderOf_iff]
/-
**mem_approxOrderOf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_approxOrderOf_iff {A : Type*} [SeminormedGroup A] {n : Nat} {δ : Real}
 {a : A} : a in approxOrderOf A n δ ↔ exists b : A, orderOf b = n ∧ a in ball b 
δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_eq_biUnion_ball`：thickening_eq_biUnion_ball {δ : Real}
 {E : Set X} : thickening δ E = ⋃ x in E, ball x δ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_approxOrderOf_iff {A : Type*} [SeminormedGroup A] {n : ℕ} {δ : ℝ} {a : A} :
    a ∈ approxOrderOf A n δ ↔ ∃ b : A, orderOf b = n ∧ a ∈ ball b δ := by
  simp only [approxOrderOf, thickening_eq_biUnion_ball, mem_iUnion₂, mem_ofPred_eq, exists_prop]

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `wellApproximable A δ`
is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approxOrderOf A n δₙ`. -/
@[to_additive addWellApproximable /-- In a seminormed additive group `A`, given a sequence of
distances `δ₁, δ₂, ...`, `addWellApproximable A δ` is the limsup as `n → ∞` of the sets
`approxAddOrderOf A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets
`approxAddOrderOf A n δₙ`. -/]
/-
**wellApproximable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：wellApproximable (A : Type*) [SeminormedGroup A] (δ : Nat -> Real) : Set A
参数：A : Type*；δ : Nat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def wellApproximable (A : Type*) [SeminormedGroup A] (δ : ℕ → ℝ) : Set A :=
  blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n

@[to_additive mem_add_wellApproximable_iff]
/-
**mem_wellApproximable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_wellApproximable_iff {A : Type*} [SeminormedGroup A] {δ : Nat -> Real}
 {a : A} : a in wellApproximable A δ ↔ a in blimsup (fun n => approxOrderOf A n 
(δ n)) atTop fun n => 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_wellApproximable_iff {A : Type*} [SeminormedGroup A] {δ : ℕ → ℝ} {a : A} :
    a ∈ wellApproximable A δ ↔
      a ∈ blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n :=
  Iff.rfl

namespace approxOrderOf

variable {A : Type*} [SeminormedCommGroup A] {a : A} {m n : ℕ} (δ : ℝ)

@[to_additive]
/-
**approxOrderOf.image_pow_subset_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `approxOrd
erOf`。
形式化陈述：image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.Coprime m) : (fun (y : A
) => y ^ m) '' approxOrderOf A n δ subseteq approxOrderOf A n (m * δ)
参数：hm : 0 < m；hmn : n.Coprime m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_approxOrderOf_iff`：mem_approxOrderOf_iff {A : Type*} [SeminormedGrou
p A] {n : Nat} {δ : Real} {a : A} : a in approxOrderOf A n δ ↔ exists b : A, ord
erOf b = n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.Coprime.orderOf_pow`：Nat.Coprime.orderOf_pow (h : (orderOf y).Coprim
e m) : orderOf (y ^ m) = orderOf y
· 使用定理 `Metric.ball_subset_thickening`：ball_subset_thickening {x : X} {E : Set X
} (hx : x in E) (δ : Real) : ball x δ subseteq thickening δ E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_mem_ball`：pow_mem_ball {n : Nat} (hn : 0 < n) (h : a in ball b r) : 
a ^ n in ball (b ^ n) (n • r)
-/
theorem image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.Coprime m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A n δ ⊆ approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m ∈ {u : A | orderOf u = n} := by
    rw [← hb] at hmn ⊢; exact hmn.orderOf_pow
  apply ball_subset_thickening hb ((m : ℝ) • δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, smul_eq_mul]

@[to_additive]
/-
**approxOrderOf.image_pow_subset** 是 Mathlib 中的一个定理，位于命名空间 `approxOrderOf`。
形式化陈述：image_pow_subset (n : Nat) (hm : 0 < m) : (fun (y : A) => y ^ m) '' approx
OrderOf A (n * m) δ subseteq approxOrderOf A n (m * δ)
参数：n : Nat；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_approxOrderOf_iff`：mem_approxOrderOf_iff {A : Type*} [SeminormedGrou
p A] {n : Nat} {δ : Real} {a : A} : a in approxOrderOf A n δ ↔ exists b : A, ord
erOf b = n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `orderOf_pow'`：orderOf_pow' (h : n != 0) : orderOf (x ^ n) = orderOf x / 
Nat.gcd (orderOf x) n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.gcd_mul_left_left`：∀ (m n : ℕ), (m * n).gcd n = n
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Metric.ball_subset_thickening`：ball_subset_thickening {x : X} {E : Set X
} (hx : x in E) (δ : Real) : ball x δ subseteq thickening δ E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_mem_ball`：pow_mem_ball {n : Nat} (hn : 0 < n) (h : a in ball b r) : 
a ^ n in ball (b ^ n) (n • r)
-/
theorem image_pow_subset (n : ℕ) (hm : 0 < m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A (n * m) δ ⊆ approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a ∈ ball b δ⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m ∈ {y : A | orderOf y = n} := by
    rw [mem_ofPred_eq, orderOf_pow' b hm.ne', hb, Nat.gcd_mul_left_left, n.mul_div_cancel hm]
  apply ball_subset_thickening hb (m * δ)
  convert! pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul]

@[to_additive]
/-
**approxOrderOf.smul_subset_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `approxOrderOf`
。
形式化陈述：smul_subset_of_coprime (han : (orderOf a).Coprime n) : a • approxOrderOf A
 n δ subseteq approxOrderOf A (orderOf a * n) δ
参数：han : (orderOf a).Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_eq_biUnion_ball`：thickening_eq_biUnion_ball {δ : Real}
 {E : Set X} : thickening δ E = ⋃ x in E, ball x δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_iUnion₂`：image_iUnion₂ (f : α -> β) (s : forall i, κ i -> Set 
α) : (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `smul_ball''`：smul_ball'' : a • ball b r = ball (a • b) r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`：orderOf_mul_eq_mul_orderO
f_of_coprime (h : Commute x y) (hco : (orderOf x).Coprime (orderOf y)) : orderOf
 (x * y) = orderOf x * orderOf y
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem smul_subset_of_coprime (han : (orderOf a).Coprime n) :
    a • approxOrderOf A n δ ⊆ approxOrderOf A (orderOf a * n) δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  refine iUnion₂_subset_iff.mpr fun b hb c hc => ?_
  simp only [mem_iUnion, exists_prop]
  refine ⟨a * b, ?_, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime han

@[to_additive vadd_eq_of_mul_dvd]
/-
**approxOrderOf.smul_eq_of_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `approxOrderOf`。
形式化陈述：smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) : a • approxOrde
rOf A n δ = approxOrderOf A n δ
参数：hn : 0 < n；han : orderOf a ^ 2 ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_eq_biUnion_ball`：thickening_eq_biUnion_ball {δ : Real}
 {E : Set X} : thickening δ E = ⋃ x in E, ball x δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_iUnion₂`：image_iUnion₂ (f : α -> β) (s : forall i, κ i -> Set 
α) : (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `smul_ball''`：smul_ball'' : a • ball b r = ball (a • b) r
· 使用定理 `Commute.orderOf_mul_eq_right_of_forall_prime_mul_dvd`：orderOf_mul_eq_rig
ht_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfFinOrder y) (hdvd : foral
l p : Nat, p.Prime -> p ∣ orderOf x -> p *…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `orderOf_inv`：orderOf_inv (x : G) : orderOf x⁻¹ = orderOf x
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
（共 31 条，此处仅展示前 30 条）
-/
theorem smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) :
    a • approxOrderOf A n δ = approxOrderOf A n δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_ofPred_eq]
  replace han : ∀ {b : A}, orderOf b = n → orderOf (a * b) = n := by
    intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a b).orderOf_mul_eq_right_of_forall_prime_mul_dvd (orderOf_pos_iff.mp hn)
      fun p _ hp' => dvd_trans (mul_dvd_mul_right hp' <| orderOf a) han]
  let f : {b : A | orderOf b = n} → {b : A | orderOf b = n} := fun b => ⟨a * b, han b.property⟩
  have hf : Surjective f := by
    rintro ⟨b, hb⟩
    refine ⟨⟨a⁻¹ * b, ?_⟩, ?_⟩
    · rw [mem_ofPred_eq, ← orderOf_inv, mul_inv_rev, inv_inv, mul_comm]
      apply han
      simpa
    · simp only [f, mul_inv_cancel_left]
  simpa only [mem_ofPred_eq, Subtype.coe_mk, iUnion_coe_set] using
    hf.iUnion_comp fun b => ball (b : A) δ

end approxOrderOf

namespace UnitAddCircle

/-
**UnitAddCircle.mem_approxAddOrderOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCircl
e`。
形式化陈述：mem_approxAddOrderOf_iff {δ : Real} {x : UnitAddCircle} {n : Nat} (hn : 0 
< n) : x in approxAddOrderOf UnitAddCircle n δ ↔ exists m < n, gcd m n = 1 ∧ ‖x 
- ↑((m : Real) / n)‖ < δ
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddCircle.addOrderOf_eq_pos_iff`：addOrderOf_eq_pos_iff {u : AddCircle p}
 {n : Nat} (h : 0 < n) : addOrderOf u = n ↔ exists m < n, m.gcd n = 1 ∧ ↑(↑m / ↑
n * p) = u
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
-/
theorem mem_approxAddOrderOf_iff {δ : ℝ} {x : UnitAddCircle} {n : ℕ} (hn : 0 < n) :
    x ∈ approxAddOrderOf UnitAddCircle n δ ↔ ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ := by
  simp only [mem_approx_add_orderOf_iff, mem_ofPred_eq, ball, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : ℝ) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩
/-
**UnitAddCircle.mem_addWellApproximable_iff** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCi
rcle`。
形式化陈述：mem_addWellApproximable_iff (δ : Nat -> Real) (x : UnitAddCircle) : x in a
ddWellApproximable UnitAddCircle δ ↔ {n : Nat | exists m < n, gcd m n = 1 ∧ ‖x -
 ↑((m : Real) / n)‖ < δ n}.Infinite
参数：δ : Nat -> Real；x : UnitAddCircle。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.cofinite.blimsup_set_eq`：∀ {α : Type u_1} {ι : Type u_4} {p : ι →
 Prop} {s : ι → Set α},   Filter.blimsup s Filter.cofinite p = {x | {n | p n ∧ x
 ∈ s n}.Infinite}
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UnitAddCircle.mem_approxAddOrderOf_iff`：mem_approxAddOrderOf_iff {δ : Re
al} {x : UnitAddCircle} {n : Nat} (hn : 0 < n) : x in approxAddOrderOf UnitAddCi
rcle n δ ↔ exists m < n, gcd…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mem_addWellApproximable_iff (δ : ℕ → ℝ) (x : UnitAddCircle) :
    x ∈ addWellApproximable UnitAddCircle δ ↔
      {n : ℕ | ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ n}.Infinite := by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_ofPred_eq]
  refine iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
  · exact (mem_approxAddOrderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, _, _⟩ := hn; exact pos_of_gt hm₁
    exact ⟨h, (mem_approxAddOrderOf_iff h).mpr hn⟩

end UnitAddCircle

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

local notation a "∤" b => ¬a ∣ b

local notation a "∣∣" b => a ∣ b ∧ (a * a)∤b

local notation "𝕊" => AddCircle T

set_option backward.isDefEq.respectTransparency.types false in
/-- **Gallagher's ergodic theorem** on Diophantine approximation. -/
/-
**AddCircle.addWellApproximable_ae_empty_or_univ** 是 Mathlib 中的一个定理，位于命名空间 `AddC
ircle`。
形式化陈述：addWellApproximable_ae_empty_or_univ (δ : Nat -> Real) (hδ : Tendsto δ atT
op (𝓝 0)) : (forallᵐ x, x ∉ addWellApproximable 𝕊 δ) ∨ forallᵐ x, x in addWellAp
proximable 𝕊 δ
参数：δ : Nat -> Real；hδ : Tendsto δ atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCircle.addOrderOf_div_of_gcd_eq_one`：addOrderOf_div_of_gcd_eq_one {m 
n : Nat} (hn : 0 < n) (h : m.gcd n = 1) : addOrderOf (↑(↑m / ↑n * p) : AddCircle
 p) = n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `gcd_one_left`：gcd_one_left [NormalizedGCDMonoid α] (a : α) : gcd 1 a = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p
· 使用定理 `MeasurableSet.measurableSet_blimsup`：measurableSet_blimsup {s : Nat -> S
et α} {p : Nat -> Prop} (h : forall n, p n -> MeasurableSet (s n)) : MeasurableS
et blimsup s atTop p
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `addWellApproximable.eq_1`：∀ (A : Type u_1) [inst : SeminormedAddGroup A]
 (δ : ℕ → ℝ),   addWellApproximable A δ = Filter.blimsup (fun n => approxAddOrde
rOf A n (δ n))…
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
**Gallagher's ergodic theorem** on Diophantine approximation.
-/
theorem addWellApproximable_ae_empty_or_univ (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (∀ᵐ x, x ∉ addWellApproximable 𝕊 δ) ∨ ∀ᵐ x, x ∈ addWellApproximable 𝕊 δ := by
  /- Sketch of proof:

    Let `E := addWellApproximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∣∣ n))`
      `C p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p*p ∣ n))`.
    In other words, `A p` is the set of points `x` for which there exist infinitely many `n` such
    that `x` is within a distance `δ n` of a point of order `n` and `p ∤ n`. Similarly for `B`, `C`.

    These sets have the following key properties:
      1. `A p` is almost invariant under the ergodic map `y ↦ p • y`
      2. `B p` is almost invariant under the ergodic map `y ↦ p • y + 1/p`
      3. `C p` is invariant under the map `y ↦ y + 1/p`
    To prove 1 and 2 we need the key result `blimsup_thickening_mul_ae_eq` but 3 is elementary.

    It follows from `AddCircle.ergodic_nsmul_add` and `Ergodic.ae_empty_or_univ_of_image_ae_le` that
    if either `A p` or `B p` is not almost empty for any `p`, then it is almost full and thus so is
    `E`. We may therefore assume that `A p` and `B p` are almost empty for all `p`. We thus have
    `E` is almost equal to `C p` for every prime. Combining this with 3 we find that `E` is almost
    invariant under the map `y ↦ y + 1/p` for every prime `p`. The required result then follows from
    `AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`. -/
  let : SemilatticeSup Nat.Primes := Nat.Subtype.semilatticeSup _
  set μ : Measure 𝕊 := volume
  set u : Nat.Primes → 𝕊 := fun p => ↑((↑(1 : ℕ) : ℝ) / ((p : ℕ) : ℝ) * T)
  have hu₀ : ∀ p : Nat.Primes, addOrderOf (u p) = (p : ℕ) := by
    rintro ⟨p, hp⟩; exact addOrderOf_div_of_gcd_eq_one hp.pos (gcd_one_left p)
  have hu : Tendsto (addOrderOf ∘ u) atTop atTop := by
    rw [(funext hu₀ : addOrderOf ∘ u = (↑))]
    have h_mono : Monotone ((↑) : Nat.Primes → ℕ) := fun p q hpq => hpq
    refine h_mono.tendsto_atTop_atTop fun n => ?_
    obtain ⟨p, hp, hp'⟩ := n.exists_infinite_primes
    exact ⟨⟨p, hp'⟩, hp⟩
  set E := addWellApproximable 𝕊 δ
  set X : ℕ → Set 𝕊 := fun n => approxAddOrderOf 𝕊 n (δ n)
  set A : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∤n
  set B : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∣∣n
  set C : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p ^ 2 ∣ n
  have hA₀ : ∀ p, MeasurableSet (A p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hB₀ : ∀ p, MeasurableSet (B p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hE₀ : NullMeasurableSet E μ := by
    refine (MeasurableSet.measurableSet_blimsup fun n hn =>
      IsOpen.measurableSet ?_).nullMeasurableSet
    exact isOpen_thickening
  have hE₁ : ∀ p, E = A p ∪ B p ∪ C p := by
    intro p
    simp only [E, A, B, C, addWellApproximable, ← blimsup_or_eq_sup, ← and_or_left, ← sup_eq_union,
      sq]
    congr
    ext n
    tauto
  have hE₂ : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊) → E =ᵐ[μ] C p := by
    rintro p ⟨hA, hB⟩
    rw [hE₁ p]
    exact union_ae_eq_right_of_ae_eq_empty ((union_ae_eq_right_of_ae_eq_empty hA).trans hB)
  have hA : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∨ A p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => (p : ℕ) • y
    suffices
      f '' A p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∤n by
      apply (ergodic_nsmul hp.one_lt).ae_empty_or_univ_of_image_ae_le (hA₀ p).nullMeasurableSet
      apply (LE.le.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∤n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup fun n hn => ?_)
    replace hn := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.2 hn.2)
    exact approxAddOrderOf.image_nsmul_subset_of_coprime (δ n) hp.pos hn
  have hB : ∀ p : Nat.Primes, B p =ᵐ[μ] (∅ : Set 𝕊) ∨ B p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let x := u ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => p • y + x
    suffices
      f '' B p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∣∣n by
      apply (ergodic_nsmul_add x hp.one_lt).ae_empty_or_univ_of_image_ae_le
        (hB₀ p).nullMeasurableSet
      apply (LE.le.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∣∣n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup ?_)
    rintro n ⟨hn, h_div, h_ndiv⟩
    have h_cop : (addOrderOf x).Coprime (n / p) := by
      obtain ⟨q, rfl⟩ := h_div
      rw [hu₀, Subtype.coe_mk, hp.coprime_iff_not_dvd, q.mul_div_cancel_left hp.pos]
      exact fun contra => h_ndiv (mul_dvd_mul_left p contra)
    replace h_div : n / p * p = n := Nat.div_mul_cancel h_div
    have hf : f = (fun y => x + y) ∘ fun y => p • y := by
      ext; simp [f, add_comm x]
    simp_rw [Function.comp_apply]
    rw [sSupHom.setImage_toFun, hf, image_comp]
    have := @monotone_image 𝕊 𝕊 fun y => x + y
    specialize this (approxAddOrderOf.image_nsmul_subset (δ n) (n / p) hp.pos)
    simp only [h_div] at this ⊢
    refine this.trans ?_
    convert! approxAddOrderOf.vadd_subset_of_coprime (p * δ n) h_cop
    rw [hu₀, Subtype.coe_mk, mul_comm p, h_div]
  change (∀ᵐ x, x ∉ E) ∨ E ∈ ae volume
  rw [← eventuallyEq_empty, ← eventuallyEq_univ]
  have hC : ∀ p : Nat.Primes, u p +ᵥ C p = C p := by
    intro p
    let e := (AddAction.toPerm (u p) : Equiv.Perm 𝕊).toOrderIsoSet
    change e (C p) = C p
    rw [OrderIso.apply_blimsup e, ← hu₀ p]
    exact blimsup_congr (Eventually.of_forall fun n hn =>
      approxAddOrderOf.vadd_eq_of_mul_dvd (δ n) hn.1 hn.2)
  by_cases! +distrib h : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊)
  · replace h : ∀ p : Nat.Primes, (u p +ᵥ E : Set _) =ᵐ[μ] E := by
      intro p
      replace hE₂ : E =ᵐ[μ] C p := hE₂ p (h p)
      have h_qmp : Measure.QuasiMeasurePreserving (-u p +ᵥ ·) μ μ :=
        (measurePreserving_vadd _ μ).quasiMeasurePreserving
      refine (h_qmp.vadd_ae_eq_of_ae_eq (u p) hE₂).trans (ae_eq_trans ?_ hE₂.symm)
      rw [hC]
    exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu
  · right
    obtain ⟨p, hp⟩ := h
    rw [hE₁ p]
    cases hp
    · rcases hA p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left]
    · rcases hB p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left,
        union_ae_eq_univ_of_ae_eq_univ_right]

/-- A general version of **Dirichlet's approximation theorem**.

See also `AddCircle.exists_norm_nsmul_le`. -/
/-
**AddCircle._root_.NormedAddCommGroup.exists_norm_nsmul_le** 是 Mathlib 中的一个引理，位于
命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A general version of **Dirichlet's approximation theorem**.

See also `AddCircle.exists_norm_nsmul_le`.
-/
lemma _root_.NormedAddCommGroup.exists_norm_nsmul_le {A : Type*}
    [NormedAddCommGroup A] [CompactSpace A] [PreconnectedSpace A]
    [MeasurableSpace A] [BorelSpace A] {μ : Measure A} [μ.IsAddHaarMeasure]
    (ξ : A) {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : μ univ ≤ (n + 1) • μ (closedBall (0 : A) (δ / 2))) :
    ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ δ := by
  let B : Icc 0 n → Set A := fun j ↦ closedBall ((j : ℕ) • ξ) (δ / 2)
  have hB : ∀ j, IsClosed (B j) := fun j ↦ isClosed_closedBall
  suffices ¬ Pairwise (Disjoint on B) by
    obtain ⟨i, j, hij, x, hx⟩ := exists_lt_mem_inter_of_not_pairwise_disjoint this
    refine ⟨j - i, ⟨le_tsub_of_add_le_left hij, ?_⟩, ?_⟩
    · simpa only [tsub_le_iff_right] using j.property.2.trans le_self_add
    · rw [sub_nsmul _ (Subtype.coe_le_coe.mpr hij.le), ← sub_eq_add_neg, ← dist_eq_norm]
      exact (dist_triangle ((j : ℕ) • ξ) x ((i : ℕ) • ξ)).trans (by
        linarith [mem_closedBall.mp hx.1, mem_closedBall'.mp hx.2])
  by_contra h
  apply hn.ne'
  have h' : ⋃ j, B j = univ := by
    rw [← (isClosed_iUnion_of_finite hB).measure_eq_univ_iff_eq (μ := μ)]
    refine le_antisymm (μ.mono (subset_univ _)) ?_
    simp_rw [measure_iUnion h (fun _ ↦ measurableSet_closedBall), tsum_fintype,
      B, μ.addHaar_closedBall_center, Finset.sum_const, Finset.card_univ, Fintype.card_Icc,
      Nat.card_Icc, tsub_zero]
    exact hδ
  replace hδ : 0 ≤ δ / 2 := by
    by_contra contra
    refine (isOpen_univ.measure_pos μ univ_nonempty).not_ge <| hδ.trans ?_
    suffices μ (closedBall 0 (δ / 2)) = 0 by simp [this]
    rw [not_le, ← closedBall_eq_empty (x := (0 : A))] at contra
    simp [contra]
  have h'' : ∀ j, (B j).Nonempty := by intro j; rwa [nonempty_closedBall]
  simpa using subsingleton_of_disjoint_isClosed_iUnion_eq_univ h'' h hB h'

/-- **Dirichlet's approximation theorem**

See also `Real.exists_rat_abs_sub_le_and_den_le`. -/
/-
**AddCircle.exists_norm_nsmul_le** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：exists_norm_nsmul_le (ξ : 𝕊) {n : Nat} (hn : 0 < n) : exists j in Icc 1 n,
 ‖j • ξ‖ <= T / ↑(n + 1)
参数：ξ : 𝕊；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddCommGroup.exists_norm_nsmul_le`：∀ {A : Type u_1} [inst : Normed
AddCommGroup A] [CompactSpace A] [PreconnectedSpace A] [inst_3 : MeasurableSpace
 A]   [BorelSpace A] {μ : Mea…
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `AddCircle.instIsAddHaarMeasureRealVolume`：∀ (T : ℝ) [hT : Fact (0 < T)],
 MeasureTheory.volume.IsAddHaarMeasure
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.measure_univ`：∀ (T : ℝ) [hT : Fact (0 < T)], MeasureTheory.vol
ume Set.univ = ENNReal.ofReal T
· 使用定理 `AddCircle.volume_closedBall`：volume_closedBall {x : AddCircle T} (ε : Re
al) : volume (Metric.closedBall x ε) = ENNReal.ofReal (min T (2 * ε))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_nsmul`：ofReal_nsmul {x : Real} {n : Nat} : ENNReal.ofReal
 (n • x) = n • ENNReal.ofReal x
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
**Dirichlet's approximation theorem**

See also `Real.exists_rat_abs_sub_le_and_den_le`.
-/
lemma exists_norm_nsmul_le (ξ : 𝕊) {n : ℕ} (hn : 0 < n) :
    ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ T / ↑(n + 1) := by
  apply NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn
  rw [AddCircle.measure_univ, volume_closedBall, ← ENNReal.ofReal_nsmul,
    mul_div_cancel₀ _ two_ne_zero, min_eq_right (div_le_self hT.out.le <| by simp), nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)]

end AddCircle

