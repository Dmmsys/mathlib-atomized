/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Set.Image
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Algebra.Order.Group.Pointwise.Bounds

/-!
# ℓp space

This file describes properties of elements `f` of a pi-type `∀ i, E i` with finite "norm",
defined for `p : ℝ≥0∞` as the size of the support of `f` if `p=0`, `(∑' a, ‖f a‖^p) ^ (1/p)` for
`0 < p < ∞` and `⨆ a, ‖f a‖` for `p=∞`.

The Prop-valued `Memℓp f p` states that a function `f : ∀ i, E i` has finite norm according
to the above definition; that is, `f` has finite support if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if
`0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if `p = ∞`.

The space `lp E p` is the subtype of elements of `∀ i : α, E i` which satisfy `Memℓp f p`. For
`1 ≤ p`, the "norm" is genuinely a norm and `lp` is a complete metric space.

## Main definitions

* `Memℓp f p` : property that the function `f` satisfies, as appropriate, `f` finitely supported
  if `p = 0`, `Summable (fun a ↦ ‖f a‖^p)` if `0 < p < ∞`, and `BddAbove (norm '' (Set.range f))` if
  `p = ∞`.
* `lp E p` : elements of `∀ i : α, E i` such that `Memℓp f p`. Defined as an `AddSubgroup` of
  a type synonym `PreLp` for `∀ i : α, E i`, and equipped with a `NormedAddCommGroup` structure.
  Under appropriate conditions, this is also equipped with the instances `lp.normedSpace`,
  `lp.completeSpace`. For `p=∞`, there is also `lp.inftyNormedRing`,
  `lp.inftyNormedAlgebra`, `lp.inftyStarRing` and `lp.inftyCStarRing`.

## Main results

* `Memℓp.of_exponent_ge`: For `q ≤ p`, a function which is `Memℓp` for `q` is also `Memℓp` for `p`.
* `lp.memℓp_of_tendsto`, `lp.norm_le_of_tendsto`: A pointwise limit of functions in `lp`, all with
  `lp` norm `≤ C`, is itself in `lp` and has `lp` norm `≤ C`.
* `lp.tsum_mul_le_mul_norm`: basic form of Hölder's inequality

## Implementation

Since `lp` is defined as an `AddSubgroup`, dot notation does not work. Use `lp.norm_neg f` to
say that `‖-f‖ = ‖f‖`, instead of the non-working `f.norm_neg`.

## TODO

* More versions of Hölder's inequality (for example: the case `p = 1`, `q = ∞`; a version for normed
  rings which has `‖∑' i, f i * g i‖` rather than `∑' i, ‖f i‖ * g i‖` on the RHS; a version for
  three exponents satisfying `1 / r = 1 / p + 1 / q`)

-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal Function

variable {𝕜 𝕜' : Type*} {α : Type*} {E : α → Type*} {p q : ℝ≥0∞} [∀ i, NormedAddCommGroup (E i)]

/-!
### `Memℓp` predicate

-/


/-- The property that `f : ∀ i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `Set.range (fun i ↦ ‖f i‖)`, if `p = ∞`, or
* has the series `∑' i, ‖f i‖ ^ p` be summable, if `0 < p < ∞`. -/
/-
**Mem** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that `f : ∀ i : α, E i`
* is finitely supported, if `p = 0`, or
* admits an upper bound for `Set.range (fun i ↦ ‖f i‖)`, if `p = ∞`, or
* has the series `∑' i, ‖f i‖ ^ p` be summable, if `0 < p < ∞`.
-/
def Memℓp (f : ∀ i, E i) (p : ℝ≥0∞) : Prop :=
  if p = 0 then Set.Finite { i | f i ≠ 0 }
  else if p = ∞ then BddAbove (Set.range fun i => ‖f i‖)
  else Summable fun i => ‖f i‖ ^ p.toReal
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_zero_iff {f : ∀ i, E i} : Memℓp f 0 ↔ Set.Finite { i | f i ≠ 0 } := by
  dsimp [Memℓp]
  rw [if_pos rfl]
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_zero {f : ∀ i, E i} (hf : Set.Finite { i | f i ≠ 0 }) : Memℓp f 0 :=
  memℓp_zero_iff.2 hf
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_infty_iff {f : ∀ i, E i} : Memℓp f ∞ ↔ BddAbove (Set.range fun i => ‖f i‖) := by
  simp [Memℓp]
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_infty {f : ∀ i, E i} (hf : BddAbove (Set.range fun i => ‖f i‖)) : Memℓp f ∞ :=
  memℓp_infty_iff.2 hf
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_gen_iff (hp : 0 < p.toReal) {f : ∀ i, E i} :
    Memℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal := by
  rw [ENNReal.toReal_pos_iff] at hp
  dsimp [Memℓp]
  rw [if_neg hp.1.ne', if_neg hp.2.ne]
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_gen {f : ∀ i, E i} (hf : Summable fun i => ‖f i‖ ^ p.toReal) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    exact (Set.Finite.of_summable_const (by simp) H).subset (Set.subset_univ _)
  · apply memℓp_infty
    have H : Summable fun _ : α => (1 : ℝ) := by simpa using hf
    simpa using ((Set.Finite.of_summable_const (by simp) H).image fun i => ‖f i‖).bddAbove
  exact (memℓp_gen_iff hp).2 hf
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_gen' {C : ℝ} {f : ∀ i, E i} (hf : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C) :
    Memℓp f p := by
  apply memℓp_gen
  use ⨆ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    positivity
  apply isLUB_ciSup
  use C
  rintro - ⟨s, rfl⟩
  exact hf s
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_gen_iff' {f : (i : α) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∀ (s : Finset α), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ∑' i, ‖f i‖ ^ p.toReal := by
  refine ⟨fun hf ↦ ?_, memℓp_gen'⟩
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp only [Memℓp, hp₁.ne', ↓reduceIte, hp₂.ne] at hf
  simpa [upperBounds] using isLUB_hasSum (by intro; positivity) hf.hasSum |>.1
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_gen_iff'' {f : (i : α) → E i} (hp : 0 < p.toReal) :
    Memℓp f p ↔ ∃ C, 0 ≤ C ∧ ∀ (s : Finset α), ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C := by
  refine ⟨fun hf ↦ ?_, fun ⟨C, _, hC⟩ ↦ memℓp_gen' hC⟩
  exact ⟨_, tsum_nonneg fun i ↦ (by positivity), memℓp_gen_iff' hp |>.mp hf⟩

/-- When `α` is `Finite`, every `f : PreLp E p` satisfies `Memℓp f p`. -/
/-
**Mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is `Finite`, every `f : PreLp E p` satisfies `Memℓp f p`.
-/
theorem Memℓp.all [Finite α] (f : ∀ i, E i) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | _h)
  · exact memℓp_zero_iff.mpr { i : α | f i ≠ 0 }.toFinite
  · exact memℓp_infty_iff.mpr (Set.Finite.bddAbove (Set.range fun i : α ↦ ‖f i‖).toFinite)
  · cases nonempty_fintype α; exact memℓp_gen ⟨Finset.univ.sum _, hasSum_fintype _⟩
/-
**zero_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_memℓp : Memℓp (0 : ∀ i, E i) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp
  · apply memℓp_infty
    simp only [norm_zero, Pi.zero_apply]
    exact bddAbove_singleton.mono Set.range_const_subset
  · apply memℓp_gen
    simp [Real.zero_rpow hp.ne', summable_zero]
/-
**zero_mem_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_mem_ℓp' : Memℓp (fun i : α => (0 : E i)) p :=
  zero_memℓp
/-
**mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem memℓp_norm_iff {f : (i : α) → E i} :
    Memℓp (‖f ·‖) p ↔ Memℓp f p := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp [memℓp_zero_iff]
  · simp [memℓp_infty_iff]
  · simp [memℓp_gen_iff hp]

alias ⟨Memℓp.of_norm, Memℓp.norm⟩ := memℓp_norm_iff
namespace Memℓp

/-
**Memℓp.mono** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：mono {f : (i : α) -> E i} {g : α -> Real} (hg : Memℓp g p) (hfg : forall i
, ‖f i‖ <= g i) : Memℓp f p
参数：i : α；hg : Memℓp g p；hfg : forall i, ‖f i‖ <= g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.le_norm_self`：le_norm_self (r : Real) : r <= ‖r‖
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `memℓp_infty_iff`：memℓp_infty_iff {f : forall i, E i} : Memℓp f ∞ ↔ BddAb
ove (Set.range fun i => ‖f i‖)
· 使用引理 `BddAbove.range_mono`：BddAbove.range_mono [Preorder β] {f : α -> β} (g : 
α -> β) (h : forall a, f a <= g a) (hbdd : BddAbove (range g)) : BddAbove (range
 f)
· 使用定理 `memℓp_gen_iff`：memℓp_gen_iff (hp : 0 < p.toReal) {f : forall i, E i} : M
emℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mono {f : (i : α) → E i} {g : α → ℝ}
    (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ g i) :
    Memℓp f p := by
  replace hfg (i) : ‖f i‖ ≤ ‖g i‖ := (hfg i).trans (Real.le_norm_self _)
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp_rw [memℓp_zero_iff, ← norm_pos_iff] at hg ⊢
    refine hg.subset fun i hi ↦ hi.trans_le <| hfg i
  · rw [memℓp_infty_iff] at hg ⊢
    exact hg.range_mono _ hfg
  · rw [memℓp_gen_iff hp] at hg ⊢
    apply hg.of_norm_bounded fun i ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact hfg i

/-- Often it is more convenient to use `Memℓp.mono`, where the bounding function is real-valued.
This version is provable from that one using `Memℓp.toNorm` applied to the argument with type
`Memℓp g p`. -/
/-
**Memℓp.mono'** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：mono' {F : α -> Type*} [forall i, NormedAddCommGroup (F i)] {f : (i : α) -
> E i} {g : (i : α) -> F i} (hg : Memℓp g p) (hfg : forall i, ‖f i‖ <= ‖g i‖) : 
Memℓp f p
参数：F i；i : α；i : α；hg : Memℓp g p；hfg : forall i, ‖f i‖ <= ‖g i‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.mono`：mono {f : (i : α) -> E i} {g : α -> Real} (hg : Memℓp g p) (
hfg : forall i, ‖f i‖ <= g i) : Memℓp f p
· 使用定理 `Memℓp.norm`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i
 : α) → NormedAddCommGroup (E i)] {f : (i : α) → E i},   Memℓp f p → Memℓp (fun 
…

--- 原说明 ---
Often it is more convenient to use `Memℓp.mono`, where the bounding function is 
real-valued.
This version is provable from that one using `Memℓp.toNorm` applied to the argum
ent with type
`Memℓp g p`.
-/
theorem mono' {F : α → Type*} [∀ i, NormedAddCommGroup (F i)] {f : (i : α) → E i}
    {g : (i : α) → F i} (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ ‖g i‖) :
    Memℓp f p :=
  hg.norm.mono hfg
/-
**Memℓp.finite_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：finite_dsupport {f : forall i, E i} (hf : Memℓp f 0) : Set.Finite { i | f 
i != 0 }
参数：hf : Memℓp f 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `memℓp_zero_iff`：memℓp_zero_iff {f : forall i, E i} : Memℓp f 0 ↔ Set.Fin
ite { i | f i != 0 }
-/
theorem finite_dsupport {f : ∀ i, E i} (hf : Memℓp f 0) : Set.Finite { i | f i ≠ 0 } :=
  memℓp_zero_iff.1 hf
/-
**Memℓp.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：bddAbove {f : forall i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i 
=> ‖f i‖)
参数：hf : Memℓp f ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `memℓp_infty_iff`：memℓp_infty_iff {f : forall i, E i} : Memℓp f ∞ ↔ BddAb
ove (Set.range fun i => ‖f i‖)
-/
theorem bddAbove {f : ∀ i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i => ‖f i‖) :=
  memℓp_infty_iff.1 hf
/-
**Memℓp.summable** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : Memℓp f p) : Summab
le fun i => ‖f i‖ ^ p.toReal
参数：hp : 0 < p.toReal；hf : Memℓp f p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `memℓp_gen_iff`：memℓp_gen_iff (hp : 0 < p.toReal) {f : forall i, E i} : M
emℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal
-/
theorem summable (hp : 0 < p.toReal) {f : ∀ i, E i} (hf : Memℓp f p) :
    Summable fun i => ‖f i‖ ^ p.toReal :=
  (memℓp_gen_iff hp).1 hf
/-
**Memℓp.summable_of_one** 是 Mathlib 中的一个引理，位于命名空间 `Memℓp`。
形式化陈述：summable_of_one {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {x : 
α -> E} (hx : Memℓp x 1) : Summable x
参数：hx : Memℓp x 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
-/
lemma summable_of_one {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {x : α → E} (hx : Memℓp x 1) : Summable x :=
  .of_norm <| by simpa using hx.summable
/-
**Memℓp.neg** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：neg {f : forall i, E i} (hf : Memℓp f p) : Memℓp (-f) p
参数：hf : Memℓp f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `memℓp_zero`：memℓp_zero {f : forall i, E i} (hf : Set.Finite { i | f i !=
 0 }) : Memℓp f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `memℓp_infty`：memℓp_infty {f : forall i, E i} (hf : BddAbove (Set.range f
un i => ‖f i‖)) : Memℓp f ∞
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Memℓp.bddAbove`：bddAbove {f : forall i, E i} (hf : Memℓp f ∞) : BddAbove
 (Set.range fun i => ‖f i‖)
· 使用定理 `memℓp_gen`：memℓp_gen {f : forall i, E i} (hf : Summable fun i => ‖f i‖ ^
 p.toReal) : Memℓp f p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
-/
theorem neg {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (-f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp [hf.finite_dsupport]
  · apply memℓp_infty
    simpa using hf.bddAbove
  · apply memℓp_gen
    simpa using hf.summable hp

@[simp]
/-
**Memℓp.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：neg_iff {f : forall i, E i} : Memℓp (-f) p ↔ Memℓp f p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.neg`：neg {f : forall i, E i} (hf : Memℓp f p) : Memℓp (-f) p
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_iff {f : ∀ i, E i} : Memℓp (-f) p ↔ Memℓp f p :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℓp.neg⟩
/-
**Memℓp.of_exponent_ge** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：of_exponent_ge {p q : Real>=0∞} {f : forall i, E i} (hfq : Memℓp f q) (hpq
 : q <= p) : Memℓp f p
参数：hfq : Memℓp f q；hpq : q <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy₂`：∀ {p q : ENNReal},   p ≤ q →     p = 0 ∧ q = 0 ∨   
    p = 0 ∧ q = ⊤ ∨         p = 0 ∧ 0 < q.toReal ∨ p = ⊤ ∧ q = ⊤ ∨ 0 < p.toReal 
∧ q = ⊤ ∨…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `memℓp_infty`：memℓp_infty {f : forall i, E i} (hf : BddAbove (Set.range f
un i => ‖f i‖)) : Memℓp f ∞
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `memℓp_gen`：memℓp_gen {f : forall i, E i} (hf : Summable fun i => ‖f i‖ ^
 p.toReal) : Memℓp f p
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `summable_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddC
ommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}
 {s : Finset β},…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Filter.Tendsto.bddAbove_range_of_cofinite`：Filter.Tendsto.bddAbove_range
_of_cofinite [IsDirectedOrder α] (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.
range u)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
（共 52 条，此处仅展示前 30 条）
-/
theorem of_exponent_ge {p q : ℝ≥0∞} {f : ∀ i, E i} (hfq : Memℓp f q) (hpq : q ≤ p) : Memℓp f p := by
  rcases ENNReal.trichotomy₂ hpq with
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨rfl, rfl⟩ | ⟨hq, rfl⟩ | ⟨hq, _, hpq'⟩)
  · exact hfq
  · apply memℓp_infty
    obtain ⟨C, hC⟩ := (hfq.finite_dsupport.image fun i => ‖f i‖).bddAbove
    use max 0 C
    rintro x ⟨i, rfl⟩
    by_cases hi : f i = 0
    · simp [hi]
    · exact (hC ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  · apply memℓp_gen
    have : ∀ i ∉ hfq.finite_dsupport.toFinset, ‖f i‖ ^ p.toReal = 0 := by
      intro i hi
      have : f i = 0 := by simpa using hi
      simp [this, Real.zero_rpow hp.ne']
    exact summable_of_ne_finset_zero this
  · exact hfq
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bddAbove_range_of_cofinite
    use A ^ q.toReal⁻¹
    rintro x ⟨i, rfl⟩
    have : 0 ≤ ‖f i‖ ^ q.toReal := by positivity
    simpa [← Real.rpow_mul, mul_inv_cancel₀ hq.ne'] using
      Real.rpow_le_rpow this (hA ⟨i, rfl⟩) (inv_nonneg.mpr hq.le)
  · apply memℓp_gen
    have hf' := hfq.summable hq
    refine .of_norm_bounded_eventually hf' (@Set.Finite.subset _ { i | 1 ≤ ‖f i‖ } ?_ _ ?_)
    · have H : { x : α | 1 ≤ ‖f x‖ ^ q.toReal }.Finite := by
        simpa using hf'.tendsto_cofinite_zero.eventually_lt_const (by simp)
      exact H.subset fun i hi => Real.one_le_rpow hi hq.le
    · change ∀ i, ¬|‖f i‖ ^ p.toReal| ≤ ‖f i‖ ^ q.toReal → 1 ≤ ‖f i‖
      intro i hi
      have : 0 ≤ ‖f i‖ ^ p.toReal := by positivity
      simp only [abs_of_nonneg, this] at hi
      contrapose! hi
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq'
/-
**Memℓp.add** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：add {f g : forall i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f + g
) p
参数：hf : Memℓp f p；hg : Memℓp g p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `memℓp_zero`：memℓp_zero {f : forall i, E i} (hf : Set.Finite { i | f i !=
 0 }) : Memℓp f 0
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `memℓp_infty`：memℓp_infty {f : forall i, E i} (hf : BddAbove (Set.range f
un i => ‖f i‖)) : Memℓp f ∞
· 使用定理 `Memℓp.bddAbove`：bddAbove {f : forall i, E i} (hf : Memℓp f ∞) : BddAbove
 (Set.range fun i => ‖f i‖)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `memℓp_gen`：memℓp_gen {f : forall i, E i} (hf : Summable fun i => ‖f i‖ ^
 p.toReal) : Memℓp f p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
（共 53 条，此处仅展示前 30 条）
-/
theorem add {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f + g) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine (hf.finite_dsupport.union hg.finite_dsupport).subset fun i => ?_
    simp only [Pi.add_apply, Ne, Set.mem_union, Set.mem_ofPred_eq]
    contrapose!
    rintro ⟨hf', hg'⟩
    simp [hf', hg']
  · apply memℓp_infty
    obtain ⟨A, hA⟩ := hf.bddAbove
    obtain ⟨B, hB⟩ := hg.bddAbove
    refine ⟨A + B, ?_⟩
    rintro a ⟨i, rfl⟩
    exact le_trans (norm_add_le _ _) (add_le_add (hA ⟨i, rfl⟩) (hB ⟨i, rfl⟩))
  apply memℓp_gen
  let C : ℝ := if p.toReal < 1 then 1 else (2 : ℝ) ^ (p.toReal - 1)
  refine .of_nonneg_of_le ?_ (fun i => ?_) (((hf.summable hp).add (hg.summable hp)).mul_left C)
  · intro; positivity
  · refine (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp.le).trans ?_
    dsimp only [C]
    split_ifs with h
    · simpa using! NNReal.coe_le_coe.2 (NNReal.rpow_add_le_add_rpow ‖f i‖₊ ‖g i‖₊ hp.le h.le)
    · let F : Fin 2 → ℝ≥0 := ![‖f i‖₊, ‖g i‖₊]
      simp only [not_lt] at h
      simpa [Fin.sum_univ_succ] using!
        Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ h fun i _ => (F i).coe_nonneg
/-
**Memℓp.sub** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：sub {f g : forall i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f - g
) p
参数：hf : Memℓp f p；hg : Memℓp g p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Memℓp.add`：add {f g : forall i, E i} (hf : Memℓp f p) (hg : Memℓp g p) :
 Memℓp (f + g) p
· 使用定理 `Memℓp.neg`：neg {f : forall i, E i} (hf : Memℓp f p) : Memℓp (-f) p
-/
theorem sub {f g : ∀ i, E i} (hf : Memℓp f p) (hg : Memℓp g p) : Memℓp (f - g) p := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg
/-
**Memℓp.finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：finsetSum {ι} (s : Finset ι) {f : ι -> forall i, E i} (hf : forall i in s,
 Memℓp (f i) p) : Memℓp (fun a => ∑ i in s, f i a) p
参数：s : Finset ι；hf : forall i in s, Memℓp (f i) p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Memℓp.add`：add {f g : forall i, E i} (hf : Memℓp f p) (hg : Memℓp g p) :
 Memℓp (f + g) p
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem finsetSum {ι} (s : Finset ι) {f : ι → ∀ i, E i} (hf : ∀ i ∈ s, Memℓp (f i) p) :
    Memℓp (fun a => ∑ i ∈ s, f i a) p := by
  have : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp only [zero_mem_ℓp', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias finset_sum := finsetSum

section IsBoundedSMul

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

/-
**Memℓp.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：const_smul {f : forall i, E i} (hf : Memℓp f p) (c : 𝕜) : Memℓp (c • f) p
参数：hf : Memℓp f p；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `memℓp_zero`：memℓp_zero {f : forall i, E i} (hf : Set.Finite { i | f i !=
 0 }) : Memℓp f 0
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Memℓp.bddAbove`：bddAbove {f : forall i, E i} (hf : Memℓp f ∞) : BddAbove
 (Set.range fun i => ‖f i‖)
· 使用定理 `memℓp_infty`：memℓp_infty {f : forall i, E i} (hf : BddAbove (Set.range f
un i => ‖f i‖)) : Memℓp f ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `memℓp_gen`：memℓp_gen {f : forall i, E i} (hf : Summable fun i => ‖f i‖ ^
 p.toReal) : Memℓp f p
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `NNReal.summable_of_le`：summable_of_le {f g : β -> Real>=0} (hgf : forall
 b, g b <= f b) : Summable f -> Summable g | ⟨_r, hfr⟩ => let ⟨_p, _, hp⟩
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem const_smul {f : ∀ i, E i} (hf : Memℓp f p) (c : 𝕜) : Memℓp (c • f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    refine hf.finite_dsupport.subset fun i => (?_ : ¬c • f i = 0 → ¬f i = 0)
    exact not_imp_not.mpr fun hf' => hf'.symm ▸ smul_zero c
  · obtain ⟨A, hA⟩ := hf.bddAbove
    refine memℓp_infty ⟨‖c‖ * A, ?_⟩
    rintro a ⟨i, rfl⟩
    dsimp only [Pi.smul_apply]
    refine (norm_smul_le _ _).trans ?_
    gcongr
    exact hA ⟨i, rfl⟩
  · apply memℓp_gen
    dsimp only [Pi.smul_apply]
    have := (hf.summable hp).mul_left (↑(‖c‖₊ ^ p.toReal) : ℝ)
    simp_rw [← coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul, NNReal.summable_coe,
      ← NNReal.mul_rpow] at this ⊢
    refine NNReal.summable_of_le ?_ this
    intro i
    gcongr
    apply nnnorm_smul_le
/-
**Memℓp.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Memℓp`。
形式化陈述：const_mul {f : α -> 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp (fun x => c * f x)
 p
参数：hf : Memℓp f p；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.const_smul`：const_smul {f : forall i, E i} (hf : Memℓp f p) (c : 𝕜
) : Memℓp (c • f) p
-/
theorem const_mul {f : α → 𝕜} (hf : Memℓp f p) (c : 𝕜) : Memℓp (fun x => c * f x) p :=
  hf.const_smul c

end IsBoundedSMul

end Memℓp

/-!
### lp space

The space of elements of `∀ i, E i` satisfying the predicate `Memℓp`.
-/


/-- We define `PreLp E` to be a type synonym for `∀ i, E i` which, importantly, does not inherit
the `pi` topology on `∀ i, E i` (otherwise this topology would descend to `lp E p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `∀ i, E i` rather than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) to be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below). -/
@[nolint unusedArguments]
/-
**PreLp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreLp (E : α -> Type*) [forall i, NormedAddCommGroup (E i)] : Type _
参数：E : α -> Type*；E i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `PreLp E` to be a type synonym for `∀ i, E i` which, importantly, does
 not inherit
the `pi` topology on `∀ i, E i` (otherwise this topology would descend to `lp E 
p` and conflict
with the normed group topology we will later equip it with.)

We choose to deal with this issue by making a type synonym for `∀ i, E i` rather
 than for the `lp`
subgroup itself, because this allows all the spaces `lp E p` (for varying `p`) t
o be subgroups of
the same ambient group, which permits lemma statements like `lp.monotone` (below
).
-/
def PreLp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] : Type _ :=
  ∀ i, E i

namespace PreLp

-- The `SMul` instance exists to avoid a zsmul diamond.
variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] in
deriving instance SMul 𝕜, AddCommGroup for PreLp E

/-
**PreLp.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {x y : PreLp E} {i : α},   (x + y) i = x i + y i
参数：i : α；E i；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_apply {x y : PreLp E} {i : α} : (x + y) i = x i + y i := rfl
/-
**PreLp.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {i : α}, 0 i = 0
参数：i : α；E i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_apply {i : α} : (0 : PreLp E) i = 0 := rfl
/-
**PreLp.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {x y : PreLp E} {i : α},   (x - y) i = x i - y i
参数：i : α；E i；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_apply {x y : PreLp E} {i : α} : (x - y) i = x i - y i := rfl
/-
**PreLp.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {x : PreLp E} {i : α}, (-x) i = -x i
参数：i : α；E i；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_apply {x : PreLp E} {i : α} : (-x) i = -(x i) := rfl
/-
**PreLp.nsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {n : ℕ} {x : PreLp E} {i : α},   (n • x) i = n • x i
参数：i : α；E i；n • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nsmul_apply {n : ℕ} {x : PreLp E} {i : α} : (n • x) i = n • (x i) := rfl
/-
**PreLp.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PreLp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {n : ℤ} {x : PreLp E} {i : α},   (n • x) i = n • x i
参数：i : α；E i；n • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zsmul_apply {n : ℤ} {x : PreLp E} {i : α} : (n • x) i = n • (x i) := rfl
/-
**PreLp.unique** 是 Mathlib 中的一个实例，位于命名空间 `PreLp`。
形式化陈述：unique [IsEmpty α] : Unique (PreLp E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique [IsEmpty α] : Unique (PreLp E) :=
  inferInstanceAs <| Unique (∀ _, _)

end PreLp

/-- **The (little) ℓᵖ space**: The additive subgroup of a type synonym of `Π i, E i`, which consists
of those functions `f` such that `Memℓp f p` (i.e., `f` has finite `p`-norm).

The non-dependent version comes equipped with the notation `ℓ^p(ι, E)` in the `lp` namespace. When
`p` takes the values `0`, `1` or `2`, the notation `ℓ⁰(ι, E)`, `ℓ¹(ι, E)`, `ℓ²(ι, E)` is also
available. -/
/-
**lp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lp (E : α -> Type*) [forall i, NormedAddCommGroup (E i)] (p : Real>=0∞) : 
AddSubgroup (PreLp E) where carrier
参数：E : α -> Type*；E i；p : Real>=0∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.add`：add {f g : forall i, E i} (hf : Memℓp f p) (hg : Memℓp g p) :
 Memℓp (f + g) p
· 使用定理 `zero_memℓp`：zero_memℓp : Memℓp (0 : forall i, E i) p
· 使用定理 `Memℓp.neg`：neg {f : forall i, E i} (hf : Memℓp f p) : Memℓp (-f) p

--- 原说明 ---
**The (little) ℓᵖ space**: The additive subgroup of a type synonym of `Π i, E i`
, which consists
of those functions `f` such that `Memℓp f p` (i.e., `f` has finite `p`-norm).

The non-dependent version comes equipped with the notation `ℓ^p(ι, E)` in the `l
p` namespace. When
`p` takes the values `0`, `1` or `2`, the notation `ℓ⁰(ι, E)`, `ℓ¹(ι, E)`, `ℓ²(ι
, E)` is also
available.
-/
def lp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞) : AddSubgroup (PreLp E) where
  carrier := { f | Memℓp f p }
  zero_mem' := zero_memℓp
  add_mem' := Memℓp.add
  neg_mem' := Memℓp.neg

@[inherit_doc] scoped[lp] notation "ℓ^" p "(" ι ", " E ")" => lp (fun _ : ι ↦ E) p
/-- `ℓ⁰(ι, E)` is the space of finitely supported functions `ι → E`. In general, this should not
be used outside of the context of `ℓ^p(ι, E)` spaces, and one should instead prefer `Finsupp`
in other situations. -/
scoped[lp] notation "ℓ⁰(" ι ", " E ")" => lp (fun _ : ι ↦ E) 0
/-- `ℓ¹(ι, E)` is the space of summable functions `ι → E`. To be more precise, it is the space
of functions whose *norms* are summable, but when `E` is complete these coincide. -/
scoped[lp] notation "ℓ¹(" ι ", " E ")" => lp (fun _ : ι ↦ E) 1
/-- `ℓ²(ι, E)` is the space of square-summable functions `ι → E`. When `E := 𝕜`, with `RCLike 𝕜`,
this is a Hilbert space. -/
scoped[lp] notation "ℓ²(" ι ", " E ")" => lp (fun _ : ι ↦ E) 2

namespace lp

-- TODO: this instance is bad because it inserts `Subtype.val` as the casting function,
-- which abuses definitional equality.
/-
**lp.coeFun** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：coeFun : CoeFun (lp E p) fun _ => forall i, E i
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeFun : CoeFun (lp E p) fun _ => ∀ i, E i :=
  ⟨Subtype.val (α := ∀ i, E i)⟩

@[ext]
/-
**lp.ext** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
参数：h : (f : forall i, E i) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ext {f g : lp E p} (h : (f : ∀ i, E i) = g) : f = g :=
  Subtype.ext h
/-
**lp.eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：eq_zero' [IsEmpty α] (f : lp E p) : f = 0
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem eq_zero' [IsEmpty α] (f : lp E p) : f = 0 :=
  Subsingleton.elim f 0
/-
**lp.monotone** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {p q : ENNReal}, q ≤ p → lp E q ≤ lp E p
参数：i : α；E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.of_exponent_ge`：of_exponent_ge {p q : Real>=0∞} {f : forall i, E i
} (hfq : Memℓp f q) (hpq : q <= p) : Memℓp f p
-/
protected theorem monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : lp E q ≤ lp E p :=
  fun _ hf => Memℓp.of_exponent_ge hf hpq
/-
**lp.mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem memℓp (f : lp E p) : Memℓp f p :=
  f.prop

variable (E p)

@[simp]
/-
**lp.coeFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_zero : ⇑(0 : lp E p) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_zero : ⇑(0 : lp E p) = 0 :=
  rfl

variable {E p}

@[simp]
/-
**lp.coeFn_neg** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_neg (f : lp E p) : ⇑(-f) = -f
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_neg (f : lp E p) : ⇑(-f) = -f :=
  rfl

@[simp]
/-
**lp.coeFn_add** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_add (f g : lp E p) : ⇑(f + g) = f + g
参数：f g : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_add (f g : lp E p) : ⇑(f + g) = f + g :=
  rfl

variable (p E) in
/-- Coercion to function as an `AddMonoidHom`. -/
/-
**lp.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：coeFnAddMonoidHom : lp E p ->+ (forall i, E i) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to function as an `AddMonoidHom`.
-/
def coeFnAddMonoidHom : lp E p →+ (∀ i, E i) where
  toFun := (⇑)
  __ := AddSubgroup.subtype _

@[simp]
/-
**lp.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFnAddMonoidHom_apply (x : lp E p) : coeFnAddMonoidHom E p x = ⇑x
参数：x : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFnAddMonoidHom_apply (x : lp E p) : coeFnAddMonoidHom E p x = ⇑x := rfl
/-
**lp.coeFn_sum** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_sum {ι : Type*} (f : ι -> lp E p) (s : Finset ι) : ⇑(∑ i in s, f i) 
= ∑ i in s, ⇑(f i)
参数：f : ι -> lp E p；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.val_finsetSum`：∀ {ι : Type u_3} {G : Type u_4} [inst : AddCo
mmGroup G] (H : AddSubgroup G) (f : ι → ↥H) (s : Finset ι),   ↑(∑ i ∈ s, f i) = 
∑ i ∈ s, ↑(f i)
-/
theorem coeFn_sum {ι : Type*} (f : ι → lp E p) (s : Finset ι) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  (lp E p).val_finsetSum f s

@[simp]
/-
**lp.coeFn_sub** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_sub (f g : lp E p) : ⇑(f - g) = f - g
参数：f g : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_sub (f g : lp E p) : ⇑(f - g) = f - g :=
  rfl
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Norm (lp E p) where
  norm f :=
    if hp : p = 0 then by
      subst hp
      exact ((lp.memℓp f).finite_dsupport.toFinset.card : ℝ)
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
/-
**lp.norm_eq_card_dsupport** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.memℓp f).finite_dsupport.to
Finset.card
参数：f : lp E 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.memℓp f).finite_dsupport.toFinset.card :=
  dif_pos rfl
/-
**lp.norm_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖
参数：f : lp E ∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖ := rfl
/-
**lp.isLUB_norm** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range fun i => ‖f i‖) ‖f
‖
参数：f : lp E ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_eq_ciSup`：norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
theorem isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range fun i => ‖f i‖) ‖f‖ := by
  rw [lp.norm_eq_ciSup]
  exact isLUB_ciSup (lp.memℓp f)
/-
**lp.norm_eq_tsum_rpow** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p) : ‖f‖ = (∑' i, ‖f i‖ ^ 
p.toReal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  dsimp [norm]
  rw [ENNReal.toReal_pos_iff] at hp
  rw [dif_neg hp.1.ne', if_neg hp.2.ne]
/-
**lp.norm_rpow_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p) : ‖f‖ ^ p.toReal = ∑' i
, ‖f i‖ ^ p.toReal
参数：hp : 0 < p.toReal；f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
（共 38 条，此处仅展示前 30 条）
-/
theorem norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal := by
  rw [norm_eq_tsum_rpow hp, ← Real.rpow_mul]
  · field_simp
    simp
  positivity
/-
**lp.hasSum_norm** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (fun i => ‖f i‖ ^ p.
toReal) (‖f‖ ^ p.toReal)
参数：hp : 0 < p.toReal；f : lp E p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_rpow_eq_tsum`：norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
theorem hasSum_norm (hp : 0 < p.toReal) (f : lp E p) :
    HasSum (fun i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal) := by
  rw [norm_rpow_eq_tsum hp]
  exact ((lp.memℓp f).summable hp).hasSum

/-- The sequence of norms of `x : lp E p` as a term of `ℓ^p(α, ℝ)`. Here `E : α → Type*`
is a dependent type and `ℓ^p(α, ℝ)` is the non-dependent `ℝ`-valued `lp` space. -/
@[simps]
/-
**lp.toNorm** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：toNorm {p : Real>=0∞} (x : lp E p) : ℓ^p(α, Real)
参数：x : lp E p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence of norms of `x : lp E p` as a term of `ℓ^p(α, ℝ)`. Here `E : α → Ty
pe*`
is a dependent type and `ℓ^p(α, ℝ)` is the non-dependent `ℝ`-valued `lp` space.
-/
def toNorm {p : ℝ≥0∞} (x : lp E p) : ℓ^p(α, ℝ) :=
  ⟨fun i ↦ ‖x i‖, lp.memℓp x |>.norm⟩
/-
**lp.norm_toNorm** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_toNorm {p : Real>=0∞} {x : lp E p} : ‖toNorm x‖ = ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lp.toNorm_coe`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → Nor
medAddCommGroup (E i)] {p : ENNReal} (x : ↥(lp E p)) (i : α),   ↑(lp.toNorm x) i
 = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma norm_toNorm {p : ℝ≥0∞} {x : lp E p} :
    ‖toNorm x‖ = ‖x‖ := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · simp [norm_eq_card_dsupport]
  · simp [norm_eq_ciSup]
  · simp [norm_eq_tsum_rpow hp]
/-
**lp.norm_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `lp.norm_eq_ciSup`：norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport f]
  · rcases isEmpty_or_nonempty α with _i | _i
    · rw [lp.norm_eq_ciSup]
      simp [Real.iSup_of_isEmpty]
    inhabit α
    exact (norm_nonneg (f default)).trans ((lp.isLUB_norm f).1 ⟨default, rfl⟩)
  · rw [lp.norm_eq_tsum_rpow hp f]
    exact Real.rpow_nonneg (tsum_nonneg fun i ↦ by positivity) _

@[simp]
/-
**lp.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_zero : ‖(0 : lp E p)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.iSup_const_zero`：iSup_const_zero : ⨆ _ : ι, (0 : Real) = 0
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem norm_zero : ‖(0 : lp E p)‖ = 0 := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp [lp.norm_eq_card_dsupport]
  · simp [lp.norm_eq_ciSup]
  · rw [lp.norm_eq_tsum_rpow hp]
    have hp' : 1 / p.toReal ≠ 0 := one_div_ne_zero hp.ne'
    simpa [Real.zero_rpow hp.ne'] using Real.zero_rpow hp'
/-
**lp.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_eq_zero_iff {f : lp E p} : ‖f‖ = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_eq_zero_iff_of_nonneg`：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x
) : x ^ y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `hasSum_zero_iff_of_nonneg`：∀ {ι : Type u_4} {α : Type u_5} {L : Summatio
nFilter ι} [inst : AddCommMonoid α] [inst_1 : PartialOrder α]   [IsOrderedAddMon
oid α] [inst_3 …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
（共 34 条，此处仅展示前 30 条）
-/
theorem norm_eq_zero_iff {f : lp E p} : ‖f‖ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; exact norm_zero⟩
  rcases p.trichotomy with (rfl | rfl | hp)
  · ext i
    have : { i : α | ¬f i = 0 } = ∅ := by simpa [lp.norm_eq_card_dsupport f] using! h
    have : ¬¬f i = 0 := Set.eq_empty_iff_forall_notMem.mp this i
    tauto
  · rcases isEmpty_or_nonempty α with _i | _i
    · simp [eq_iff_true_of_subsingleton]
    have H : IsLUB (Set.range fun i => ‖f i‖) 0 := by simpa [h] using! lp.isLUB_norm f
    ext i
    have : ‖f i‖ = 0 := le_antisymm (H.1 ⟨i, rfl⟩) (norm_nonneg _)
    simpa using! this
  · have hf : HasSum (fun i : α => ‖f i‖ ^ p.toReal) 0 := by
      have := lp.hasSum_norm hp f
      rwa [h, Real.zero_rpow hp.ne'] at this
    have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i ↦ by positivity
    rw [hasSum_zero_iff_of_nonneg this] at hf
    ext i
    have : f i = 0 ∧ p.toReal ≠ 0 := by
      simpa [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (f i))] using! congr_fun hf i
    exact this.1
/-
**lp.eq_zero_iff_coeFn_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：eq_zero_iff_coeFn_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.ext_iff`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i
 : α) → NormedAddCommGroup (E i)] {f g : ↥(lp E p)},   f = g ↔ ↑f = ↑g
· 使用定理 `lp.coeFn_zero`：coeFn_zero : ⇑(0 : lp E p) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_zero_iff_coeFn_eq_zero {f : lp E p} : f = 0 ↔ ⇑f = 0 := by
  rw [lp.ext_iff, coeFn_zero]

@[simp]
/-
**lp.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `lp.eq_zero'`：eq_zero' [IsEmpty α] (f : lp E p) : f = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `lp.norm_zero`：norm_zero : ‖(0 : lp E p)‖ = 0
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `Real.rpow_left_injOn`：rpow_left_injOn {x : Real} (hx : x != 0) : InjOn (
fun y : Real => y ^ x) { y : Real | 0 <= y }
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
-/
theorem norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · simp only [norm_eq_card_dsupport, coeFn_neg, Pi.neg_apply, ne_eq, neg_eq_zero]
  · cases isEmpty_or_nonempty α
    · simp only [lp.eq_zero' f, neg_zero, norm_zero]
    apply (lp.isLUB_norm (-f)).unique
    simpa only [coeFn_neg, Pi.neg_apply, norm_neg] using lp.isLUB_norm f
  · suffices ‖-f‖ ^ p.toReal = ‖f‖ ^ p.toReal by
      exact Real.rpow_left_injOn hp.ne' (norm_nonneg' _) (norm_nonneg' _) this
    apply (lp.hasSum_norm hp (-f)).unique
    simpa only [coeFn_neg, Pi.neg_apply, _root_.norm_neg] using lp.hasSum_norm hp f
/-
**lp.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：normedAddCommGroup [hp : Fact (1 <= p)] : NormedAddCommGroup (lp E p)
参数：1 <= p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.norm_zero`：norm_zero : ‖(0 : lp E p)‖ = 0
· 使用定理 `lp.norm_neg`：norm_neg ⦃f : lp E p⦄ : ‖-f‖ = ‖f‖
-/
instance normedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (lp E p) :=
  fast_instance% AddGroupNorm.toNormedAddCommGroup
    { toFun := norm
      map_zero' := norm_zero
      neg' := norm_neg
      add_le' := fun f g => by
        rcases p.dichotomy with (rfl | hp')
        · cases isEmpty_or_nonempty α
          · simp only [lp.eq_zero' f, zero_add, norm_zero, le_refl]
          refine (lp.isLUB_norm (f + g)).2 ?_
          rintro x ⟨i, rfl⟩
          refine le_trans ?_ (add_mem_upperBounds_add
            (lp.isLUB_norm f).1 (lp.isLUB_norm g).1 ⟨_, ⟨i, rfl⟩, _, ⟨i, rfl⟩, rfl⟩)
          exact norm_add_le (f i) (g i)
        · have hp'' : 0 < p.toReal := zero_lt_one.trans_le hp'
          have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
          have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
          have hf₂ := lp.hasSum_norm hp'' f
          have hg₂ := lp.hasSum_norm hp'' g
          -- apply Minkowski's inequality
          obtain ⟨C, hC₁, hC₂, hCfg⟩ :=
            Real.Lp_add_le_hasSum_of_nonneg hp' hf₁ hg₁ (norm_nonneg' _) (norm_nonneg' _) hf₂ hg₂
          refine le_trans ?_ hC₂
          rw [← Real.rpow_le_rpow_iff (norm_nonneg' (f + g)) hC₁ hp'']
          refine hasSum_le ?_ (lp.hasSum_norm hp'' (f + g)) hCfg
          intro i
          gcongr
          apply norm_add_le
      eq_zero_of_map_eq_zero' := fun _ => norm_eq_zero_iff.1 }

-- TODO: define an `ENNReal` version of `HolderConjugate`, and then express this inequality
-- in a better version which also covers the case `p = 1, q = ∞`.
/-- Hölder inequality -/
/-
**lp.tsum_mul_le_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.toReal →     ∀ (f : ↥(lp E p
)) (g : ↥(lp E q)), (Summable fun i => ‖↑f i‖ * ‖↑g i‖) ∧ ∑' (i : α), ‖↑f i‖ * ‖
↑g i‖ ≤ ‖f‖ * ‖g‖
参数：i : α；E i；f : ↥(lp E p)；g : ↥(lp E q)；Summable fun i => ‖↑f i‖ * ‖↑g i‖；i : α
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg`：inner_le_Lp_mul_Lq_hasSum_of_n
onneg (hpq : p.HolderConjugate q) {A B : Real} (hA : 0 <= A) (hB : 0 <= B) (hf :
 forall i, 0 <= f i) (hg : for…
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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

--- 原说明 ---
Hölder inequality
-/
protected theorem tsum_mul_le_mul_norm {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) :
    (Summable fun i => ‖f i‖ * ‖g i‖) ∧ ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ := by
  have hf₁ : ∀ i, 0 ≤ ‖f i‖ := fun i => norm_nonneg _
  have hg₁ : ∀ i, 0 ≤ ‖g i‖ := fun i => norm_nonneg _
  have hf₂ := lp.hasSum_norm hpq.pos f
  have hg₂ := lp.hasSum_norm hpq.symm.pos g
  obtain ⟨C, -, hC', hC⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq (norm_nonneg' _) (norm_nonneg' _) hf₁ hg₁ hf₂ hg₂
  rw [← hC.tsum_eq] at hC'
  exact ⟨hC.summable, hC'⟩
/-
**lp.summable_mul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.toReal → ∀ (f : ↥(lp E p)) (
g : ↥(lp E q)), Summable fun i => ‖↑f i‖ * ‖↑g i‖
参数：i : α；E i；f : ↥(lp E p)；g : ↥(lp E q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lp.tsum_mul_le_mul_norm`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i 
: α) → NormedAddCommGroup (E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.t
oReal →     ∀…
-/
protected theorem summable_mul {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : Summable fun i => ‖f i‖ * ‖g i‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).1
/-
**lp.tsum_mul_le_mul_norm'** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.toReal → ∀ (f : ↥(lp E p)) (
g : ↥(lp E q)), ∑' (i : α), ‖↑f i‖ * ‖↑g i‖ ≤ ‖f‖ * ‖g‖
参数：i : α；E i；f : ↥(lp E p)；g : ↥(lp E q)；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lp.tsum_mul_le_mul_norm`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i 
: α) → NormedAddCommGroup (E i)] {p q : ENNReal},   p.toReal.HolderConjugate q.t
oReal →     ∀…
-/
protected theorem tsum_mul_le_mul_norm' {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).2

section ComparePointwise

/-
**lp.norm_apply_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i : α) : ‖f i‖ <= ‖f‖
参数：hp : p != 0；f : lp E p；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
· 使用定理 `le_hasSum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst
 : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
-/
theorem norm_apply_le_norm (hp : p ≠ 0) (f : lp E p) (i : α) : ‖f i‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with (rfl | hp')
  · have : Nonempty α := ⟨i⟩
    exact (isLUB_norm f).1 ⟨i, rfl⟩
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i ↦ by positivity
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg' _) hp'']
  convert! le_hasSum (hasSum_norm hp'' f) i fun i _ => this i
/-
**lp.lipschitzWith_one_eval** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：lipschitzWith_one_eval (p : Real>=0∞) [Fact (1 <= p)] (i : α) : LipschitzW
ith 1 (fun x : lp E p => x i)
参数：p : Real>=0∞；1 <= p；i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma lipschitzWith_one_eval (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : α) :
    LipschitzWith 1 (fun x : lp E p ↦ x i) :=
  .mk_one fun _ _ ↦ by
    simp_rw [dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' ..
/-
**lp.sum_rpow_le_norm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) : ∑ 
i in s, ‖f i‖ ^ p.toReal <= ‖f‖ ^ p.toReal
参数：hp : 0 < p.toReal；f : lp E p；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.norm_rpow_eq_tsum`：norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
theorem sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp f]
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i ↦ by positivity
  refine Summable.sum_le_tsum _ (fun i _ => this i) ?_
  exact (lp.memℓp f).summable hp
/-
**lp.norm_le_of_forall_le'** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_le_of_forall_le' [Nonempty α] {f : lp E ∞} (C : Real) (hCf : forall i
, ‖f i‖ <= C) : ‖f‖ <= C
参数：C : Real；hCf : forall i, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
-/
theorem norm_le_of_forall_le' [Nonempty α] {f : lp E ∞} (C : ℝ) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  refine (isLUB_norm f).2 ?_
  rintro - ⟨i, rfl⟩
  exact hCf i
/-
**lp.norm_le_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_le_of_forall_le {f : lp E ∞} {C : Real} (hC : 0 <= C) (hCf : forall i
, ‖f i‖ <= C) : ‖f‖ <= C
参数：hC : 0 <= C；hCf : forall i, ‖f i‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lp.eq_zero'`：eq_zero' [IsEmpty α] (f : lp E p) : f = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `lp.norm_le_of_forall_le'`：norm_le_of_forall_le' [Nonempty α] {f : lp E ∞
} (C : Real) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
-/
theorem norm_le_of_forall_le {f : lp E ∞} {C : ℝ} (hC : 0 ≤ C) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  cases isEmpty_or_nonempty α
  · simpa [eq_zero' f] using hC
  · exact norm_le_of_forall_le' C hCf
/-
**lp.norm_le_of_tsum_le** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_le_of_tsum_le (hp : 0 < p.toReal) {C : Real} (hC : 0 <= C) {f : lp E 
p} (hf : ∑' i, ‖f i‖ ^ p.toReal <= C ^ p.toReal) : ‖f‖ <= C
参数：hp : 0 < p.toReal；hC : 0 <= C；hf : ∑' i, ‖f i‖ ^ p.toReal <= C ^ p.toReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
· 使用定理 `lp.norm_rpow_eq_tsum`：norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal
-/
theorem norm_le_of_tsum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∑' i, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C := by
  rw [← Real.rpow_le_rpow_iff (norm_nonneg' _) hC hp, norm_rpow_eq_tsum hp]
  exact hf
/-
**lp.norm_le_of_forall_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_le_of_forall_sum_le (hp : 0 < p.toReal) {C : Real} (hC : 0 <= C) {f :
 lp E p} (hf : forall s : Finset α, ∑ i in s, ‖f i‖ ^ p.toReal <= C ^ p.toReal) 
: ‖f‖ <= C
参数：hp : 0 < p.toReal；hC : 0 <= C；hf : forall s : Finset α, ∑ i in s, ‖f i‖ ^ p.t
oReal <= C ^ p.toReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.norm_le_of_tsum_le`：norm_le_of_tsum_le (hp : 0 < p.toReal) {C : Real}
 (hC : 0 <= C) {f : lp E p} (hf : ∑' i, ‖f i‖ ^ p.toReal <= C ^ p.toReal) : ‖f‖ 
<= C
· 使用定理 `Summable.tsum_le_of_sum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : Summati
onFilter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : Topologic
alSpace α] [Orde…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
theorem norm_le_of_forall_sum_le (hp : 0 < p.toReal) {C : ℝ} (hC : 0 ≤ C) {f : lp E p}
    (hf : ∀ s : Finset α, ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal) : ‖f‖ ≤ C :=
  norm_le_of_tsum_le hp hC (((lp.memℓp f).summable hp).tsum_le_of_sum_le hf)
/-
**lp.norm_mono** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_mono {F : α -> Type*} [forall i, NormedAddCommGroup (F i)] {p : Real>
=0∞} (hp : p != 0) {x : lp E p} {y : lp F p} (h : forall i, ‖x i‖ <= ‖y i‖) : ‖x
‖ <= ‖y‖
参数：F i；hp : p != 0；h : forall i, ‖x i‖ <= ‖y i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `lp.norm_le_of_forall_sum_le`：norm_le_of_forall_sum_le (hp : 0 < p.toReal
) {C : Real} (hC : 0 <= C) {f : lp E p} (hf : forall s : Finset α, ∑ i in s, ‖f 
i‖ ^ p.toReal <= …
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lp.sum_rpow_le_norm_rpow`：sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f :
 lp E p) (s : Finset α) : ∑ i in s, ‖f i‖ ^ p.toReal <= ‖f‖ ^ p.toReal
-/
lemma norm_mono {F : α → Type*} [∀ i, NormedAddCommGroup (F i)]
    {p : ℝ≥0∞} (hp : p ≠ 0) {x : lp E p} {y : lp F p} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖x‖ ≤ ‖y‖ := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · exact hp rfl |>.elim
  · exact norm_le_of_forall_le (by positivity) fun i ↦ (h i).trans <| norm_apply_le_norm hp y i
  · exact norm_le_of_forall_sum_le hp (norm_nonneg' _) fun s ↦ calc
      ∑ i ∈ s, ‖x i‖ ^ p.toReal
      _ ≤ ∑ i ∈ s, ‖y i‖ ^ p.toReal := by gcongr with i _; exact h i
      _ ≤ ‖y‖ ^ p.toReal := sum_rpow_le_norm_rpow hp y s

end ComparePointwise

section IsBoundedSMul

variable [NormedRing 𝕜] [NormedRing 𝕜']
variable [∀ i, Module 𝕜 (E i)] [∀ i, Module 𝕜' (E i)]

/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module 𝕜 (PreLp E) :=
  inferInstanceAs <| Module 𝕜 (∀ i, E i)
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (PreLp E) :=
  inferInstanceAs <| SMulCommClass 𝕜' 𝕜 (∀ i, E i)
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (PreLp E) :=
  inferInstanceAs <| IsScalarTower 𝕜' 𝕜 (∀ i, E i)
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (PreLp E) :=
  inferInstanceAs <| IsCentralScalar 𝕜 (∀ i, E i)

variable [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜' (E i)]
/-
**lp.mem_lp_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : PreLp E) in lp E p
参数：c : 𝕜；f : lp E p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Memℓp.const_smul`：const_smul {f : forall i, E i} (hf : Memℓp f p) (c : 𝕜
) : Memℓp (c • f) p
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
-/
theorem mem_lp_const_smul (c : 𝕜) (f : lp E p) : c • (f : PreLp E) ∈ lp E p :=
  (lp.memℓp f).const_smul c

variable (𝕜 E p)

/-- The `𝕜`-submodule of elements of `∀ i : α, E i` whose `lp` norm is finite. This is `lp E p`,
with extra structure. -/
/-
**lp._root_.lpSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝕜`-submodule of elements of `∀ i : α, E i` whose `lp` norm is finite. This 
is `lp E p`,
with extra structure.
-/
def _root_.lpSubmodule : Submodule 𝕜 (PreLp E) :=
  { lp E p with smul_mem' := fun c f hf => by simpa using mem_lp_const_smul c ⟨f, hf⟩ }

variable {𝕜 E p}
/-
**lp.coe_lpSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coe_lpSubmodule : (lpSubmodule 𝕜 E p).toAddSubgroup = lp E p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lpSubmodule : (lpSubmodule 𝕜 E p).toAddSubgroup = lp E p :=
  rfl
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module 𝕜 (lp E p) :=
  inferInstanceAs <| Module 𝕜 (lpSubmodule 𝕜 E p)

@[simp]
/-
**lp.coeFn_smul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • ⇑f
参数：c : 𝕜；f : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_smul (c : 𝕜) (f : lp E p) : ⇑(c • f) = c • ⇑f :=
  rfl
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMulCommClass 𝕜' 𝕜 (E i)] : SMulCommClass 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_comm _ _ _⟩
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul 𝕜' 𝕜] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] : IsScalarTower 𝕜' 𝕜 (lp E p) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_assoc _ _ _⟩
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Module 𝕜ᵐᵒᵖ (E i)] [∀ i, IsCentralScalar 𝕜 (E i)] : IsCentralScalar 𝕜 (lp E p) :=
  ⟨fun _ _ => Subtype.ext <| op_smul_eq_smul _ _⟩
/-
**lp.norm_const_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_const_smul_le (hp : p != 0) (c : 𝕜) (f : lp E p) : ‖c • f‖ <= ‖c‖ * ‖
f‖
参数：hp : p != 0；c : 𝕜；f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lp.eq_zero'`：eq_zero' [IsEmpty α] (f : lp E p) : f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsLUB.mul_left`：IsLUB.mul_left {s : Set α} (ha : 0 <= a) (hs : IsLUB s b
) : IsLUB ((fun b => a * b) '' s) (a * b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `lp.isLUB_norm`：isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range f
un i => ‖f i‖) ‖f‖
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lp.norm_nonneg'`：norm_nonneg' (f : lp E p) : 0 <= ‖f‖
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 43 条，此处仅展示前 30 条）
-/
theorem norm_const_smul_le (hp : p ≠ 0) (c : 𝕜) (f : lp E p) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · exact absurd rfl hp
  · cases isEmpty_or_nonempty α
    · simp [lp.eq_zero' f]
    have hfc := (lp.isLUB_norm f).mul_left (norm_nonneg c)
    simp_rw [← Set.range_comp, Function.comp_def] at hfc
    exact norm_le_of_forall_le (by positivity)
      fun i ↦ norm_smul_le c (f i) |>.trans <| hfc.1 ⟨i, rfl⟩
  · let inst : NNNorm (lp E p) := ⟨fun f => ⟨‖f‖, norm_nonneg' _⟩⟩
    have coe_nnnorm : ∀ f : lp E p, ↑‖f‖₊ = ‖f‖ := fun _ => rfl
    suffices ‖c • f‖₊ ^ p.toReal ≤ (‖c‖₊ * ‖f‖₊) ^ p.toReal by
      rwa [NNReal.rpow_le_rpow_iff hp] at this
    clear_value inst
    rw [NNReal.mul_rpow]
    have hLHS := lp.hasSum_norm hp (c • f)
    have hRHS := (lp.hasSum_norm hp f).mul_left (‖c‖ ^ p.toReal)
    simp_rw [← coe_nnnorm, ← _root_.coe_nnnorm, ← NNReal.coe_rpow, ← NNReal.coe_mul,
      NNReal.hasSum_coe] at hRHS hLHS
    refine hasSum_mono hLHS hRHS fun i => ?_
    dsimp only
    rw [← NNReal.mul_rpow, lp.coeFn_smul, Pi.smul_apply]
    gcongr
    apply nnnorm_smul_le
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (lp E p) :=
  IsBoundedSMul.of_norm_smul_le <| norm_const_smul_le (zero_lt_one.trans_le <| Fact.out).ne'

end IsBoundedSMul

section Sum

variable {E : Type*} [NormedAddCommGroup E]

set_option backward.isDefEq.respectTransparency false in
/-
**lp.norm_tsum_le** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：norm_tsum_le (f : ℓ¹(α, E)) : ‖∑' i, f i‖ <= ‖f‖
参数：f : ℓ¹(α, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_tsum_le_tsum_norm`：norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summab
le fun i => ‖f i‖) : ‖∑' i, f i‖ <= ∑' i, ‖f i‖
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Memℓp.summable`：summable (hp : 0 < p.toReal) {f : forall i, E i} (hf : M
emℓp f p) : Summable fun i => ‖f i‖ ^ p.toReal
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_tsum_le (f : ℓ¹(α, E)) :
    ‖∑' i, f i‖ ≤ ‖f‖ := calc
  ‖∑' i, f i‖ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm (.of_norm (by simpa using f.2.summable))
  _ = ‖f‖ := by simp [norm_eq_tsum_rpow]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [CompleteSpace E]

variable (α 𝕜 E) in
/-- Summation (i.e., `tsum`) in `ℓ¹(α, E)` as a continuous linear map. -/
@[simps!]
/-
**lp.tsumCLM** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：tsumCLM : ℓ¹(α, E) ->L[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Summation (i.e., `tsum`) in `ℓ¹(α, E)` as a continuous linear map.
-/
noncomputable def tsumCLM : ℓ¹(α, E) →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun f := ∑' i, f i
      map_add' f g := by
        rw [← Summable.tsum_add]
        exacts [rfl, .of_norm (by simpa using f.2.summable), .of_norm (by simpa using g.2.summable)]
      map_smul' c f := by
        simp only [coeFn_smul]
        exact Summable.tsum_const_smul _ (.of_norm (by simpa using f.2.summable)) }
    1 (fun f ↦ by simpa using norm_tsum_le f)

end Sum

section DivisionRing

variable [NormedDivisionRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]

/-
**lp.norm_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_const_smul (hp : p != 0) {c : 𝕜} (f : lp E p) : ‖c • f‖ = ‖c‖ * ‖f‖
参数：hp : p != 0；f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `lp.norm_zero`：norm_zero : ‖(0 : lp E p)‖ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `lp.norm_const_smul_le`：norm_const_smul_le (hp : p != 0) (c : 𝕜) (f : lp 
E p) : ‖c • f‖ <= ‖c‖ * ‖f‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem norm_const_smul (hp : p ≠ 0) {c : 𝕜} (f : lp E p) : ‖c • f‖ = ‖c‖ * ‖f‖ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm (norm_const_smul_le hp c f) ?_
  have := mul_le_mul_of_nonneg_left (norm_const_smul_le hp c⁻¹ (c • f)) (norm_nonneg c)
  rwa [inv_smul_smul₀ hc, norm_inv, mul_inv_cancel_left₀ (norm_ne_zero_iff.mpr hc)] at this

end DivisionRing

section NormedSpace

variable [NormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

/-
**lp.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：instNormedSpace [Fact (1 <= p)] : NormedSpace 𝕜 (lp E p) where norm_smul_l
e c f
参数：1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (lp E p) where
  norm_smul_le c f := norm_smul_le c f

end NormedSpace

section NormedStarGroup

variable [∀ i, StarAddMonoid (E i)] [∀ i, NormedStarGroup (E i)]

/-
**lp._root_.Mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Memℓp.star_mem {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (star f) p := by
  rcases p.trichotomy with (rfl | rfl | hp)
  · apply memℓp_zero
    simp [hf.finite_dsupport]
  · apply memℓp_infty
    simpa using hf.bddAbove
  · apply memℓp_gen
    simpa using hf.summable hp

@[simp]
/-
**lp._root_.Mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Memℓp.star_iff {f : ∀ i, E i} : Memℓp (star f) p ↔ Memℓp f p :=
  ⟨fun h => star_star f ▸ Memℓp.star_mem h, Memℓp.star_mem⟩
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (lp E p) where
  star f := ⟨(star f : ∀ i, E i), f.property.star_mem⟩

@[simp]
/-
**lp.coeFn_star** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：coeFn_star (f : lp E p) : ⇑(star f) = star (⇑f)
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_star (f : lp E p) : ⇑(star f) = star (⇑f) :=
  rfl

@[simp]
/-
**lp.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)]   [inst_1 : (i : α) → StarAddMonoid (E i)] [inst_2 : ∀ (i : 
α), NormedStarGroup (E i)] (f : ↥(lp E p)) (i : α),   ↑(star f) i = star (↑f i)
参数：i : α；E i；i : α；E i；i : α；E i；f : ↥(lp E p)；i : α；star f；↑f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem star_apply (f : lp E p) (i : α) : star f i = star (f i) :=
  rfl
/-
**lp.instInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：instInvolutiveStar : InvolutiveStar (lp E p) where star_involutive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveStar : InvolutiveStar (lp E p) where
  star_involutive x := by simp [star]
/-
**lp.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：instStarAddMonoid : StarAddMonoid (lp E p) where star_add _f _g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid : StarAddMonoid (lp E p) where
  star_add _f _g := ext <| star_add (R := ∀ i, E i) _ _
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hp : Fact (1 ≤ p)] : NormedStarGroup (lp E p) where
  norm_star_le f := le_of_eq <| by
    rcases p.trichotomy with (rfl | rfl | h)
    · exfalso
      have := ENNReal.toReal_mono ENNReal.zero_ne_top hp.elim
      norm_num at this
    · simp only [lp.norm_eq_ciSup, lp.star_apply, norm_star]
    · simp only [lp.norm_eq_tsum_rpow h, lp.star_apply, norm_star]

variable [Star 𝕜] [NormedRing 𝕜]
variable [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, StarModule 𝕜 (E i)]
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule 𝕜 (lp E p) where
  star_smul _r _f := ext <| star_smul (R := 𝕜) (A := ∀ i, E i) _ _

end NormedStarGroup

section NonUnitalNormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NonUnitalNormedRing (B i)]

/-
**lp._root_.Mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Memℓp.infty_mul {f g : ∀ i, B i} (hf : Memℓp f ∞) (hg : Memℓp g ∞) :
    Memℓp (f * g) ∞ := by
  rw [memℓp_infty_iff]
  obtain ⟨⟨Cf, hCf⟩, ⟨Cg, hCg⟩⟩ := hf.bddAbove, hg.bddAbove
  refine ⟨Cf * Cg, ?_⟩
  rintro _ ⟨i, rfl⟩
  calc
    ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le (f i) (g i)
    _ ≤ Cf * Cg :=
      mul_le_mul (hCf ⟨i, rfl⟩) (hCg ⟨i, rfl⟩) (norm_nonneg _)
        ((norm_nonneg _).trans (hCf ⟨i, rfl⟩))
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (lp B ∞) where
  mul f g := ⟨HMul.hMul (α := ∀ i, B i) _ _, f.property.infty_mul g.property⟩

@[simp]
/-
**lp.infty_coeFn_mul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：infty_coeFn_mul (f g : lp B ∞) : ⇑(f * g) = ⇑f * ⇑g
参数：f g : lp B ∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_coeFn_mul (f g : lp B ∞) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl
/-
**lp.nonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：nonUnitalRing : NonUnitalRing (lp B ∞)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalRing : NonUnitalRing (lp B ∞) := fast_instance%
  Function.Injective.nonUnitalRing lp.coeFun.coe Subtype.coe_injective (lp.coeFn_zero B ∞)
    lp.coeFn_add infty_coeFn_mul lp.coeFn_neg lp.coeFn_sub (fun _ _ => rfl) fun _ _ => rfl
/-
**lp.nonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：nonUnitalNormedRing : NonUnitalNormedRing (lp B ∞)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
-/
instance nonUnitalNormedRing : NonUnitalNormedRing (lp B ∞) :=
  { lp.nonUnitalRing, lp.normedAddCommGroup with
    norm_mul_le f g := lp.norm_le_of_forall_le (by positivity) fun i ↦ calc
      ‖(f * g) i‖ ≤ ‖f i‖ * ‖g i‖ := norm_mul_le _ _
      _ ≤ ‖f‖ * ‖g‖ := mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero f i)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero g i) (norm_nonneg _) (norm_nonneg _) }
/-
**lp.nonUnitalNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：nonUnitalNormedCommRing {B : I -> Type*} [forall i, NonUnitalNormedCommRin
g (B i)] : NonUnitalNormedCommRing (lp B ∞) where mul_comm _ _
参数：B i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNormedCommRing {B : I → Type*} [∀ i, NonUnitalNormedCommRing (B i)] :
    NonUnitalNormedCommRing (lp B ∞) where
  mul_comm _ _ := ext <| mul_comm ..

-- we also want a `NonUnitalNormedCommRing` instance, but this has to wait for https://github.com/leanprover-community/mathlib3/pull/13719
/-
**lp.infty_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：infty_isScalarTower {𝕜} [NormedRing 𝕜] [forall i, Module 𝕜 (B i)] [forall 
i, IsBoundedSMul 𝕜 (B i)] [forall i, IsScalarTower 𝕜 (B i) (B i)] : IsScalarTowe
r 𝕜 (lp B ∞) (lp B ∞)
参数：B i；B i；B i；B i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance infty_isScalarTower {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, IsBoundedSMul 𝕜 (B i)]
    [∀ i, IsScalarTower 𝕜 (B i) (B i)] : IsScalarTower 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_assoc (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩
/-
**lp.infty_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：infty_smulCommClass {𝕜} [NormedRing 𝕜] [forall i, Module 𝕜 (B i)] [forall 
i, IsBoundedSMul 𝕜 (B i)] [forall i, SMulCommClass 𝕜 (B i) (B i)] : SMulCommClas
s 𝕜 (lp B ∞) (lp B ∞)
参数：B i；B i；B i；B i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance infty_smulCommClass {𝕜} [NormedRing 𝕜] [∀ i, Module 𝕜 (B i)] [∀ i, IsBoundedSMul 𝕜 (B i)]
    [∀ i, SMulCommClass 𝕜 (B i) (B i)] : SMulCommClass 𝕜 (lp B ∞) (lp B ∞) :=
  ⟨fun r f g => lp.ext <| smul_comm (N := ∀ i, B i) (α := ∀ i, B i) r (⇑f) (⇑g)⟩

section StarRing

variable [∀ i, StarRing (B i)] [∀ i, NormedStarGroup (B i)]

/-
**lp.inftyStarRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyStarRing : StarRing (lp B ∞)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inftyStarRing : StarRing (lp B ∞) :=
  { lp.instStarAddMonoid with
    star_mul := fun _f _g => ext <| star_mul (R := ∀ i, B i) _ _ }
/-
**lp.inftyCStarRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyCStarRing [forall i, CStarRing (B i)] : CStarRing (lp B ∞) where norm
_mul_self_le f
参数：B i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
-/
instance inftyCStarRing [∀ i, CStarRing (B i)] : CStarRing (lp B ∞) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]
    refine lp.norm_le_of_forall_le ‖star f * f‖.sqrt_nonneg fun i => ?_
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (star f * f) i

end StarRing

end NonUnitalNormedRing

section NormedRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedRing (B i)]

/-
**lp._root_.PreLp.ring** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.PreLp.ring : Ring (PreLp B) :=
  inferInstanceAs (Ring (∀ i, B i))

variable [∀ i, NormOneClass (B i)]
/-
**lp._root_.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.one_memℓp_infty : Memℓp (1 : ∀ i, B i) ∞ :=
  ⟨1, by rintro i ⟨i, rfl⟩; exact norm_one.le⟩

variable (B) in
/-- The `𝕜`-subring of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
/-
**lp._root_.lpInftySubring** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝕜`-subring of elements of `∀ i : α, B i` whose `lp` norm is finite. This is
 `lp E ∞`,
with extra structure.
-/
def _root_.lpInftySubring : Subring (PreLp B) :=
  { lp B ∞ with
    carrier := { f | Memℓp f ∞ }
    one_mem' := one_memℓp_infty
    mul_mem' := Memℓp.infty_mul }
/-
**lp.inftyRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyRing : Ring (lp B ∞)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inftyRing : Ring (lp B ∞) :=
  inferInstanceAs <| Ring (lpInftySubring B)
/-
**lp._root_.Mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Memℓp.infty_pow {f : ∀ i, B i} (hf : Memℓp f ∞) (n : ℕ) : Memℓp (f ^ n) ∞ :=
  (lpInftySubring B).pow_mem hf n
/-
**lp._root_.natCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.natCast_memℓp_infty (n : ℕ) : Memℓp (n : ∀ i, B i) ∞ :=
  natCast_mem (lpInftySubring B) n
/-
**lp._root_.intCast_mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.intCast_memℓp_infty (z : ℤ) : Memℓp (z : ∀ i, B i) ∞ :=
  intCast_mem (lpInftySubring B) z

@[simp]
/-
**lp.infty_coeFn_one** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：infty_coeFn_one : ⇑(1 : lp B ∞) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_coeFn_one : ⇑(1 : lp B ∞) = 1 :=
  rfl

@[simp]
/-
**lp.infty_coeFn_pow** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：infty_coeFn_pow (f : lp B ∞) (n : Nat) : ⇑(f ^ n) = (⇑f) ^ n
参数：f : lp B ∞；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_coeFn_pow (f : lp B ∞) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[simp]
/-
**lp.infty_coeFn_natCast** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：infty_coeFn_natCast (n : Nat) : ⇑(n : lp B ∞) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_coeFn_natCast (n : ℕ) : ⇑(n : lp B ∞) = n :=
  rfl

@[simp]
/-
**lp.infty_coeFn_intCast** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：infty_coeFn_intCast (z : Int) : ⇑(z : lp B ∞) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_coeFn_intCast (z : ℤ) : ⇑(z : lp B ∞) = z :=
  rfl
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty I] : NormOneClass (lp B ∞) where
  norm_one := by simp_rw [lp.norm_eq_ciSup, infty_coeFn_one, Pi.one_apply, norm_one, ciSup_const]
/-
**lp.inftyNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyNormedRing : NormedRing (lp B ∞)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inftyNormedRing : NormedRing (lp B ∞) :=
  { lp.inftyRing, lp.nonUnitalNormedRing with }

end NormedRing

section NormedCommRing

variable {I : Type*} {B : I → Type*} [∀ i, NormedCommRing (B i)] [∀ i, NormOneClass (B i)]

/-
**lp.inftyNormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyNormedCommRing : NormedCommRing (lp B ∞) where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inftyNormedCommRing : NormedCommRing (lp B ∞) where
  mul_comm := mul_comm

end NormedCommRing

section Algebra

variable {I : Type*} {B : I → Type*}
variable [NormedField 𝕜] [∀ i, NormedRing (B i)] [∀ i, NormedAlgebra 𝕜 (B i)]

/-
**lp._root_.PreLp.algebra** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.PreLp.algebra : Algebra 𝕜 (PreLp B) :=
  inferInstanceAs <| Algebra 𝕜 (∀ i, B i)

variable [∀ i, NormOneClass (B i)]
/-
**lp._root_.algebraMap_mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.algebraMap_memℓp_infty (k : 𝕜) : Memℓp (algebraMap 𝕜 (∀ i, B i) k) ∞ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (one_memℓp_infty.const_smul k : Memℓp (k • (1 : ∀ i, B i)) ∞)

variable (𝕜 B)

/-- The `𝕜`-subalgebra of elements of `∀ i : α, B i` whose `lp` norm is finite. This is `lp E ∞`,
with extra structure. -/
/-
**lp._root_.lpInftySubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝕜`-subalgebra of elements of `∀ i : α, B i` whose `lp` norm is finite. This
 is `lp E ∞`,
with extra structure.
-/
def _root_.lpInftySubalgebra : Subalgebra 𝕜 (PreLp B) :=
  { lpInftySubring B with
    carrier := { f | Memℓp f ∞ }
    algebraMap_mem' := algebraMap_memℓp_infty }

variable {𝕜 B}
/-
**lp.** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra 𝕜 (lp B ∞) := inferInstanceAs <| Algebra 𝕜 (lpInftySubalgebra 𝕜 B)
/-
**lp.inftyNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：inftyNormedAlgebra : NormedAlgebra 𝕜 (lp B ∞) where norm_smul_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inftyNormedAlgebra : NormedAlgebra 𝕜 (lp B ∞) where
  norm_smul_le := norm_smul_le

end Algebra

section Single

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)]
variable [DecidableEq α]

/-- The element of `lp E p` which is `a : E i` at the index `i`, and zero elsewhere. -/
/-
**lp.single** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：{α : Type u_3} →   {E : α → Type u_4} →     [inst : (i : α) → NormedAddCom
mGroup (E i)] → [DecidableEq α] → (p : ENNReal) → (i : α) → E i → ↥(lp E p)
参数：i : α；E i；p : ENNReal；i : α；lp E p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element of `lp E p` which is `a : E i` at the index `i`, and zero elsewhere.
-/
protected def single (p) (i : α) (a : E i) : lp E p :=
  ⟨Pi.single i a, by
    refine (memℓp_zero ?_).of_exponent_ge zero_le
    refine (Set.finite_singleton i).subset ?_
    intro j
    simp only [Set.mem_singleton_iff, Ne,
      Set.mem_ofPred_eq]
    rw [not_imp_comm]
    intro h
    exact Pi.single_eq_of_ne h _⟩

@[norm_cast]
/-
**lp.coeFn_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i), ↑(lp.single p 
i a) = Pi.single i a
参数：i : α；E i；p : ENNReal；i : α；a : E i；lp.single p i a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coeFn_single (p) (i : α) (a : E i) :
    ⇑(lp.single p i a) = Pi.single i a := rfl

@[simp]
/-
**lp.single_apply** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i) (j : α), ↑(lp.s
ingle p i a) j = Pi.single i a j
参数：i : α；E i；p : ENNReal；i : α；a : E i；j : α；lp.single p i a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem single_apply (p) (i : α) (a : E i) (j : α) :
    lp.single p i a j = Pi.single i a j :=
  rfl
/-
**lp.single_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i), ↑(lp.single p 
i a) i = a
参数：i : α；E i；p : ENNReal；i : α；a : E i；lp.single p i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
protected theorem single_apply_self (p) (i : α) (a : E i) : lp.single p i a i = a :=
  Pi.single_eq_same _ _
/-
**lp.single_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i) {j : α}, j ≠ i 
→ ↑(lp.single p i a) j = 0
参数：i : α；E i；p : ENNReal；i : α；a : E i；lp.single p i a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
protected theorem single_apply_ne (p) (i : α) (a : E i) {j : α} (hij : j ≠ i) :
    lp.single p i a j = 0 :=
  Pi.single_eq_of_ne hij _

@[simp]
/-
**lp.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α), lp.single p i 0 = 0
参数：i : α；E i；p : ENNReal；i : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0
-/
protected theorem single_zero (p) (i : α) :
    lp.single p i (0 : E i) = 0 :=
  ext <| Pi.single_zero _

@[simp]
/-
**lp.single_add** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a b : E i), lp.single p 
i (a + b) = lp.single p i a + lp.single p i b
参数：i : α；E i；p : ENNReal；i : α；a b : E i；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `Pi.single_add`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddZeroClass (f i)] (i : I) (x y : f i),   Pi.single i (x + y)
 = …
-/
protected theorem single_add (p) (i : α) (a b : E i) :
    lp.single p i (a + b) = lp.single p i a + lp.single p i b :=
  ext <| Pi.single_add _ _ _

/-- `single` as an `AddMonoidHom`. -/
@[simps]
/-
**lp.singleAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：singleAddMonoidHom (p) (i : α) : E i ->+ lp E p where toFun
参数：p；i : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `lp.single_zero`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → No
rmedAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α), lp.sin
gle …
· 使用定理 `lp.single_add`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → Nor
medAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a b : E
 i)…

--- 原说明 ---
`single` as an `AddMonoidHom`.
-/
def singleAddMonoidHom (p) (i : α) : E i →+ lp E p where
  toFun := lp.single p i
  map_zero' := lp.single_zero _ _
  map_add' := lp.single_add _ _

@[simp]
/-
**lp.single_neg** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i), lp.single p i 
(-a) = -lp.single p i a
参数：i : α；E i；p : ENNReal；i : α；a : E i；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `Pi.single_neg`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddGroup (f i)] (i : I) (x : f i),   Pi.single i (-x) = -Pi.si
ngl…
-/
protected theorem single_neg (p) (i : α) (a : E i) : lp.single p i (-a) = -lp.single p i a :=
  ext <| Pi.single_neg _ _

@[simp]
/-
**lp.single_sub** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → NormedAddCommGroup (
E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a b : E i), lp.single p 
i (a - b) = lp.single p i a - lp.single p i b
参数：i : α；E i；p : ENNReal；i : α；a b : E i；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `Pi.single_sub`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddGroup (f i)] (i : I) (x y : f i),   Pi.single i (x - y) = P
i.s…
-/
protected theorem single_sub (p) (i : α) (a b : E i) :
    lp.single p i (a - b) = lp.single p i a - lp.single p i b :=
  ext <| Pi.single_sub _ _ _

@[simp]
/-
**lp.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → Norme
dAddCommGroup (E i)] [inst_1 : NormedRing 𝕜]   [inst_2 : (i : α) → _root_.Module
 𝕜 (E i)] [inst_3 : ∀ (i : α), IsBoundedSMul 𝕜 (E i)] [inst_4 : DecidableEq α]  
 (p : ENNReal) (i : α) (c : 𝕜) (a : E i), lp.single p i (c • a) = c • lp.single 
p i a
参数：i : α；E i；i : α；E i；i : α；E i；p : ENNReal；i : α；c : 𝕜；a : E i；c • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `Pi.single_smul`：single_smul {α} [Monoid α] [forall i, AddMonoid <| f i] 
[forall i, DistribMulAction α <| f i] [DecidableEq I] (i : I) (r : α) (x : f i) 
: si…
-/
protected theorem single_smul (p) (i : α) (c : 𝕜) (a : E i) :
    lp.single p i (c • a) = c • lp.single p i a :=
  ext <| Pi.single_smul _ _ _

/-- `single` as a `LinearMap`. -/
@[simps]
/-
**lp.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：lsingle (p) (i : α) : E i ->ₗ[𝕜] lp E p where toFun
参数：p；i : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `lp.single_smul`：∀ {𝕜 : Type u_1} {α : Type u_3} {E : α → Type u_4} [inst
 : (i : α) → NormedAddCommGroup (E i)] [inst_1 : NormedRing 𝕜]   [inst_2 : (i : 
α) →…

--- 原说明 ---
`single` as a `LinearMap`.
-/
def lsingle (p) (i : α) : E i →ₗ[𝕜] lp E p where
  toFun := lp.single p i
  __ := singleAddMonoidHom p i
  map_smul' := lp.single_smul p i

/-- The basis for `ℓ⁰(α, 𝕜)` given by `lp.single`. -/
@[simps repr_apply]
/-
**lp.zeroBasis** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：zeroBasis : Module.Basis α 𝕜 ℓ⁰(α, 𝕜) where repr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis for `ℓ⁰(α, 𝕜)` given by `lp.single`.
-/
noncomputable def zeroBasis : Module.Basis α 𝕜 ℓ⁰(α, 𝕜) where
  repr :=
    { toFun x := .ofSupportFinite ⇑x <| memℓp_zero_iff.mp x.2
      invFun x := ⟨⇑x, memℓp_zero_iff.mpr x.hasFiniteSupport⟩
      map_add' _ _ := Finsupp.ext fun _ ↦ rfl
      map_smul' _ _ := Finsupp.ext fun _ ↦ rfl
      left_inv _ := rfl
      right_inv _ := Finsupp.ext fun _ ↦ rfl }

set_option backward.isDefEq.respectTransparency false in
/-
**lp.zeroBasis_apply** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：zeroBasis_apply (i : α) : zeroBasis i = lp.single 0 i (1 : 𝕜)
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroBasis_apply (i : α) : zeroBasis i = lp.single 0 i (1 : 𝕜) := by
  ext; simp [zeroBasis, Finsupp.single_apply, Pi.single, Function.update, eq_comm]
/-
**lp.norm_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < p.toReal →     ∀ (f : (i : α
) → E i) (s : Finset α), ‖∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal = ∑ i ∈ s, ‖f
 i‖ ^ p.toReal
参数：i : α；E i；f : (i : α) → E i；s : Finset α；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `lp.coeFn_sum`：coeFn_sum {ι : Type*} (f : ι -> lp E p) (s : Finset ι) : ⇑
(∑ i in s, f i) = ∑ i in s, ⇑(f i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `hasSum_sum_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α} {s : Finset β},…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
protected theorem norm_sum_single (hp : 0 < p.toReal) (f : ∀ i, E i) (s : Finset α) :
    ‖∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal = ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  refine (hasSum_norm hp (∑ i ∈ s, lp.single p i (f i))).unique ?_
  simp only [lp.coeFn_single, coeFn_sum, Finset.sum_apply, Finset.sum_pi_single]
  have h : ∀ i ∉ s, ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 := fun i hi ↦ by
    simp [if_neg hi, Real.zero_rpow hp.ne']
  have h' : ∀ i ∈ s, ‖f i‖ ^ p.toReal = ‖ite (i ∈ s) (f i) 0‖ ^ p.toReal := by
    intro i hi
    rw [if_pos hi]
  simpa [Finset.sum_congr rfl h'] using hasSum_sum_of_ne_finset_zero h

@[simp]
/-
**lp.norm_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < p → ∀ (i : α) (x : E i), ‖lp
.single p i x‖ = ‖x‖
参数：i : α；E i；i : α；x : E i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `lp.coeFn_single`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → N
ormedAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E
 i), …
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.rpow_rpow_inv`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y) ^ y⁻¹ = x
-/
protected theorem norm_single (hp : 0 < p) (i : α) (x : E i) : ‖lp.single p i x‖ = ‖x‖ := by
  have : Nonempty α := ⟨i⟩
  induction p with
  | top =>
    simp only [norm_eq_ciSup, lp.coeFn_single]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne' hij, _root_.norm_zero]
        exact norm_nonneg _
    · rw [Pi.single_eq_same]
  | coe p =>
    have : 0 < (p : ℝ≥0∞).toReal := by simpa using hp
    rw [norm_eq_tsum_rpow this, tsum_eq_single i, lp.coeFn_single, one_div,
      Real.rpow_rpow_inv _ this.ne', Pi.single_eq_same]
    · exact norm_nonneg _
    · intro j hji
      rw [lp.coeFn_single, Pi.single_eq_of_ne hji, _root_.norm_zero, Real.zero_rpow this.ne']
/-
**lp.isometry_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：isometry_single [Fact (1 <= p)] (i : α) : Isometry (lp.single (E
参数：1 <= p；i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `lp.norm_single`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst 
: (i : α) → NormedAddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < p → ∀ (i :
 α) …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem isometry_single [Fact (1 ≤ p)] (i : α) : Isometry (lp.single (E := E) p i) :=
  AddMonoidHomClass.isometry_of_norm (lp.singleAddMonoidHom (E := E) p i) fun _ ↦
    lp.norm_single (zero_lt_one.trans_le Fact.out) _ _

variable (p E) in
/-- `lp.single` as a continuous morphism of additive monoids. -/
/-
**lp.singleContinuousAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：singleContinuousAddMonoidHom [Fact (1 <= p)] (i : α) : ContinuousAddMonoid
Hom (E i) (lp E p) where __
参数：1 <= p；i : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lp.single` as a continuous morphism of additive monoids.
-/
def singleContinuousAddMonoidHom [Fact (1 ≤ p)] (i : α) :
    ContinuousAddMonoidHom (E i) (lp E p) where
  __ := singleAddMonoidHom p i
  continuous_toFun := isometry_single i |>.continuous

@[simp]
/-
**lp.singleContinuousAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：singleContinuousAddMonoidHom_apply [Fact (1 <= p)] (i : α) (x : E i) : sin
gleContinuousAddMonoidHom E p i x = lp.single p i x
参数：1 <= p；i : α；x : E i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleContinuousAddMonoidHom_apply [Fact (1 ≤ p)] (i : α) (x : E i) :
    singleContinuousAddMonoidHom E p i x = lp.single p i x :=
  rfl

variable (𝕜 p E) in
/-- `lp.single` as a continuous linear map. -/
/-
**lp.singleContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：singleContinuousLinearMap [Fact (1 <= p)] (i : α) : E i ->L[𝕜] lp E p wher
e __
参数：1 <= p；i : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lp.single` as a continuous linear map.
-/
def singleContinuousLinearMap [Fact (1 ≤ p)] (i : α) : E i →L[𝕜] lp E p where
  __ := lsingle p i
  cont := isometry_single i |>.continuous

@[simp]
/-
**lp.singleContinuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：singleContinuousLinearMap_apply [Fact (1 <= p)] (i : α) (x : E i) : single
ContinuousLinearMap 𝕜 E p i x = lp.single p i x
参数：1 <= p；i : α；x : E i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleContinuousLinearMap_apply [Fact (1 ≤ p)] (i : α) (x : E i) :
    singleContinuousLinearMap 𝕜 E p i x = lp.single p i x :=
  rfl
/-
**lp.norm_sub_norm_compl_sub_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < p.toReal →     ∀ (f : ↥(lp E
 p)) (s : Finset α),       ‖f‖ ^ p.toReal - ‖f - ∑ i ∈ s, lp.single p i (↑f i)‖ 
^ p.toReal = ∑ i ∈ s, ‖↑f i‖ ^ p.toReal
参数：i : α；E i；f : ↥(lp E p)；s : Finset α；↑f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `lp.coeFn_sum`：coeFn_sum {ι : Type*} (f : ι -> lp E p) (s : Finset ι) : ⇑
(∑ i in s, f i) = ∑ i in s, ⇑(f i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `hasSum_sum_of_ne_finset_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α} {s : Finset β},…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
protected theorem norm_sub_norm_compl_sub_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f‖ ^ p.toReal - ‖f - ∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal =
      ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  refine ((hasSum_norm hp f).sub (hasSum_norm hp (f - ∑ i ∈ s, lp.single p i (f i)))).unique ?_
  let F : α → ℝ := fun i => ‖f i‖ ^ p.toReal - ‖(f - ∑ i ∈ s, lp.single p i (f i)) i‖ ^ p.toReal
  have hF : ∀ i ∉ s, F i = 0 := by
    intro i hi
    suffices ‖f i‖ ^ p.toReal - ‖f i - ite (i ∈ s) (f i) 0‖ ^ p.toReal = 0 by
      simpa only [coeFn_sub, coeFn_sum, lp.coeFn_single, Pi.sub_apply, Finset.sum_apply,
        Finset.sum_pi_single, F] using this
    simp only [if_neg hi, sub_zero, sub_self]
  have hF' : ∀ i ∈ s, F i = ‖f i‖ ^ p.toReal := by
    intro i hi
    simp only [F, coeFn_sum, lp.single_apply, if_pos hi, sub_self, coeFn_sub,
      Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single, sub_eq_self]
    simp [Real.zero_rpow hp.ne']
  have : HasSum F (∑ i ∈ s, F i) := hasSum_sum_of_ne_finset_zero hF
  rwa [Finset.sum_congr rfl hF'] at this
/-
**lp.norm_compl_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < p.toReal →     ∀ (f : ↥(lp E
 p)) (s : Finset α),       ‖f - ∑ i ∈ s, lp.single p i (↑f i)‖ ^ p.toReal = ‖f‖ 
^ p.toReal - ∑ i ∈ s, ‖↑f i‖ ^ p.toReal
参数：i : α；E i；f : ↥(lp E p)；s : Finset α；↑f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 37 条，此处仅展示前 30 条）
-/
protected theorem norm_compl_sum_single (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ‖f - ∑ i ∈ s, lp.single p i (f i)‖ ^ p.toReal = ‖f‖ ^ p.toReal - ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
  linarith [lp.norm_sub_norm_compl_sub_single hp f s]

/-- The canonical finitely-supported approximations to an element `f` of `lp` converge to it, in the
`lp` topology. -/
/-
**lp.hasSum_single** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i : α) → Normed
AddCommGroup (E i)] [inst_1 : DecidableEq α]   [inst_2 : Fact (1 ≤ p)], p ≠ ⊤ → 
∀ (f : ↥(lp E p)), HasSum (fun i => lp.single p i (↑f i)) f
参数：i : α；E i；1 ≤ p；f : ↥(lp E p)；fun i => lp.single p i (↑f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasSu
m…
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_iff`：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z < y ^ z ↔ x < y
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lp.single_neg`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → Nor
medAddCommGroup (E i)] [inst_1 : DecidableEq α] (p : ENNReal)   (i : α) (a : E i
), …
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `lp.norm_compl_sum_single`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNRe
al} [inst : (i : α) → NormedAddCommGroup (E i)] [inst_1 : DecidableEq α],   0 < 
p.toReal →    …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The canonical finitely-supported approximations to an element `f` of `lp` conver
ge to it, in the
`lp` topology.
-/
protected theorem hasSum_single [Fact (1 ≤ p)] (hp : p ≠ ⊤) (f : lp E p) :
    HasSum (fun i : α => lp.single p i (f i : E i)) f := by
  have hp₀ : 0 < p := zero_lt_one.trans_le Fact.out
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  have := lp.hasSum_norm hp' f
  rw [HasSum, Metric.tendsto_nhds] at this ⊢
  intro ε hε
  refine (this _ (Real.rpow_pos_of_pos hε p.toReal)).mono ?_
  intro s hs
  rw [← Real.rpow_lt_rpow_iff dist_nonneg (le_of_lt hε) hp']
  rw [dist_comm] at hs
  simp only [dist_eq_norm, Real.norm_eq_abs] at hs ⊢
  have H : ‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal =
      ‖f‖ ^ p.toReal - ∑ i ∈ s, ‖f i‖ ^ p.toReal := by
    simpa only [coeFn_neg, Pi.neg_apply, lp.single_neg, Finset.sum_neg_distrib, neg_sub_neg,
      norm_neg, _root_.norm_neg] using lp.norm_compl_sum_single hp' (-f) s
  rw [← H] at hs
  have : |‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal| =
      ‖(∑ i ∈ s, lp.single p i (f i : E i)) - f‖ ^ p.toReal := by
    simp only [Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm]
  exact this ▸ hs

/-- Two continuous additive maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas]. -/
@[local ext] -- not globally `ext` due to `hp`
/-
**lp.ext_continuousAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：ext_continuousAddMonoidHom {F : Type*} [AddCommMonoid F] [TopologicalSpace
 F] [T2Space F] [Fact (1 <= p)] (hp : p != ⊤) ⦃f g : ContinuousAddMonoidHom (lp 
E p) F⦄ (h : forall i, f.comp (singleContinuousAddMonoidHom E p i) = g.comp (sin
gleContinuousAddMonoidHom E p i)) : f = g
参数：1 <= p；hp : p != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAddMonoidHom.ext`：∀ {A : Type u_2} {B : Type u_3} [inst : AddM
onoid A] [inst_1 : AddMonoid B] [inst_2 : TopologicalSpace A]   [inst_3 : Topolo
gicalSpace B] {f…
· 使用定理 `lp.hasSum_single`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [ins
t : (i : α) → NormedAddCommGroup (E i)] [inst_1 : DecidableEq α]   [inst_2 : Fac
t (1 ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `ContinuousAddMonoidHom.instAddMonoidHomClass`：∀ {A : Type u_2} {B : Type
 u_3} [inst : AddMonoid A] [inst_1 : AddMonoid B] [inst_2 : TopologicalSpace A] 
  [inst_3 : TopologicalSpace B], A…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Two continuous additive maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas].
-/
theorem ext_continuousAddMonoidHom
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F] [T2Space F]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) ⦃f g : ContinuousAddMonoidHom (lp E p) F⦄
    (h : ∀ i,
      f.comp (singleContinuousAddMonoidHom E p i) = g.comp (singleContinuousAddMonoidHom E p i)) :
    f = g := by
  ext x
  have := lp.hasSum_single hp x
  rw [← (this.map f f.continuous).tsum_eq, ← (this.map g g.continuous).tsum_eq]
  congr! 2 with i
  exact DFunLike.congr_fun (h i) (x i)

/-- Two continuous linear maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas]. -/
@[local ext] -- not globally `ext` due to `hp`
/-
**lp.ext_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：ext_continuousLinearMap {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [Topolo
gicalSpace F] [T2Space F] [Fact (1 <= p)] (hp : p != ⊤) ⦃f g : lp E p ->L[𝕜] F⦄ 
(h : forall i, f.comp (singleContinuousLinearMap 𝕜 E p i) = g.comp (singleContin
uousLinearMap 𝕜 E p i)) : f = g
参数：1 <= p；hp : p != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.toContinuousAddMonoidHom_injective`：toContinuousAddM
onoidHom_injective : Function.Injective ((↑) : (M₁ ->SL[σ₁₂] M₂) -> ContinuousAd
dMonoidHom M₁ M₂)
· 使用定理 `lp.ext_continuousAddMonoidHom`：ext_continuousAddMonoidHom {F : Type*} [A
ddCommMonoid F] [TopologicalSpace F] [T2Space F] [Fact (1 <= p)] (hp : p != ⊤) ⦃
f g : ContinuousAdd…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearMap.toContinuousAddMonoidHom_inj`：toContinuousAddMonoidH
om_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : ContinuousAddMonoidHom M₁ M₂) = g ↔ f = g

--- 原说明 ---
Two continuous linear maps from `lp E p` agree if they agree on `lp.single`.

See note [partially-applied ext lemmas].
-/
theorem ext_continuousLinearMap
    {F : Type*} [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [T2Space F]
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) ⦃f g : lp E p →L[𝕜] F⦄
    (h : ∀ i,
      f.comp (singleContinuousLinearMap 𝕜 E p i) = g.comp (singleContinuousLinearMap 𝕜 E p i)) :
    f = g :=
  ContinuousLinearMap.toContinuousAddMonoidHom_injective <|
    ext_continuousAddMonoidHom hp fun i => ContinuousLinearMap.toContinuousAddMonoidHom_inj.2 (h i)

end Single

section OfLE

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] {p q r : ℝ≥0∞}

variable (𝕜 E) in
/-- The `AddSubgroup.inclusion` between `lp` spaces, as a linear map. -/
/-
**lp.linearMapOfLE** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：linearMapOfLE (h : p <= q) : lp E p ->ₗ[𝕜] lp E q where .of_exponent_ge h⟩
 toFun f
参数：h : p <= q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AddSubgroup.inclusion` between `lp` spaces, as a linear map.
-/
def linearMapOfLE (h : p ≤ q) : lp E p →ₗ[𝕜] lp E q where
  toFun f := ⟨f, lp.memℓp f |>.of_exponent_ge h⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
/-
**lp.coe_linearMapOfLE_apply** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：coe_linearMapOfLE_apply (h : p <= q) (f : lp E p) : ⇑(linearMapOfLE 𝕜 E h 
f) = f
参数：h : p <= q；f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma coe_linearMapOfLE_apply (h : p ≤ q) (f : lp E p) :
    ⇑(linearMapOfLE 𝕜 E h f) = f := by
  ext; rfl


@[simp]
/-
**lp.toAddMonoidHom_linearMapOfLE** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：toAddMonoidHom_linearMapOfLE (h : p <= q) : (linearMapOfLE 𝕜 E h).toAddMon
oidHom = AddSubgroup.inclusion (lp.monotone h)
参数：h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `lp.monotone`：∀ {α : Type u_3} {E : α → Type u_4} [inst : (i : α) → Norme
dAddCommGroup (E i)] {p q : ENNReal}, q ≤ p → lp E q ≤ lp E p
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma toAddMonoidHom_linearMapOfLE (h : p ≤ q) :
    (linearMapOfLE 𝕜 E h).toAddMonoidHom = AddSubgroup.inclusion (lp.monotone h) := by
  ext; rfl
/-
**lp.linearMapOfLE_comp** 是 Mathlib 中的一个引理，位于命名空间 `lp`。
形式化陈述：linearMapOfLE_comp (hpq : p <= q) (hqr : q <= r) : (linearMapOfLE 𝕜 E hqr)
.comp (linearMapOfLE 𝕜 E hpq) = linearMapOfLE 𝕜 E (hpq.trans hqr)
参数：hpq : p <= q；hqr : q <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `lp.ext`：ext {f g : lp E p} (h : (f : forall i, E i) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma linearMapOfLE_comp (hpq : p ≤ q) (hqr : q ≤ r) :
    (linearMapOfLE 𝕜 E hqr).comp (linearMapOfLE 𝕜 E hpq) = linearMapOfLE 𝕜 E (hpq.trans hqr) := by
  ext; rfl

end OfLE

section Eval

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] {p q r : ℝ≥0∞}

variable (E p) in
/-- Evaluation at a single coordinate, as a linear map on `lp E p`. -/
@[simps]
/-
**lp.eval** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a single coordinate, as a linear map on `lp E p`.
-/
def evalₗ (i : α) : lp E p →ₗ[𝕜] E i where
  toFun f := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E p) in
/-- Evaluation at a single coordinate, as a continuous linear map on `lp E p`. -/
/-
**lp.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `lp`。
形式化陈述：evalCLM [Fact (1 <= p)] (i : α) : lp E p ->L[𝕜] E i
参数：1 <= p；i : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a single coordinate, as a continuous linear map on `lp E p`.
-/
def evalCLM [Fact (1 ≤ p)] (i : α) : lp E p →L[𝕜] E i :=
  (evalₗ E p i).mkContinuous 1 fun x ↦ by
    have hp : p ≠ 0 := zero_lt_one.trans_le Fact.out |>.ne'
    simpa only [evalₗ_apply, one_mul, ge_iff_le] using norm_apply_le_norm hp x i

end Eval

section Topology

open Filter

open scoped Topology uniformity

set_option backward.isDefEq.respectTransparency false in
/-- The coercion from `lp E p` to `∀ i, E i` is uniformly continuous. -/
/-
**lp.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：uniformContinuous_coe [_i : Fact (1 <= p)] : UniformContinuous (α
参数：1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用引理 `lp.lipschitzWith_one_eval`：lipschitzWith_one_eval (p : Real>=0∞) [Fact (
1 <= p)] (i : α) : LipschitzWith 1 (fun x : lp E p => x i)

--- 原说明 ---
The coercion from `lp E p` to `∀ i, E i` is uniformly continuous.
-/
theorem uniformContinuous_coe [_i : Fact (1 ≤ p)] :
    UniformContinuous (α := lp E p) ((↑) : lp E p → ∀ i, E i) :=
  uniformContinuous_pi.2 fun i ↦ (lipschitzWith_one_eval p i).uniformContinuous

variable {ι : Type*} {l : Filter ι} [Filter.NeBot l]
/-
**lp.norm_apply_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_apply_le_of_tendsto {C : Real} {F : ι -> lp E ∞} (hCF : forallᶠ k in 
l, ‖F k‖ <= C) {f : forall a, E a} (hf : Tendsto (id fun i => F i : ι -> forall 
a, E a) l (𝓝 f)) (a : α) : ‖f a‖ <= C
参数：hCF : forallᶠ k in l, ‖F k‖ <= C；hf : Tendsto (id fun i => F i : ι -> forall 
a, E a) l (𝓝 f)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
-/
theorem norm_apply_le_of_tendsto {C : ℝ} {F : ι → lp E ∞} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (a : α) : ‖f a‖ ≤ C := by
  have : Tendsto (fun k => ‖F k a‖) l (𝓝 ‖f a‖) :=
    (Tendsto.comp (continuous_apply a).continuousAt hf).norm
  refine le_of_tendsto this (hCF.mono ?_)
  intro k hCFk
  exact (norm_apply_le_norm ENNReal.top_ne_zero (F k) a).trans hCFk

variable [_i : Fact (1 ≤ p)]
/-
**lp.sum_rpow_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：sum_rpow_le_of_tendsto (hp : p != ∞) {C : Real} {F : ι -> lp E p} (hCF : f
orallᶠ k in l, ‖F k‖ <= C) {f : forall a, E a} (hf : Tendsto (id fun i => F i : 
ι -> forall a, E a) l (𝓝 f)) (s : Finset α) : ∑ i in s, ‖f i‖ ^ p.toReal <= C ^ 
p.toReal
参数：hp : p != ∞；hCF : forallᶠ k in l, ‖F k‖ <= C；hf : Tendsto (id fun i => F i : 
ι -> forall a, E a) l (𝓝 f)；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.rpow_const`：Continuous.rpow_const (hf : Continuous f) (h : fo
rall x, f x != 0 ∨ 0 <= p) : Continuous fun x => f x ^ p
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `lp.sum_rpow_le_norm_rpow`：sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f :
 lp E p) (s : Finset α) : ∑ i in s, ‖f i‖ ^ p.toReal <= ‖f‖ ^ p.toReal
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem sum_rpow_le_of_tendsto (hp : p ≠ ∞) {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C)
    {f : ∀ a, E a} (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) (s : Finset α) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ C ^ p.toReal := by
  have hp' : p ≠ 0 := (zero_lt_one.trans_le _i.elim).ne'
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp' hp
  let G : (∀ a, E a) → ℝ := fun f => ∑ a ∈ s, ‖f a‖ ^ p.toReal
  have hG : Continuous G := by
    refine continuous_finsetSum s ?_
    intro a _
    have : Continuous fun f : ∀ a, E a => f a := continuous_apply a
    exact this.norm.rpow_const fun _ => Or.inr hp''.le
  refine le_of_tendsto (hG.continuousAt.tendsto.comp hf) ?_
  refine hCF.mono ?_
  intro k hCFk
  refine (lp.sum_rpow_le_norm_rpow hp'' (F k) s).trans ?_
  gcongr

/-- "Semicontinuity of the `lp` norm": If all sufficiently large elements of a sequence in `lp E p`
have `lp` norm `≤ C`, then the pointwise limit, if it exists, also has `lp` norm `≤ C`. -/
/-
**lp.norm_le_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：norm_le_of_tendsto {C : Real} {F : ι -> lp E p} (hCF : forallᶠ k in l, ‖F 
k‖ <= C) {f : lp E p} (hf : Tendsto (id fun i => F i : ι -> forall a, E a) l (𝓝 
f)) : ‖f‖ <= C
参数：hCF : forallᶠ k in l, ‖F k‖ <= C；hf : Tendsto (id fun i => F i : ι -> forall 
a, E a) l (𝓝 f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `lp.norm_apply_le_of_tendsto`：norm_apply_le_of_tendsto {C : Real} {F : ι 
-> lp E ∞} (hCF : forallᶠ k in l, ‖F k‖ <= C) {f : forall a, E a} (hf : Tendsto 
(id fun i => F i …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `lp.norm_le_of_forall_sum_le`：norm_le_of_forall_sum_le (hp : 0 < p.toReal
) {C : Real} (hC : 0 <= C) {f : lp E p} (hf : forall s : Finset α, ∑ i in s, ‖f 
i‖ ^ p.toReal <= …
· 使用定理 `lp.sum_rpow_le_of_tendsto`：sum_rpow_le_of_tendsto (hp : p != ∞) {C : Rea
l} {F : ι -> lp E p} (hCF : forallᶠ k in l, ‖F k‖ <= C) {f : forall a, E a} (hf 
: Tendsto (id f…

--- 原说明 ---
"Semicontinuity of the `lp` norm": If all sufficiently large elements of a seque
nce in `lp E p`
have `lp` norm `≤ C`, then the pointwise limit, if it exists, also has `lp` norm
 `≤ C`.
-/
theorem norm_le_of_tendsto {C : ℝ} {F : ι → lp E p} (hCF : ∀ᶠ k in l, ‖F k‖ ≤ C) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : ‖f‖ ≤ C := by
  obtain ⟨i, hi⟩ := hCF.exists
  have hC : 0 ≤ C := (norm_nonneg _).trans hi
  rcases eq_top_or_lt_top p with (rfl | hp)
  · apply norm_le_of_forall_le hC
    exact norm_apply_le_of_tendsto hCF hf
  · have : 0 < p := zero_lt_one.trans_le _i.elim
    have hp' : 0 < p.toReal := ENNReal.toReal_pos this.ne' hp.ne
    apply norm_le_of_forall_sum_le hp' hC
    exact sum_rpow_le_of_tendsto hp.ne hCF hf

/-- If `f` is the pointwise limit of a bounded sequence in `lp E p`, then `f` is in `lp E p`. -/
/-
**lp.mem** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is the pointwise limit of a bounded sequence in `lp E p`, then `f` is in 
`lp E p`.
-/
theorem memℓp_of_tendsto {F : ι → lp E p} (hF : Bornology.IsBounded (Set.range F)) {f : ∀ a, E a}
    (hf : Tendsto (id fun i => F i : ι → ∀ a, E a) l (𝓝 f)) : Memℓp f p := by
  obtain ⟨C, hCF⟩ : ∃ C, ∀ k, ‖F k‖ ≤ C := hF.exists_norm_le.imp fun _ ↦ Set.forall_mem_range.1
  rcases eq_top_or_lt_top p with (rfl | hp)
  · apply memℓp_infty
    use C
    rintro _ ⟨a, rfl⟩
    exact norm_apply_le_of_tendsto (Eventually.of_forall hCF) hf a
  · apply memℓp_gen'
    exact sum_rpow_le_of_tendsto hp.ne (Eventually.of_forall hCF) hf

/-- If a sequence is Cauchy in the `lp E p` topology and pointwise convergent to an element `f` of
`lp E p`, then it converges to `f` in the `lp E p` topology. -/
/-
**lp.tendsto_lp_of_tendsto_pi** 是 Mathlib 中的一个定理，位于命名空间 `lp`。
形式化陈述：tendsto_lp_of_tendsto_pi {F : Nat -> lp E p} (hF : CauchySeq F) {f : lp E 
p} (hf : Tendsto (id fun i => F i : Nat -> forall a, E a) atTop (𝓝 f)) : Tendsto
 F atTop (𝓝 f)
参数：hF : CauchySeq F；hf : Tendsto (id fun i => F i : Nat -> forall a, E a) atTop 
(𝓝 f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `NormedAddCommGroup.uniformity_basis_dist`：∀ {E : Type u_5} [inst : Semin
ormedAddCommGroup E],   (uniformity E).HasBasis (fun ε => 0 < ε) fun ε => {p | ‖
p.1 - p.2‖ < ε}
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `CauchySeq.eventually_eventually`：CauchySeq.eventually_eventually [Preord
er β] {u : β -> α} (hu : CauchySeq u) {V : SetRel α α} (hV : V in 𝓤 α) : forallᶠ
 k in atTop, forallᶠ …
· 使用定理 `mem_closedBall_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖b - a‖ ≤ r
· 使用定理 `lp.norm_le_of_tendsto`：norm_le_of_tendsto {C : Real} {F : ι -> lp E p} (
hCF : forallᶠ k in l, ‖F k‖ <= C) {f : lp E p} (hf : Tendsto (id fun i => F i : 
ι -> forall…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …

--- 原说明 ---
If a sequence is Cauchy in the `lp E p` topology and pointwise convergent to an 
element `f` of
`lp E p`, then it converges to `f` in the `lp E p` topology.
-/
theorem tendsto_lp_of_tendsto_pi {F : ℕ → lp E p} (hF : CauchySeq F) {f : lp E p}
    (hf : Tendsto (id fun i => F i : ℕ → ∀ a, E a) atTop (𝓝 f)) : Tendsto F atTop (𝓝 f) := by
  rw [Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  have hε' : { p : lp E p × lp E p | ‖p.1 - p.2‖ < ε } ∈ uniformity (lp E p) :=
    NormedAddCommGroup.uniformity_basis_dist.mem_of_mem hε
  refine (hF.eventually_eventually hε').mono ?_
  rintro n (hn : ∀ᶠ l in atTop, ‖(fun f => F n - f) (F l)‖ < ε)
  rw [mem_closedBall_iff_norm]
  refine norm_le_of_tendsto (hn.mono fun k hk => hk.le) ?_
  rw [tendsto_pi_nhds]
  intro a
  exact (hf.apply_nhds a).const_sub (F n a)

variable [∀ a, CompleteSpace (E a)]
/-
**lp.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 `lp`。
形式化陈述：completeSpace : CompleteSpace (lp E p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_cauchySeq_tendsto`：Metric.complete_of_cauchySeq_tends
to : (forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Co
mpleteSpace α
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `UniformContinuous.comp_cauchySeq`：UniformContinuous.comp_cauchySeq {γ} [
UniformSpace β] [Preorder γ] {f : α -> β} (hf : UniformContinuous f) {u : γ -> α
} (hu : CauchySeq u) :…
· 使用定理 `lp.uniformContinuous_coe`：uniformContinuous_coe [_i : Fact (1 <= p)] : U
niformContinuous (α
· 使用定理 `lp.memℓp_of_tendsto`：memℓp_of_tendsto {F : ι -> lp E p} (hF : Bornology.
IsBounded (Set.range F)) {f : forall a, E a} (hf : Tendsto (id fun i => F i : ι 
-> forall…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CauchySeq.isBounded_range`：∀ {α : Type u} [inst : PseudoMetricSpace α] {
f : ℕ → α}, CauchySeq f → Bornology.IsBounded (Set.range f)
· 使用定理 `lp.tendsto_lp_of_tendsto_pi`：tendsto_lp_of_tendsto_pi {F : Nat -> lp E p
} (hF : CauchySeq F) {f : lp E p} (hf : Tendsto (id fun i => F i : Nat -> forall
 a, E a) atTop (𝓝…
-/
instance completeSpace : CompleteSpace (lp E p) :=
  Metric.complete_of_cauchySeq_tendsto (by
    intro F hF
    -- A Cauchy sequence in `lp E p` is pointwise convergent; let `f` be the pointwise limit.
    obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
      ((uniformContinuous_coe (p := p)).comp_cauchySeq hF)
    -- Since the Cauchy sequence is bounded, its pointwise limit `f` is in `lp E p`.
    have hf' : Memℓp f p := memℓp_of_tendsto hF.isBounded_range hf
    -- And therefore `f` is its limit in the `lp E p` topology as well as pointwise.
    exact ⟨⟨f, hf'⟩, tendsto_lp_of_tendsto_pi hF hf⟩)

end Topology

end lp

section Lipschitz

open ENNReal lp
variable {ι : Type*}

/-
**LipschitzWith.uniformly_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzWith.uniformly_bounded [PseudoMetricSpace α] (g : α -> ι -> Real)
 {K : Real>=0} (hg : forall i, LipschitzWith K (g · i)) (a₀ : α) (hga₀b : Memℓp 
(g a₀) ∞) (a : α) : Memℓp (g a) ∞
参数：g : α -> ι -> Real；hg : forall i, LipschitzWith K (g · i)；a₀ : α；hga₀b : Memℓ
p (g a₀) ∞；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
-/
lemma LipschitzWith.uniformly_bounded [PseudoMetricSpace α] (g : α → ι → ℝ) {K : ℝ≥0}
    (hg : ∀ i, LipschitzWith K (g · i)) (a₀ : α) (hga₀b : Memℓp (g a₀) ∞) (a : α) :
    Memℓp (g a) ∞ := by
  rcases hga₀b with ⟨M, hM⟩
  use ↑K * dist a a₀ + M
  rintro - ⟨i, rfl⟩
  calc
    |g a i| = |g a i - g a₀ i + g a₀ i| := by simp
    _ ≤ |g a i - g a₀ i| + |g a₀ i| := abs_add_le _ _
    _ ≤ ↑K * dist a a₀ + M := by
        gcongr
        · exact lipschitzWith_iff_dist_le_mul.1 (hg i) a a₀
        · exact hM ⟨i, rfl⟩
/-
**LipschitzOnWith.coordinate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.coordinate [PseudoMetricSpace α] (f : α -> ℓ^∞(ι, Real)) (
s : Set α) (K : Real>=0) : LipschitzOnWith K f s ↔ forall i : ι, LipschitzOnWith
 K (fun a : α => f a i) s
参数：f : α -> ℓ^∞(ι, Real)；s : Set α；K : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `lp.norm_apply_le_norm`：norm_apply_le_norm (hp : p != 0) (f : lp E p) (i 
: α) : ‖f i‖ <= ‖f‖
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `lp.norm_le_of_forall_le`：norm_le_of_forall_le {f : lp E ∞} {C : Real} (h
C : 0 <= C) (hCf : forall i, ‖f i‖ <= C) : ‖f‖ <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem LipschitzOnWith.coordinate [PseudoMetricSpace α] (f : α → ℓ^∞(ι, ℝ)) (s : Set α) (K : ℝ≥0) :
    LipschitzOnWith K f s ↔ ∀ i : ι, LipschitzOnWith K (fun a : α ↦ f a i) s := by
  simp_rw [lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hfl i x hx y hy
    calc
      dist (f x i) (f y i) ≤ dist (f x) (f y) := by
        simp only [dist_eq_norm]
        exact lp.norm_apply_le_norm top_ne_zero (f x - f y) i
      _ ≤ K * dist x y := hfl x hx y hy
  · intro hgl x hx y hy
    rw [dist_eq_norm]
    apply lp.norm_le_of_forall_le
    · positivity
    intro i
    apply hgl i x hx y hy
/-
**LipschitzWith.coordinate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.coordinate [PseudoMetricSpace α] {f : α -> ℓ^∞(ι, Real)} (K 
: Real>=0) : LipschitzWith K f ↔ forall i : ι, LipschitzWith K (fun a : α => f a
 i)
参数：ι, Real；K : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LipschitzOnWith.coordinate`：LipschitzOnWith.coordinate [PseudoMetricSpac
e α] (f : α -> ℓ^∞(ι, Real)) (s : Set α) (K : Real>=0) : LipschitzOnWith K f s ↔
 forall i : ι, L…
-/
theorem LipschitzWith.coordinate [PseudoMetricSpace α] {f : α → ℓ^∞(ι, ℝ)} (K : ℝ≥0) :
    LipschitzWith K f ↔ ∀ i : ι, LipschitzWith K (fun a : α ↦ f a i) := by
  simp_rw [← lipschitzOnWith_univ]
  apply LipschitzOnWith.coordinate

end Lipschitz

