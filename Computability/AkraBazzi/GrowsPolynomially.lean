/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Akra-Bazzi theorem: the polynomial growth condition

This file defines and develops an API for the polynomial growth condition that appears in the
statement of the Akra-Bazzi theorem: for the theorem to hold, the function `g` must
satisfy the condition that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b*n` and `n` for any
constant `b ∈ (0,1)`.

## Implementation notes

Our definition requires that the condition hold for any `b ∈ (0,1)`. This is equivalent to requiring
it only for `b = 1 / 2` (or any other particular value in `(0, 1)`). While this could, in principle,
make it harder to prove that a particular function grows polynomially, this issue does not seem to
arise in practice.

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

/-- The growth condition that the function `g` must satisfy for the Akra-Bazzi theorem to apply.
It roughly states that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b * n` and `n`, for any
constant `b ∈ (0, 1)`. -/
/-
**AkraBazziRecurrence.GrowsPolynomially** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：GrowsPolynomially (f : Real -> Real) : Prop
参数：f : Real -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The growth condition that the function `g` must satisfy for the Akra-Bazzi theor
em to apply.
It roughly states that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b * n` and `
n`, for any
constant `b ∈ (0, 1)`.
-/
def GrowsPolynomially (f : ℝ → ℝ) : Prop :=
  ∀ b ∈ Set.Ioo 0 1, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ∈ Set.Icc (c₁ * (f x)) (c₂ * f x)

namespace GrowsPolynomially

/-
**AkraBazziRecurrence.GrowsPolynomially.congr_of_eventuallyEq** 是 Mathlib 中的一个引理
，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：congr_of_eventuallyEq {f g : Real -> Real} (hfg : f =ᶠ[atTop] g) (hg : Gro
wsPolynomially g) : GrowsPolynomially f
参数：hfg : f =ᶠ[atTop] g；hg : GrowsPolynomially g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_of_eventuallyEq {f g : ℝ → ℝ} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g) :
    GrowsPolynomially f := by
  intro b hb
  have hg' := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1, hx₃]
  exact hx₁ u hu
/-
**AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq** 是 Mathlib 中的一个引理，位于命名
空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：iff_eventuallyEq {f g : Real -> Real} (h : f =ᶠ[atTop] g) : GrowsPolynomia
lly f ↔ GrowsPolynomially g
参数：h : f =ᶠ[atTop] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.congr_of_eventuallyEq`：congr_of_ev
entuallyEq {f g : Real -> Real} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g)
 : GrowsPolynomially f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma iff_eventuallyEq {f g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    GrowsPolynomially f ↔ GrowsPolynomially g :=
  ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

variable {f : ℝ → ℝ}
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_le** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_le {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomi
ally f) : exists c > 0, forallᶠ x in atTop, forall u in Set.Icc (b * x) x, f u <
= c * f x
参数：hb : b in Set.Ioo 0 1；hf : GrowsPolynomially f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma eventually_atTop_le {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ≤ c * f x := by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := hf b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_le_nat** 是 Mathlib 中的一个
引理，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_le_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPoly
nomially f) : exists c > 0, forallᶠ (n : Nat) in atTop, forall u in Set.Icc (b *
 n) n, f u <= c * f n
参数：hb : b in Set.Ioo 0 1；hf : GrowsPolynomially f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_le`：eventually_at
Top_le {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) : exists c 
> 0, forallᶠ x in atTop, forall u in Set.Icc (b…
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
-/
lemma eventually_atTop_le_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, f u ≤ c * f n := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_ge** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_ge {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomi
ally f) : exists c > 0, forallᶠ x in atTop, forall u in Set.Icc (b * x) x, c * f
 x <= f u
参数：hb : b in Set.Ioo 0 1；hf : GrowsPolynomially f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma eventually_atTop_ge {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, c * f x ≤ f u := by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := hf b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_ge_nat** 是 Mathlib 中的一个
引理，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_ge_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPoly
nomially f) : exists c > 0, forallᶠ (n : Nat) in atTop, forall u in Set.Icc (b *
 n) n, c * f n <= f u
参数：hb : b in Set.Ioo 0 1；hf : GrowsPolynomially f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_ge`：eventually_at
Top_ge {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) : exists c 
> 0, forallᶠ x in atTop, forall u in Set.Icc (b…
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
-/
lemma eventually_atTop_ge_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, c * f n ≤ f u := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_zero_of_frequently_zero** 是 M
athlib 中的一个引理，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_zero_of_frequently_zero (hf : GrowsPolynomially f) (hf' : exist
sᶠ x in atTop, f x = 0) : forallᶠ x in atTop, f x = 0
参数：hf : GrowsPolynomially f；hf' : existsᶠ x in atTop, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_forall_ge_atTop`：eventually_forall_ge_atTop [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x i
n atTop, p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
（共 112 条，此处仅展示前 30 条）
-/
lemma eventually_zero_of_frequently_zero (hf : GrowsPolynomially f) (hf' : ∃ᶠ x in atTop, f x = 0) :
    ∀ᶠ x in atTop, f x = 0 := by
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf (1 / 2) (by norm_num)
  rw [frequently_atTop] at hf'
  filter_upwards [eventually_forall_ge_atTop.mpr hf, eventually_gt_atTop 0] with x hx hx_pos
  obtain ⟨x₀, hx₀_ge, hx₀⟩ := hf' (max x 1)
  have x₀_pos := calc
    0 < 1 := by norm_num
    _ ≤ x₀ := le_of_max_le_right hx₀_ge
  have hmain : ∀ (m : ℕ) (z : ℝ), x ≤ z →
      z ∈ Set.Icc ((2 : ℝ) ^ (-(m : ℤ) - 1) * x₀) ((2 : ℝ) ^ (-(m : ℤ)) * x₀) → f z = 0 := by
    intro m
    induction m with
    | zero =>
      simp only [CharP.cast_eq_zero, neg_zero, zero_sub, zpow_zero, one_mul] at *
      specialize hx x₀ (le_of_max_le_left hx₀_ge)
      simp only [hx₀, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx
      refine fun z _ hz => hx _ ?_
      simp only [zpow_neg, zpow_one] at hz
      simp only [one_div, hz]
    | succ k ih =>
      intro z hxz hz
      simp only [Nat.cast_add, Nat.cast_one] at *
      have hx' : x ≤ (2 : ℝ) ^ (-(k : ℤ) - 1) * x₀ := by
        calc x ≤ z := hxz
          _ ≤ _ := by simp only [neg_add, ← sub_eq_add_neg] at hz; exact hz.2
      specialize hx ((2 : ℝ) ^ (-(k : ℤ) - 1) * x₀) hx' z
      specialize ih ((2 : ℝ) ^ (-(k : ℤ) - 1) * x₀) hx' ?ineq
      case ineq =>
        rw [Set.left_mem_Icc]
        gcongr
        · norm_num
        · lia
      simp only [ih, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx
      refine hx ⟨?lb₁, ?ub₁⟩
      case lb₁ =>
        rw [one_div, ← zpow_neg_one, ← mul_assoc, ← zpow_add₀ (by norm_num)]
        have h₁ : (-1 : ℤ) + (-k - 1) = -k - 2 := by ring
        have h₂ : -(k + (1 : ℤ)) - 1 = -k - 2 := by ring
        rw [h₁]
        rw [h₂] at hz
        exact hz.1
      case ub₁ =>
        have := hz.2
        simp only [neg_add, ← sub_eq_add_neg] at this
        exact this
  refine hmain ⌊-logb 2 (x / x₀)⌋₊ x le_rfl ⟨?lb, ?ub⟩
  case lb =>
    rw [← le_div_iff₀ x₀_pos]
    refine (logb_le_logb (b := 2) (by norm_num) (zpow_pos (by norm_num) _)
      (by positivity)).mp ?_
    rw [← rpow_intCast, logb_rpow (by norm_num) (by norm_num), ← neg_le_neg_iff]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_sub, sub_neg_eq_add]
    calc -logb 2 (x / x₀) ≤ ⌈-logb 2 (x / x₀)⌉₊ := Nat.le_ceil (-logb 2 (x / x₀))
         _ ≤ _ := by rw [add_comm]; exact_mod_cast Nat.ceil_le_floor_add_one _
  case ub =>
    rw [← div_le_iff₀ x₀_pos]
    refine (logb_le_logb (b := 2) (by norm_num) (by positivity)
      (zpow_pos (by norm_num) _)).mp ?_
    rw [← rpow_intCast, logb_rpow (by norm_num) (by norm_num), ← neg_le_neg_iff]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
    have : 0 ≤ -logb 2 (x / x₀) := by
      rw [neg_nonneg]
      refine logb_nonpos (by norm_num) (by positivity) ?_
      rw [div_le_one x₀_pos]
      exact le_of_max_le_left hx₀_ge
    exact_mod_cast Nat.floor_le this
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_nonneg_or_nonpos** 是 Ma
thlib 中的一个引理，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) : (forallᶠ x 
in atTop, 0 <= f x) ∨ (forallᶠ x in atTop, f x <= 0)
参数：hf : GrowsPolynomially f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
（共 103 条，此处仅展示前 30 条）
-/
lemma eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) :
    (∀ᶠ x in atTop, 0 ≤ f x) ∨ (∀ᶠ x in atTop, f x ≤ 0) := by
  obtain ⟨c₁, _, c₂, _, h⟩ := hf (1 / 2) (by norm_num)
  match lt_trichotomy c₁ c₂ with
  | .inl hlt => -- c₁ < c₂
    left
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x ∈ Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3 / 4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : 0 ≤ (c₂ - c₁) * f x := by linarith
    exact nonneg_of_mul_nonneg_right hu' (by linarith)
  | .inr (.inr hgt) => -- c₂ < c₁
    right
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x ∈ Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3 / 4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : (c₁ - c₂) * f x ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right hu' (by linarith)
  | .inr (.inl heq) => -- c₁ = c₂
    have hmain : ∃ c, ∀ᶠ x in atTop, f x = c := by
      simp only [heq, Set.Icc_self, Set.mem_singleton_iff] at h
      rw [eventually_atTop] at h
      obtain ⟨n₀, hn₀⟩ := h
      refine ⟨f (max n₀ 2), ?_⟩
      rw [eventually_atTop]
      refine ⟨max n₀ 2, ?_⟩
      refine Real.induction_Ico_mul _ 2 (by norm_num) (by positivity) ?base ?step
      case base => grind
      case step =>
        intro n _ _ z _
        have le_2n : max n₀ 2 ≤ (2 : ℝ) ^ n * max n₀ 2 := by
          simp [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num1)]
        have half_z_to_base : f (1 / 2 * z) = f (max n₀ 2) := by
          grind [mul_assoc]
        grind
    obtain ⟨c, hc⟩ := hmain
    cases le_or_gt 0 c with
    | inl hpos =>
      exact Or.inl <| by filter_upwards [hc] with _ hc; simpa only [hc]
    | inr hneg =>
      right
      filter_upwards [hc] with x hc
      exact le_of_lt <| by simpa only [hc]
/-
**AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_zero_or_pos_or_neg** 是 
Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) : (forallᶠ 
x in atTop, f x = 0) ∨ (forallᶠ x in atTop, 0 < f x) ∨ (forallᶠ x in atTop, f x 
< 0)
参数：hf : GrowsPolynomially f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_zero_of_frequently_zero
`：eventually_zero_of_frequently_zero (hf : GrowsPolynomially f) (hf' : existsᶠ x
 in atTop, f x = 0) : forallᶠ x in atTop, f x = 0
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_nonneg_or_nonpos`
：eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) : (forallᶠ x in at
Top, 0 <= f x) ∨ (forallᶠ x in atTop, f x <= 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_and`：eventually_and {p q : α -> Prop} {f : Filter α} :
 (forallᶠ x in f, p x ∧ q x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) :
    (∀ᶠ x in atTop, f x = 0) ∨ (∀ᶠ x in atTop, 0 < f x) ∨ (∀ᶠ x in atTop, f x < 0) := by
  by_cases! h : ∃ᶠ x in atTop, f x = 0
  · exact Or.inl <| eventually_zero_of_frequently_zero hf h
  · cases eventually_atTop_nonneg_or_nonpos hf with
    | inl h' =>
      refine Or.inr (Or.inl ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', by filter_upwards [h] with x hx; exact hx.symm⟩
    | inr h' =>
      refine Or.inr (Or.inr ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', h⟩
/-
**AkraBazziRecurrence.GrowsPolynomially.neg** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ}, AkraBazziRecurrence.GrowsPolynomially f → AkraBazziRecurren
ce.GrowsPolynomially (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected lemma neg {f : ℝ → ℝ} (hf : GrowsPolynomially f) : GrowsPolynomially (-f) := by
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu
/-
**AkraBazziRecurrence.GrowsPolynomially.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `AkraB
azziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ}, AkraBazziRecurrence.GrowsPolynomially f ↔ AkraBazziRecurren
ce.GrowsPolynomially (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.neg`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially (-f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected lemma neg_iff {f : ℝ → ℝ} : GrowsPolynomially f ↔ GrowsPolynomially (-f) :=
  ⟨fun hf => hf.neg, fun hf => by rw [← neg_neg f]; exact hf.neg⟩
/-
**AkraBazziRecurrence.GrowsPolynomially.abs** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ}, AkraBazziRecurrence.GrowsPolynomially f → AkraBazziRecurren
ce.GrowsPolynomially fun x => |f x|
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_nonneg_or_nonpos`
：eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) : (forallᶠ x in at
Top, 0 <= f x) ∨ (forallᶠ x in atTop, f x <= 0)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.iff_eventuallyEq`：iff_eventuallyEq
 {f g : Real -> Real} (h : f =ᶠ[atTop] g) : GrowsPolynomially f ↔ GrowsPolynomia
lly g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.neg`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially (-f)
-/
protected lemma abs (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => |f x|) := by
  cases eventually_atTop_nonneg_or_nonpos hf with
  | inl hf' =>
    have hmain : f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      rw [abs_of_nonneg hx]
    rw [← iff_eventuallyEq hmain]
    exact hf
  | inr hf' =>
    have hmain : -f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      simp only [Pi.neg_apply, abs_of_nonpos hx]
    rw [← iff_eventuallyEq hmain]
    exact hf.neg
/-
**AkraBazziRecurrence.GrowsPolynomially.norm** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazz
iRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ}, AkraBazziRecurrence.GrowsPolynomially f → AkraBazziRecurren
ce.GrowsPolynomially fun x => ‖f x‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.abs`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially fun x => |f x|
-/
protected lemma norm (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => ‖f x‖) := by
  simp only [norm_eq_abs]
  exact hf.abs

end GrowsPolynomially

variable {f : ℝ → ℝ}

/-
**AkraBazziRecurrence.growsPolynomially_const** 是 Mathlib 中的一个引理，位于命名空间 `AkraBaz
ziRecurrence`。
形式化陈述：growsPolynomially_const {c : Real} : GrowsPolynomially (fun _ => c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma growsPolynomially_const {c : ℝ} : GrowsPolynomially (fun _ => c) := by
  refine fun _ _ => ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with x
  simp
/-
**AkraBazziRecurrence.growsPolynomially_id** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziR
ecurrence`。
形式化陈述：growsPolynomially_id : GrowsPolynomially (fun x => x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma growsPolynomially_id : GrowsPolynomially (fun x => x) := by
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards with x u hu
  simp only [one_mul, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩
/-
**AkraBazziRecurrence.GrowsPolynomially.mul** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially f →     AkraBazzi
Recurrence.GrowsPolynomially g → AkraBazziRecurrence.GrowsPolynomially fun x => 
f x * g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.abs`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially fun x => |f x|
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 43 条，此处仅展示前 30 条）
-/
protected lemma GrowsPolynomially.mul {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) : GrowsPolynomially fun x => f x * g x := by
  suffices GrowsPolynomially fun x => |f x| * |g x| by
    cases eventually_atTop_nonneg_or_nonpos hf with
    | inl hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonneg hx₁, abs_of_nonneg hx₂]
        rwa [iff_eventuallyEq hmain]
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonneg hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
    | inr hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonpos hx₁, abs_of_nonneg hx₂, neg_neg]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonpos hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain]
        exact this
  intro b hb
  have hf := hf.abs b hb
  have hg := hg.abs b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, hc₄_mem, hg⟩ := hg
  refine ⟨c₁ * c₃, by change 0 < c₁ * c₃; positivity, ?_⟩
  refine ⟨c₂ * c₄, by change 0 < c₂ * c₄; positivity, ?_⟩
  filter_upwards [hf, hg] with x hf hg
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₃ * (|f x| * |g x|) = (c₁ * |f x|) * (c₃ * |g x|) := by ring
    _ ≤ |f u| * |g u| := by
           gcongr
           · exact (hf u hu).1
           · exact (hg u hu).1
  case ub => calc
    |f u| * |g u| ≤ (c₂ * |f x|) * (c₄ * |g x|) := by
           gcongr
           · exact (hf u hu).2
           · exact (hg u hu).2
    _ = c₂ * c₄ * (|f x| * |g x|) := by ring
/-
**AkraBazziRecurrence.GrowsPolynomially.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Akr
aBazziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ} {c : ℝ}, AkraBazziRecurrence.GrowsPolynomially f → AkraBazzi
Recurrence.GrowsPolynomially fun x => c * f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.mul`：∀ {f g : ℝ → ℝ},   AkraBazziR
ecurrence.GrowsPolynomially f →     AkraBazziRecurrence.GrowsPolynomially g → Ak
raBazziRecurrence.GrowsPolynomi…
· 使用引理 `AkraBazziRecurrence.growsPolynomially_const`：growsPolynomially_const {c 
: Real} : GrowsPolynomially (fun _ => c)
-/
lemma GrowsPolynomially.const_mul {f : ℝ → ℝ} {c : ℝ} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => c * f x :=
  GrowsPolynomially.mul growsPolynomially_const hf
/-
**AkraBazziRecurrence.GrowsPolynomially.add** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially f →     AkraBazzi
Recurrence.GrowsPolynomially g →       0 ≤ᶠ[Filter.atTop] f → 0 ≤ᶠ[Filter.atTop]
 g → AkraBazziRecurrence.GrowsPolynomially fun x => f x + g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 43 条，此处仅展示前 30 条）
-/
protected lemma GrowsPolynomially.add {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) (hf' : 0 ≤ᶠ[atTop] f) (hg' : 0 ≤ᶠ[atTop] g) :
    GrowsPolynomially fun x => f x + g x := by
  intro b hb
  have hf := hf b hb
  have hg := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  refine ⟨min c₁ c₃, by change 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by change 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hg',
                  eventually_ge_atTop 0] with x hf hg hf' hg' hx_pos
  intro u hu
  have hbx : b * x ≤ x := calc
    b * x ≤ 1 * x := by gcongr; exact le_of_lt hb.2
        _ = x := by ring
  have fx_nonneg : 0 ≤ f x := hf' x hbx
  have gx_nonneg : 0 ≤ g x := hg' x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    min c₁ c₃ * (f x + g x) = min c₁ c₃ * f x + min c₁ c₃ * g x := by simp only [mul_add]
      _ ≤ c₁ * f x + c₃ * g x := by
              gcongr
              · exact min_le_left _ _
              · exact min_le_right _ _
      _ ≤ f u + g u := by
              gcongr
              · exact (hf u hu).1
              · exact (hg u hu).1
  case ub => calc
    max c₂ c₄ * (f x + g x) = max c₂ c₄ * f x + max c₂ c₄ * g x := by simp only [mul_add]
      _ ≥ c₂ * f x + c₄ * g x := by gcongr
                                    · exact le_max_left _ _
                                    · exact le_max_right _ _
      _ ≥ f u + g u := by gcongr
                          · exact (hf u hu).2
                          · exact (hg u hu).2
/-
**AkraBazziRecurrence.GrowsPolynomially.add_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 
`AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially f →     g =o[Filt
er.atTop] f → AkraBazziRecurrence.GrowsPolynomially fun x => f x + g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_nonneg_or_nonpos`
：eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) : (forallᶠ x in at
Top, 0 <= f x) ∨ (forallᶠ x in atTop, f x <= 0)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 98 条，此处仅展示前 30 条）
-/
lemma GrowsPolynomially.add_isLittleO {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hfg : g =o[atTop] f) : GrowsPolynomially fun x => f x + g x := by
  intro b hb
  have hb_ub := hb.2
  rw [isLittleO_iff] at hfg
  cases hf.eventually_atTop_nonneg_or_nonpos with
  | inl hf' => -- f is eventually non-negative
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
    refine ⟨c₁ / 3, by positivity, 3*c₂, by positivity, ?_⟩
    filter_upwards [hf,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                    eventually_ge_atTop 0] with x hf₁ hfg' hf₂ hx_nonneg
    have hbx : b * x ≤ x := by nth_rewrite 2 [← one_mul x]; gcongr
    have hfg₂ : ‖g x‖ ≤ 1 / 2 * f x := by
      calc ‖g x‖ ≤ 1 / 2 * ‖f x‖ := hfg' x hbx
           _ = 1 / 2 * f x := by congr; exact norm_of_nonneg (hf₂ _ hbx)
    have hx_ub : f x + g x ≤ 3 / 2 * f x := by
      calc _ ≤ f x + ‖g x‖ := by gcongr; exact le_norm_self (g x)
           _ ≤ f x + 1 / 2 * f x := by gcongr
           _ = 3 / 2 * f x := by ring
    have hx_lb : 1 / 2 * f x ≤ f x + g x := by
      calc f x + g x ≥ f x - ‖g x‖ := by
                rw [sub_eq_add_neg, norm_eq_abs]; gcongr; exact neg_abs_le (g x)
           _ ≥ f x - 1 / 2 * f x := by gcongr
           _ = 1 / 2 * f x := by ring
    intro u ⟨hu_lb, hu_ub⟩
    have hfu_nonneg : 0 ≤ f u := hf₂ _ hu_lb
    have hfg₃ : ‖g u‖ ≤ 1 / 2 * f u := by
      calc ‖g u‖ ≤ 1 / 2 * ‖f u‖ := hfg' _ hu_lb
           _ = 1 / 2 * f u := by congr; simp only [norm_eq_abs, abs_eq_self, hfu_nonneg]
    refine ⟨?lb, ?ub⟩
    case lb =>
      calc f u + g u ≥ f u - ‖g u‖ := by
                  rw [sub_eq_add_neg, norm_eq_abs]; gcongr; exact neg_abs_le _
           _ ≥ f u - 1 / 2 * f u := by gcongr
           _ = 1 / 2 * f u := by ring
           _ ≥ 1 / 2 * (c₁ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).1
           _ = c₁ / 3 * (3 / 2 * f x) := by ring
           _ ≥ c₁ / 3 * (f x + g x) := by gcongr
    case ub =>
      calc _ ≤ f u + ‖g u‖ := by gcongr; exact le_norm_self (g u)
           _ ≤ f u + 1 / 2 * f u := by gcongr
           _ = 3 / 2 * f u := by ring
           _ ≤ 3 / 2 * (c₂ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).2
           _ = 3 * c₂ * (1 / 2 * f x) := by ring
           _ ≤ 3 * c₂ * (f x + g x) := by gcongr
  | inr hf' => -- f is eventually nonpos
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
    refine ⟨3*c₁, by positivity, c₂/3, by positivity, ?_⟩
    filter_upwards [hf,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                    eventually_ge_atTop 0] with x hf₁ hfg' hf₂ hx_nonneg
    have hbx : b * x ≤ x := by nth_rewrite 2 [← one_mul x]; gcongr
    have hfg₂ : ‖g x‖ ≤ -1 / 2 * f x := by
      calc ‖g x‖ ≤ 1 / 2 * ‖f x‖ := hfg' x hbx
           _ = 1 / 2 * (-f x) := by congr; exact norm_of_nonpos (hf₂ x hbx)
           _ = _ := by ring
    have hx_ub : f x + g x ≤ 1 / 2 * f x := by
      calc _ ≤ f x + ‖g x‖ := by gcongr; exact le_norm_self (g x)
           _ ≤ f x + (-1 / 2 * f x) := by gcongr
           _ = 1 / 2 * f x := by ring
    have hx_lb : 3 / 2 * f x ≤ f x + g x := by
      calc f x + g x ≥ f x - ‖g x‖ := by
                rw [sub_eq_add_neg, norm_eq_abs]; gcongr; exact neg_abs_le (g x)
           _ ≥ f x + 1 / 2 * f x := by
                  rw [sub_eq_add_neg]
                  gcongr
                  refine le_of_neg_le_neg ?bc.a
                  rwa [neg_neg, ← neg_mul, ← neg_div]
           _ = 3 / 2 * f x := by ring
    intro u ⟨hu_lb, hu_ub⟩
    have hfu_nonpos : f u ≤ 0 := hf₂ _ hu_lb
    have hfg₃ : ‖g u‖ ≤ -1 / 2 * f u := by
      calc ‖g u‖ ≤ 1 / 2 * ‖f u‖ := hfg' _ hu_lb
           _ = 1 / 2 * (-f u) := by congr; exact norm_of_nonpos hfu_nonpos
           _ = -1 / 2 * f u := by ring
    refine ⟨?lb, ?ub⟩
    case lb =>
      calc f u + g u ≥ f u - ‖g u‖ := by
                  rw [sub_eq_add_neg, norm_eq_abs]; gcongr; exact neg_abs_le _
           _ ≥ f u + 1 / 2 * f u := by
                  rw [sub_eq_add_neg]
                  gcongr
                  refine le_of_neg_le_neg ?_
                  rwa [neg_neg, ← neg_mul, ← neg_div]
           _ = 3 / 2 * f u := by ring
           _ ≥ 3 / 2 * (c₁ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).1
           _ = 3 * c₁ * (1 / 2 * f x) := by ring
           _ ≥ 3 * c₁ * (f x + g x) := by gcongr
    case ub =>
      calc _ ≤ f u + ‖g u‖ := by gcongr; exact le_norm_self (g u)
           _ ≤ f u - 1 / 2 * f u := by
                rw [sub_eq_add_neg]
                gcongr
                rwa [← neg_mul, ← neg_div]
           _ = 1 / 2 * f u := by ring
           _ ≤ 1 / 2 * (c₂ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).2
           _ = c₂ / 3 * (3 / 2 * f x) := by ring
           _ ≤ c₂ / 3 * (f x + g x) := by gcongr
/-
**AkraBazziRecurrence.GrowsPolynomially.inv** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ}, AkraBazziRecurrence.GrowsPolynomially f → AkraBazziRecurren
ce.GrowsPolynomially fun x => (f x)⁻¹
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_zero_or_pos_or_ne
g`：eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) : (forallᶠ x i
n atTop, f x = 0) ∨ (forallᶠ x in atTop, 0 < f x) ∨ (forallᶠ x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.abs`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially fun x => |f x|
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
（共 47 条，此处仅展示前 30 条）
-/
protected lemma GrowsPolynomially.inv {f : ℝ → ℝ} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => (f x)⁻¹ := by
  cases hf.eventually_atTop_zero_or_pos_or_neg with
  | inl hf' =>
    refine fun b hb => ⟨1, by simp, 1, by simp, ?_⟩
    have hb_pos := hb.1
    filter_upwards [hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx'
    intro u hu
    simp only [hx, inv_zero, mul_zero, Set.Icc_self, Set.mem_singleton_iff, hx' u hu.1]
  | inr hf_pos_or_neg =>
    suffices GrowsPolynomially fun x => |(f x)⁻¹| by
      cases hf_pos_or_neg with
      | inl hf' =>
        have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => |(f x)⁻¹| := by
          filter_upwards [hf'] with x hx₁
          rw [abs_of_nonneg (inv_nonneg_of_nonneg (le_of_lt hx₁))]
        rwa [iff_eventuallyEq hmain]
      | inr hf' =>
        have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => -|(f x)⁻¹| := by
          filter_upwards [hf'] with x hx₁
          simp [abs_of_nonpos (inv_nonpos.mpr (le_of_lt hx₁))]
        rw [iff_eventuallyEq hmain]
        exact this.neg
    have hf' : ∀ᶠ x in atTop, f x ≠ 0 := by
      cases hf_pos_or_neg with
      | inl H => filter_upwards [H] with _ hx; exact (ne_of_lt hx).symm
      | inr H => filter_upwards [H] with _ hx; exact (ne_of_gt hx).symm
    simp only [abs_inv]
    have hf := hf.abs
    intro b hb
    have hb_pos := hb.1
    obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
    refine ⟨c₂⁻¹, by change 0 < c₂⁻¹; positivity, ?_⟩
    refine ⟨c₁⁻¹, by change 0 < c₁⁻¹; positivity, ?_⟩
    filter_upwards [hf, hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx' hx''
    intro u hu
    have h₁ : 0 < |f u| := by rw [abs_pos]; exact hx'' u hu.1
    refine ⟨?lb, ?ub⟩
    case lb =>
      rw [← mul_inv]
      gcongr
      exact (hx u hu).2
    case ub =>
      rw [← mul_inv]
      gcongr
      exact (hx u hu).1
/-
**AkraBazziRecurrence.GrowsPolynomially.div** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially f →     AkraBazzi
Recurrence.GrowsPolynomially g → AkraBazziRecurrence.GrowsPolynomially fun x => 
f x / g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.mul`：∀ {f g : ℝ → ℝ},   AkraBazziR
ecurrence.GrowsPolynomially f →     AkraBazziRecurrence.GrowsPolynomially g → Ak
raBazziRecurrence.GrowsPolynomi…
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.inv`：∀ {f : ℝ → ℝ}, AkraBazziRecur
rence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially fun x => (f x)
⁻¹
-/
protected lemma GrowsPolynomially.div {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) : GrowsPolynomially fun x => f x / g x := by
  have : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by ext; rw [div_eq_mul_inv]
  rw [this]
  exact GrowsPolynomially.mul hf (GrowsPolynomially.inv hg)
/-
**AkraBazziRecurrence.GrowsPolynomially.rpow** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazz
iRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ} (p : ℝ),   AkraBazziRecurrence.GrowsPolynomially f →     (∀ᶠ
 (x : ℝ) in Filter.atTop, 0 ≤ f x) → AkraBazziRecurrence.GrowsPolynomially fun x
 => f x ^ p
参数：p : ℝ；∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_zero_or_pos_or_ne
g`：eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) : (forallᶠ x i
n atTop, f x = 0) ∨ (forallᶠ x in atTop, 0 < f x) ∨ (forallᶠ x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
（共 65 条，此处仅展示前 30 条）
-/
protected lemma GrowsPolynomially.rpow (p : ℝ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially fun x => (f x) ^ p := by
  intro b hb
  obtain ⟨c₁, (hc₁_mem : 0 < c₁), c₂, hc₂_mem, hfnew⟩ := hf b hb
  have hc₁p : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁_mem _
  have hc₂p : 0 < c₂ ^ p := Real.rpow_pos_of_pos hc₂_mem _
  cases le_or_gt 0 p with
  | inl => -- 0 ≤ p
    refine ⟨c₁^p, hc₁p, ?_⟩
    refine ⟨c₂^p, hc₂p, ?_⟩
    filter_upwards [eventually_gt_atTop 0, hfnew, hf_nonneg,
        (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf_nonneg]
        with x _ hf₁ hf_nonneg hf_nonneg₂
    intro u hu
    have fu_nonneg : 0 ≤ f u := hf_nonneg₂ u hu.1
    refine ⟨?lb, ?ub⟩
    case lb => calc
      c₁ ^ p * (f x) ^ p = (c₁ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₁_mem) hf_nonneg]
        _ ≤ _ := by gcongr; exact (hf₁ u hu).1
    case ub => calc
      (f u) ^ p ≤ (c₂ * f x) ^ p := by gcongr; exact (hf₁ u hu).2
        _ = _ := by rw [← mul_rpow (le_of_lt hc₂_mem) hf_nonneg]
  | inr hp => -- p < 0
    match hf.eventually_atTop_zero_or_pos_or_neg with
    | .inl hzero => -- eventually zero
      refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      filter_upwards [hzero, hfnew] with x hx hx'
      intro u hu
      simp only [hx, zero_rpow (ne_of_lt hp), mul_zero,
        Set.Icc_self, Set.mem_singleton_iff]
      simp only [hx, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx'
      rw [hx' u hu, zero_rpow (ne_of_lt hp)]
    | .inr (.inl hpos) => -- eventually positive
      refine ⟨c₂^p, hc₂p, ?_⟩
      refine ⟨c₁^p, hc₁p, ?_⟩
      filter_upwards [eventually_gt_atTop 0, hfnew, hpos,
          (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hpos]
          with x _ hf₁ hf_pos hf_pos₂
      intro u hu
      refine ⟨?lb, ?ub⟩
      case lb => calc
        c₂ ^ p * (f x) ^ p = (c₂ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₂_mem) (le_of_lt hf_pos)]
          _ ≤ _ := rpow_le_rpow_of_nonpos (hf_pos₂ u hu.1) (hf₁ u hu).2 (le_of_lt hp)
      case ub => calc
        (f u) ^ p ≤ (c₁ * f x) ^ p := by
              exact rpow_le_rpow_of_nonpos (by positivity) (hf₁ u hu).1 (le_of_lt hp)
          _ = _ := by rw [← mul_rpow (le_of_lt hc₁_mem) (le_of_lt hf_pos)]
    | .inr (.inr hneg) => -- eventually negative (which is impossible)
      have : ∀ᶠ (_ : ℝ) in atTop, False := by
        filter_upwards [hf_nonneg, hneg] with x hx hx'; linarith
      rw [Filter.eventually_false_iff_eq_bot] at this
      exact False.elim <| atTop_neBot.ne this
/-
**AkraBazziRecurrence.GrowsPolynomially.pow** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazzi
Recurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ} (p : ℕ),   AkraBazziRecurrence.GrowsPolynomially f →     (∀ᶠ
 (x : ℝ) in Filter.atTop, 0 ≤ f x) → AkraBazziRecurrence.GrowsPolynomially fun x
 => f x ^ p
参数：p : ℕ；∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.rpow`：∀ {f : ℝ → ℝ} (p : ℝ),   Akr
aBazziRecurrence.GrowsPolynomially f →     (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x)
 → AkraBazziRecurrence.GrowsPoly…
-/
protected lemma GrowsPolynomially.pow (p : ℕ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially fun x => (f x) ^ p := by
  simp_rw [← rpow_natCast]
  exact hf.rpow p hf_nonneg
/-
**AkraBazziRecurrence.GrowsPolynomially.zpow** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazz
iRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ} (p : ℤ),   AkraBazziRecurrence.GrowsPolynomially f →     (∀ᶠ
 (x : ℝ) in Filter.atTop, 0 ≤ f x) → AkraBazziRecurrence.GrowsPolynomially fun x
 => f x ^ p
参数：p : ℤ；∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.rpow`：∀ {f : ℝ → ℝ} (p : ℝ),   Akr
aBazziRecurrence.GrowsPolynomially f →     (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x)
 → AkraBazziRecurrence.GrowsPoly…
-/
protected lemma GrowsPolynomially.zpow (p : ℤ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially fun x => (f x) ^ p := by
  simp_rw [← rpow_intCast]
  exact hf.rpow p hf_nonneg
/-
**AkraBazziRecurrence.growsPolynomially_rpow** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazz
iRecurrence`。
形式化陈述：growsPolynomially_rpow (p : Real) : GrowsPolynomially fun x => x ^ p
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.rpow`：∀ {f : ℝ → ℝ} (p : ℝ),   Akr
aBazziRecurrence.GrowsPolynomially f →     (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x)
 → AkraBazziRecurrence.GrowsPoly…
· 使用引理 `AkraBazziRecurrence.growsPolynomially_id`：growsPolynomially_id : GrowsPo
lynomially (fun x => x)
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma growsPolynomially_rpow (p : ℝ) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.rpow p (eventually_ge_atTop 0)
/-
**AkraBazziRecurrence.growsPolynomially_pow** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazzi
Recurrence`。
形式化陈述：growsPolynomially_pow (p : Nat) : GrowsPolynomially fun x => x ^ p
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.pow`：∀ {f : ℝ → ℝ} (p : ℕ),   Akra
BazziRecurrence.GrowsPolynomially f →     (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x) 
→ AkraBazziRecurrence.GrowsPoly…
· 使用引理 `AkraBazziRecurrence.growsPolynomially_id`：growsPolynomially_id : GrowsPo
lynomially (fun x => x)
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma growsPolynomially_pow (p : ℕ) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.pow p (eventually_ge_atTop 0)
/-
**AkraBazziRecurrence.growsPolynomially_zpow** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazz
iRecurrence`。
形式化陈述：growsPolynomially_zpow (p : Int) : GrowsPolynomially fun x => x ^ p
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.zpow`：∀ {f : ℝ → ℝ} (p : ℤ),   Akr
aBazziRecurrence.GrowsPolynomially f →     (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x)
 → AkraBazziRecurrence.GrowsPoly…
· 使用引理 `AkraBazziRecurrence.growsPolynomially_id`：growsPolynomially_id : GrowsPo
lynomially (fun x => x)
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma growsPolynomially_zpow (p : ℤ) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.zpow p (eventually_ge_atTop 0)
/-
**AkraBazziRecurrence.growsPolynomially_log** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazzi
Recurrence`。
形式化陈述：growsPolynomially_log : GrowsPolynomially Real.log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
（共 72 条，此处仅展示前 30 条）
-/
lemma growsPolynomially_log : GrowsPolynomially Real.log := by
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop
                    <| h_tendsto.eventually (eventually_gt_atTop (-Real.log b))] with x hx_pos hx
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    1 / 2 * Real.log x = Real.log x + (-1 / 2) * Real.log x := by ring
      _ ≤ Real.log x + Real.log b := by grind
      _ = Real.log (b * x) := by rw [← Real.log_mul (by positivity) (by positivity), mul_comm]
      _ ≤ Real.log u := by gcongr; exact hu.1
  case ub =>
    rw [one_mul]
    gcongr
    · calc 0 < b * x := by positivity
         _ ≤ u := by exact hu.1
    · exact hu.2
/-
**AkraBazziRecurrence.GrowsPolynomially.of_isTheta** 是 Mathlib 中的一个定理，位于命名空间 `Ak
raBazziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially g →     f =Θ[Filt
er.atTop] g → (∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x) → AkraBazziRecurrence.GrowsP
olynomially f
参数：∀ᶠ (x : ℝ) in Filter.atTop, 0 ≤ f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_iff''`：isBigO_iff'' {g : α -> E'''} : f =O[l] g ↔ exi
sts c > 0, forallᶠ x in l, c * ‖f x‖ <= ‖g x‖
· 使用定理 `Asymptotics.IsTheta.isBigO_symm`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}
,   f =Θ[l] g → g =O[…
· 使用定理 `Asymptotics.isBigO_iff'`：isBigO_iff' {g : α -> E'''} : f =O[l] g ↔ exist
s c > 0, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.norm`：∀ {f : ℝ → ℝ}, AkraBazziRecu
rrence.GrowsPolynomially f → AkraBazziRecurrence.GrowsPolynomially fun x => ‖f x
‖
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually_forall_ge_atTop`：∀ {α : Type u_3} {β : Type u_
4} [inst : Preorder β] {l : Filter α} {p : β → Prop} {f : α → β},   Filter.Tends
to f l Filter.atTop → (∀ᶠ (x : …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 55 条，此处仅展示前 30 条）
-/
lemma GrowsPolynomially.of_isTheta {f g : ℝ → ℝ} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
    (hf' : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially f := by
  intro b hb
  have hb_pos := hb.1
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨c₄, hc₄_pos : 0 < c₄, hg⟩ := hg
  have h_lb_pos : 0 < c₁ * c₂⁻¹ * c₃ := by positivity
  have h_ub_pos : 0 < c₂ * c₄ * c₁⁻¹ := by positivity
  refine ⟨c₁ * c₂⁻¹ * c₃, h_lb_pos, ?_⟩
  refine ⟨c₂ * c₄ * c₁⁻¹, h_ub_pos, ?_⟩
  have c₂_cancel : c₂⁻¹ * c₂ = 1 := inv_mul_cancel₀ (by positivity)
  have c₁_cancel : c₁⁻¹ * c₁ = 1 := inv_mul_cancel₀ (by positivity)
  filter_upwards [(tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_lb,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_ub,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hg,
                  eventually_ge_atTop 0]
    with x hf_pos h_lb h_ub hg_bound hx_pos
  intro u hu
  have hbx : b * x ≤ x :=
    calc b * x ≤ 1 * x := by gcongr; exact le_of_lt hb.2
             _ = x := by rw [one_mul]
  have hg_bound := hg_bound x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₂⁻¹ * c₃ * f x ≤ c₁ * c₂⁻¹ * c₃ * (c₂ * ‖g x‖) := by
          rw [← Real.norm_of_nonneg (hf_pos x hbx)]; gcongr; exact h_ub x hbx
      _ = (c₂⁻¹ * c₂) * c₁ * (c₃ * ‖g x‖) := by ring
      _ = c₁ * (c₃ * ‖g x‖) := by simp [c₂_cancel]
      _ ≤ c₁ * ‖g u‖ := by gcongr; exact (hg_bound u hu).1
      _ ≤ f u := by
          rw [← Real.norm_of_nonneg (hf_pos u hu.1)]
          exact h_lb u hu.1
  case ub => calc
    f u ≤ c₂ * ‖g u‖ := by rw [← Real.norm_of_nonneg (hf_pos u hu.1)]; exact h_ub u hu.1
      _ ≤ c₂ * (c₄ * ‖g x‖) := by gcongr; exact (hg_bound u hu).2
      _ = c₂ * c₄ * (c₁⁻¹ * c₁) * ‖g x‖ := by simp [c₁_cancel]; ring
      _ = c₂ * c₄ * c₁⁻¹ * (c₁ * ‖g x‖) := by ring
      _ ≤ c₂ * c₄ * c₁⁻¹ * f x := by
                gcongr
                rw [← Real.norm_of_nonneg (hf_pos x hbx)]
                exact h_lb x hbx
/-
**AkraBazziRecurrence.GrowsPolynomially.of_isEquivalent** 是 Mathlib 中的一个定理，位于命名空
间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f g : ℝ → ℝ},   AkraBazziRecurrence.GrowsPolynomially g →     Asymptoti
cs.IsEquivalent Filter.atTop f g → AkraBazziRecurrence.GrowsPolynomially f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.add_isLittleO`：∀ {f g : ℝ → ℝ},   
AkraBazziRecurrence.GrowsPolynomially f →     g =o[Filter.atTop] f → AkraBazziRe
currence.GrowsPolynomially fun x => f x +…
-/
lemma GrowsPolynomially.of_isEquivalent {f g : ℝ → ℝ} (hg : GrowsPolynomially g)
    (hf : f ~[atTop] g) : GrowsPolynomially f := by
  have : f = g + (f - g) := by ext; simp
  rw [this]
  exact add_isLittleO hg hf
/-
**AkraBazziRecurrence.GrowsPolynomially.of_isEquivalent_const** 是 Mathlib 中的一个定理
，位于命名空间 `AkraBazziRecurrence.GrowsPolynomially`。
形式化陈述：∀ {f : ℝ → ℝ} {c : ℝ}, (Asymptotics.IsEquivalent Filter.atTop f fun x => c
) → AkraBazziRecurrence.GrowsPolynomially f
参数：Asymptotics.IsEquivalent Filter.atTop f fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.of_isEquivalent`：∀ {f g : ℝ → ℝ}, 
  AkraBazziRecurrence.GrowsPolynomially g →     Asymptotics.IsEquivalent Filter.
atTop f g → AkraBazziRecurrence.GrowsPolyno…
· 使用引理 `AkraBazziRecurrence.growsPolynomially_const`：growsPolynomially_const {c 
: Real} : GrowsPolynomially (fun _ => c)
-/
lemma GrowsPolynomially.of_isEquivalent_const {f : ℝ → ℝ} {c : ℝ} (hf : f ~[atTop] fun _ => c) :
    GrowsPolynomially f :=
  of_isEquivalent growsPolynomially_const hf

end AkraBazziRecurrence

