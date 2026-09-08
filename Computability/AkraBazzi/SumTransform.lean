/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.GrowsPolynomially
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Positivity

/-!
# Akra-Bazzi theorem: the sum transform

We develop further preliminaries required for the theorem, up to the sum transform.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above, together with basic bounds on `r i n`
  and positivity of `T`.
* `AkraBazziRecurrence.smoothingFn`: the smoothing function $\varepsilon(x) = 1 / \log x$ used in
  the inductive estimates, along with monotonicity, differentiability, and asymptotic properties.
* `AkraBazziRecurrence.p`: the unique Akra–Bazzi exponent characterized by $\sum_i a_i\,(b_i)^p = 1$
  and supporting analytical lemmas such as continuity and injectivity of the defining sum.
* `AkraBazziRecurrence.sumTransform`: the transformation that turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)` and its eventual comparison with multiples of `g n`.
* `AkraBazziRecurrence.asympBound`: the asymptotic bound satisfied by an Akra-Bazzi recurrence,
  namely `n^p (1 + ∑ g(u) / u^(p+1))`, together with positivity statements along the branches
  `r i n`.


## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

/-!
### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence relation
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

/-- An Akra-Bazzi recurrence is a function that satisfies the recurrence
`T n = (∑ i, a i * T (r i n)) + g n`. -/
/-
**AkraBazziRecurrence** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [Fintype α] → [Nonempty α] → (ℕ → ℝ) → (ℝ → ℝ) → (α → ℝ) 
→ (α → ℝ) → (α → ℕ → ℕ) → Type
参数：ℕ → ℝ；ℝ → ℝ；α → ℝ；α → ℝ；α → ℕ → ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Akra-Bazzi recurrence is a function that satisfies the recurrence
`T n = (∑ i, a i * T (r i n)) + g n`.
-/
structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : ℕ → ℝ) (g : ℝ → ℝ) (a : α → ℝ) (b : α → ℝ) (r : α → ℕ → ℕ) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : ℕ
  /-- `n₀` is always positive -/
  n₀_gt_zero : 0 < n₀
  /-- The coefficients `a i` are positive. -/
  a_pos : ∀ i, 0 < a i
  /-- The coefficients `b i` are positive. -/
  b_pos : ∀ i, 0 < b i
  /-- The coefficients `b i` are less than 1. -/
  b_lt_one : ∀ i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : ∀ x ≥ 0, 0 ≤ g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : ℕ) (hn₀ : n₀ ≤ n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : ℕ) (hn : n < n₀) : 0 < T n
  /-- The functions `r i` always reduce `n`. -/
  r_lt_n : ∀ i n, n₀ ≤ n → r i n < n
  /-- The functions `r i` approximate the values `b i * n`. -/
  dist_r_b : ∀ i, (fun n => (r i n : ℝ) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

/-- Smallest `b i` -/
/-
**AkraBazziRecurrence.min_bi** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：min_bi (b : α -> Real) : α
参数：b : α -> Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_min`：Finite.exists_min [Finite α] [Nonempty α] [LinearOrde
r β] (f : α -> β) : exists x₀ : α, forall x, f x₀ <= f x

--- 原说明 ---
Smallest `b i`
-/
noncomputable def min_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_min b

/-- Largest `b i` -/
/-
**AkraBazziRecurrence.max_bi** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：max_bi (b : α -> Real) : α
参数：b : α -> Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_max`：Finite.exists_max [Finite α] [Nonempty α] [LinearOrde
r β] (f : α -> β) : exists x₀ : α, forall x, f x <= f x₀

--- 原说明 ---
Largest `b i`
-/
noncomputable def max_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_max b

@[aesop safe apply]
/-
**AkraBazziRecurrence.min_bi_le** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：min_bi_le {b : α -> Real} (i : α) : b (min_bi b) <= b i
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Finite.exists_min`：Finite.exists_min [Finite α] [Nonempty α] [LinearOrde
r β] (f : α -> β) : exists x₀ : α, forall x, f x₀ <= f x
-/
lemma min_bi_le {b : α → ℝ} (i : α) : b (min_bi b) ≤ b i :=
  Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]
/-
**AkraBazziRecurrence.max_bi_le** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：max_bi_le {b : α -> Real} (i : α) : b i <= b (max_bi b)
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Finite.exists_max`：Finite.exists_max [Finite α] [Nonempty α] [LinearOrde
r β] (f : α -> β) : exists x₀ : α, forall x, f x <= f x₀
-/
lemma max_bi_le {b : α → ℝ} (i : α) : b i ≤ b (max_bi b) :=
  Classical.choose_spec (Finite.exists_max b) i

end min_max

/-
**AkraBazziRecurrence.isLittleO_self_div_log_id** 是 Mathlib 中的一个引理，位于命名空间 `AkraB
azziRecurrence`。
形式化陈述：isLittleO_self_div_log_id : (fun (n : Nat) => n / log n ^ 2) =o[atTop] (fu
n (n : Nat) => (n : Real))
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
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Ty
pe u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : F
ilter α} {f : α → 𝕜…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Asymptotics.IsLittleO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Semi
normedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Fi
lter α} {f : α …
· 使用定理 `Asymptotics.IsLittleO.natCast_atTop`：∀ {E : Type u_3} {F : Type u_4} [in
st : Norm E] [inst_1 : Norm F] {R : Type u_17} [inst_2 : Semiring R]   [inst_3 :
 PartialOrder R] [IsStric…
· 使用定理 `Real.isLittleO_const_log_atTop`：isLittleO_const_log_atTop {c : Real} : (
fun _ => c) =o[atTop] log
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 33 条，此处仅展示前 30 条）
-/
lemma isLittleO_self_div_log_id :
    (fun (n : ℕ) => n / log n ^ 2) =o[atTop] (fun (n : ℕ) => (n : ℝ)) := by
  calc (fun (n : ℕ) => (n : ℝ) / log n ^ 2)
    _ = fun (n : ℕ) => (n : ℝ) * ((log n) ^ 2)⁻¹ := by simp_rw [div_eq_mul_inv]
    _ =o[atTop] fun (n : ℕ) => (n : ℝ) * 1⁻¹ := by
      refine IsBigO.mul_isLittleO (isBigO_refl _ _) ?_
      refine IsLittleO.inv_rev ?_ (by simp)
      calc
        _ = (fun (_ : ℕ) => ((1 : ℝ) ^ 2)) := by simp
        _ =o[atTop] (fun (n : ℕ) => (log n) ^ 2) :=
          IsLittleO.pow (IsLittleO.natCast_atTop <| isLittleO_const_log_atTop) (by norm_num)
    _ = (fun (n : ℕ) => (n : ℝ)) := by ext; simp

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)
section
include R

/-
**AkraBazziRecurrence.dist_r_b'** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：dist_r_b' : forallᶠ n in atTop, forall i, ‖(r i n : Real) - b i * n‖ <= n 
/ log n ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Asymptotics.IsLittleO.eventuallyLE`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter
 α},   f =o[l] g → ∀ᶠ (x…
· 使用定理 `AkraBazziRecurrence.dist_r_b`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
-/
lemma dist_r_b' : ∀ᶠ n in atTop, ∀ i, ‖(r i n : ℝ) - b i * n‖ ≤ n / log n ^ 2 := by
  rw [Filter.eventually_all]
  intro i
  simpa using IsLittleO.eventuallyLE (R.dist_r_b i)
/-
**AkraBazziRecurrence.eventually_b_le_r** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：eventually_b_le_r : forallᶠ (n : Nat) in atTop, forall i, (b i : Real) * n
 - (n / log n ^ 2) <= r i n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.dist_r_b'`：dist_r_b' : forallᶠ n in atTop, forall i,
 ‖(r i n : Real) - b i * n‖ <= n / log n ^ 2
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
-/
lemma eventually_b_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i : ℝ) * n - (n / log n ^ 2) ≤ r i n := by
  filter_upwards [R.dist_r_b'] with n hn i
  have h₁ : 0 ≤ b i := le_of_lt <| R.b_pos _
  rw [sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add]
  calc (b i : ℝ) * n - r i n
    _ = ‖b i * n‖ - ‖(r i n : ℝ)‖ := by
      simp only [norm_mul, RCLike.norm_natCast, Real.norm_of_nonneg h₁]
    _ ≤ ‖(b i * n : ℝ) - r i n‖ := norm_sub_norm_le _ _
    _ = ‖(r i n : ℝ) - b i * n‖ := norm_sub_rev _ _
    _ ≤ n / log n ^ 2 := hn i
/-
**AkraBazziRecurrence.eventually_r_le_b** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：eventually_r_le_b : forallᶠ (n : Nat) in atTop, forall i, r i n <= (b i : 
Real) * n + (n / log n ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.dist_r_b'`：dist_r_b' : forallᶠ n in atTop, forall i,
 ‖(r i n : Real) - b i * n‖ <= n / log n ^ 2
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 40 条，此处仅展示前 30 条）
-/
lemma eventually_r_le_b : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ (b i : ℝ) * n + (n / log n ^ 2) := by
  filter_upwards [R.dist_r_b'] with n hn i
  calc r i n = b i * n + (r i n - b i * n) := by ring
             _ ≤ b i * n + ‖r i n - b i * n‖ := by gcongr; exact Real.le_norm_self _
             _ ≤ b i * n + n / log n ^ 2 := by gcongr; exact hn i
/-
**AkraBazziRecurrence.eventually_r_lt_n** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：eventually_r_lt_n : forallᶠ (n : Nat) in atTop, forall i, r i n < n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `AkraBazziRecurrence.r_lt_n`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 
: Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Ak
raBazziRecurrenc…
-/
lemma eventually_r_lt_n : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n < n := by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn i using R.r_lt_n i n hn
/-
**AkraBazziRecurrence.eventually_bi_mul_le_r** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazz
iRecurrence`。
形式化陈述：eventually_bi_mul_le_r : forallᶠ (n : Nat) in atTop, forall i, (b (min_bi 
b) / 2) * n <= r i n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用引理 `AkraBazziRecurrence.isLittleO_self_div_log_id`：isLittleO_self_div_log_id
 : (fun (n : Nat) => n / log n ^ 2) =o[atTop] (fun (n : Nat) => (n : Real))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_b_le_r`：eventually_b_le_r : forallᶠ (n : 
Nat) in atTop, forall i, (b i : Real) * n - (n / log n ^ 2) <= r i n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 71 条，此处仅展示前 30 条）
-/
lemma eventually_bi_mul_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b (min_bi b) / 2) * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn' i
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] at hn
  calc b (min_bi b) / 2 * n
    _ = b (min_bi b) * n - b (min_bi b) / 2 * n := by ring
    _ ≤ b (min_bi b) * n - ‖n / log n ^ 2‖ := by gcongr
    _ ≤ b i * n - ‖n / log n ^ 2‖ := by gcongr; aesop
    _ = b i * n - n / log n ^ 2 := by
      congr
      exact Real.norm_of_nonneg <| by positivity
    _ ≤ r i n := hn' i
/-
**AkraBazziRecurrence.bi_min_div_two_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazzi
Recurrence`。
形式化陈述：bi_min_div_two_lt_one : b (min_bi b) / 2 < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AkraBazziRecurrence.b_lt_one`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
-/
lemma bi_min_div_two_lt_one : b (min_bi b) / 2 < 1 := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2
    _ < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
    _ < 1 := R.b_lt_one _
/-
**AkraBazziRecurrence.bi_min_div_two_pos** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRec
urrence`。
形式化陈述：bi_min_div_two_pos : 0 < b (min_bi b) / 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma bi_min_div_two_pos : 0 < b (min_bi b) / 2 := div_pos (R.b_pos _) (by simp)
/-
**AkraBazziRecurrence.exists_eventually_const_mul_le_r** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：exists_eventually_const_mul_le_r : exists c in Set.Ioo (0 : Real) 1, foral
lᶠ (n : Nat) in atTop, forall i, c * n <= r i n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
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
· 使用引理 `AkraBazziRecurrence.bi_min_div_two_lt_one`：bi_min_div_two_lt_one : b (mi
n_bi b) / 2 < 1
· 使用引理 `AkraBazziRecurrence.eventually_bi_mul_le_r`：eventually_bi_mul_le_r : for
allᶠ (n : Nat) in atTop, forall i, (b (min_bi b) / 2) * n <= r i n
-/
lemma exists_eventually_const_mul_le_r :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩
/-
**AkraBazziRecurrence.eventually_r_ge** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurr
ence`。
形式化陈述：eventually_r_ge (C : Real) : forallᶠ (n : Nat) in atTop, forall i, C <= r 
i n
参数：C : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.exists_eventually_const_mul_le_r`：exists_eventually_
const_mul_le_r : exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, f
orall i, c * n <= r i n
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma eventually_r_ge (C : ℝ) : ∀ᶠ (n : ℕ) in atTop, ∀ i, C ≤ r i n := by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂ i
  have h₁ := hc_mem.1
  calc C
    _ = c * (C / c) := by
      rw [← mul_div_assoc]
      exact (mul_div_cancel_left₀ _ (by positivity)).symm
    _ ≤ c * ⌈C / c⌉₊ := by gcongr; simp [Nat.le_ceil]
    _ ≤ c * n := by gcongr
    _ ≤ r i n := hn₂ i
/-
**AkraBazziRecurrence.tendsto_atTop_r** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurr
ence`。
形式化陈述：tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop
参数：i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用引理 `AkraBazziRecurrence.eventually_r_ge`：eventually_r_ge (C : Real) : forall
ᶠ (n : Nat) in atTop, forall i, C <= r i n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i
/-
**AkraBazziRecurrence.tendsto_atTop_r_real** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziR
ecurrence`。
形式化陈述：tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : Real)) atTop atT
op
参数：i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_r`：tendsto_atTop_r (i : α) : Tendsto (
r i) atTop atTop
-/
lemma tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : ℝ)) atTop atTop :=
  Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)
/-
**AkraBazziRecurrence.exists_eventually_r_le_const_mul** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：exists_eventually_r_le_const_mul : exists c in Set.Ioo (0 : Real) 1, foral
lᶠ (n : Nat) in atTop, forall i, r i n <= c * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `AkraBazziRecurrence.b_lt_one`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 105 条，此处仅展示前 30 条）
-/
lemma exists_eventually_r_le_const_mul :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ c * n := by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by positivity
  have hc_lt_one : c < 1 :=
    calc b (max_bi b) + (1 - b (max_bi b)) / 2
      _ = b (max_bi b) * (1 / 2) + 1 / 2 := by ring
      _ < 1 * (1 / 2) + 1 / 2 := by gcongr; exact R.b_lt_one _
      _ = 1 := by norm_num
  refine ⟨c, ⟨hc_pos, hc_lt_one⟩, ?_⟩
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo h₁
  filter_upwards [hlo', R.eventually_r_le_b] with n hn hn'
  intro i
  rw [Real.norm_of_nonneg (by positivity)] at hn
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] at hn
  calc r i n ≤ b i * n + n / log n ^ 2 := by exact hn' i
             _ ≤ b i * n + (1 - b (max_bi b)) / 2 * n := by gcongr
             _ = (b i + (1 - b (max_bi b)) / 2) * n := by ring
             _ ≤ (b (max_bi b) + (1 - b (max_bi b)) / 2) * n := by gcongr; exact max_bi_le _
/-
**AkraBazziRecurrence.eventually_r_pos** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecur
rence`。
形式化陈述：eventually_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < r i n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_r`：tendsto_atTop_r (i : α) : Tendsto (
r i) atTop atTop
-/
lemma eventually_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < r i n := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0
/-
**AkraBazziRecurrence.eventually_log_b_mul_pos** 是 Mathlib 中的一个引理，位于命名空间 `AkraBa
zziRecurrence`。
形式化陈述：eventually_log_b_mul_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < log (
b i * n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
lemma eventually_log_b_mul_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < log (b i * n) := by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : ℕ) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
      <| Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0
/-
**AkraBazziRecurrence.T_pos** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} 
{r : α → ℕ → ℕ} [inst_1 : Nonempty α]   (R : AkraBazziRecurrence T g a b r) (n :
 ℕ), 0 < T n
参数：R : AkraBazziRecurrence T g a b r；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `AkraBazziRecurrence.T_gt_zero'`：∀ {α : Type u_1} [inst : Fintype α] [ins
t_1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self 
: AkraBazziRecurrenc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AkraBazziRecurrence.h_rec`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `AkraBazziRecurrence.g_nonneg`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AkraBazziRecurrence.a_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `AkraBazziRecurrence.r_lt_n`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 
: Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Ak
raBazziRecurrenc…
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
@[aesop safe apply] lemma T_pos (n : ℕ) : 0 < T n := by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempty) (by simp_all)
      exact fun i _ => mul_pos (R.a_pos i) <| h_ind _ (R.r_lt_n i _ hn)

@[aesop safe apply]
/-
**AkraBazziRecurrence.T_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：T_nonneg (n : Nat) : 0 <= T n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `AkraBazziRecurrence.T_pos`：∀ {α : Type u_1} [inst : Fintype α] {T : ℕ → 
ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ} [inst_1 : Nonempty α]   (R : AkraBa
zziRecurrence T…
-/
lemma T_nonneg (n : ℕ) : 0 ≤ T n := le_of_lt <| R.T_pos n

end

/-!
### Smoothing function

We define `ε` as the "smoothing function" `fun n => 1 / log n`, which will be used in the form of a
factor of `1 ± ε n` needed to make the induction step go through.

This is its own definition to make it easier to switch to a different smoothing function.
For example, choosing `1 / log n ^ δ` for a suitable choice of `δ` leads to a slightly tighter
theorem at the price of a more complicated proof.

This part of the file then proves several properties of this function that will be needed later in
the proof.
-/

/-- The "smoothing function" is defined as `1 / log n`. This is defined as an `ℝ → ℝ` function
as opposed to `ℕ → ℝ` since this is more convenient for the proof, where we need to e.g. take
derivatives. -/
/-
**AkraBazziRecurrence.smoothingFn** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecurrence
`。
形式化陈述：smoothingFn (n : Real) : Real
参数：n : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "smoothing function" is defined as `1 / log n`. This is defined as an `ℝ → ℝ
` function
as opposed to `ℕ → ℝ` since this is more convenient for the proof, where we need
 to e.g. take
derivatives.
-/
noncomputable def smoothingFn (n : ℝ) : ℝ := 1 / log n

local notation "ε" => smoothingFn
/-
**AkraBazziRecurrence.one_add_smoothingFn_le_two** 是 Mathlib 中的一个引理，位于命名空间 `Akra
BazziRecurrence`。
形式化陈述：one_add_smoothingFn_le_two {x : Real} (hx : exp 1 <= x) : 1 + ε x <= 2
参数：hx : exp 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma one_add_smoothingFn_le_two {x : ℝ} (hx : exp 1 ≤ x) : 1 + ε x ≤ 2 := by
  simp only [smoothingFn, ← one_add_one_eq_two]
  gcongr
  have : 1 < x := by
    calc 1 = exp 0 := by simp
         _ < exp 1 := by simp
         _ ≤ x := hx
  rw [div_le_one (log_pos this)]
  calc 1 = log (exp 1) := by simp
       _ ≤ log x := log_le_log (exp_pos _) hx
/-
**AkraBazziRecurrence.isLittleO_smoothingFn_one** 是 Mathlib 中的一个引理，位于命名空间 `AkraB
azziRecurrence`。
形式化陈述：isLittleO_smoothingFn_one : ε =o[atTop] (fun _ => (1 : Real))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto`：∀ {α : Type u_1} {𝕜 : Type u_15} [inst
 : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ (x : α), g x = 0 → f
 x = 0) → Filter.Tends…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
lemma isLittleO_smoothingFn_one : ε =o[atTop] (fun _ => (1 : ℝ)) := by
  unfold smoothingFn
  refine isLittleO_of_tendsto (fun _ h => False.elim <| one_ne_zero h) ?_
  simp only [one_div, div_one]
  exact Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop
/-
**AkraBazziRecurrence.isEquivalent_one_add_smoothingFn_one** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ 
=> (1 : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用引理 `AkraBazziRecurrence.isLittleO_smoothingFn_one`：isLittleO_smoothingFn_one
 : ε =o[atTop] (fun _ => (1 : Real))
-/
lemma isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one
/-
**AkraBazziRecurrence.isEquivalent_one_sub_smoothingFn_one** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ 
=> (1 : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.sub_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用引理 `AkraBazziRecurrence.isLittleO_smoothingFn_one`：isLittleO_smoothingFn_one
 : ε =o[atTop] (fun _ => (1 : Real))
-/
lemma isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one
/-
**AkraBazziRecurrence.growsPolynomially_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence`。
形式化陈述：growsPolynomially_one_sub_smoothingFn : GrowsPolynomially fun x => 1 - ε x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.of_isEquivalent_const`：∀ {f : ℝ → 
ℝ} {c : ℝ}, (Asymptotics.IsEquivalent Filter.atTop f fun x => c) → AkraBazziRecu
rrence.GrowsPolynomially f
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_sub_smoothingFn_one`：isEquivalent_o
ne_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real))
-/
lemma growsPolynomially_one_sub_smoothingFn : GrowsPolynomially fun x => 1 - ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_sub_smoothingFn_one
/-
**AkraBazziRecurrence.growsPolynomially_one_add_smoothingFn** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence`。
形式化陈述：growsPolynomially_one_add_smoothingFn : GrowsPolynomially fun x => 1 + ε x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.GrowsPolynomially.of_isEquivalent_const`：∀ {f : ℝ → 
ℝ} {c : ℝ}, (Asymptotics.IsEquivalent Filter.atTop f fun x => c) → AkraBazziRecu
rrence.GrowsPolynomially f
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_add_smoothingFn_one`：isEquivalent_o
ne_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : Real))
-/
lemma growsPolynomially_one_add_smoothingFn : GrowsPolynomially fun x => 1 + ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_add_smoothingFn_one
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const_real** 是 Mathlib 中
的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_gt_const_real (c : Real) (hc : c < 1) : for
allᶠ (x : Real) in atTop, c < 1 - ε x
参数：c : Real；hc : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isEquivalent_const_iff_tendsto`：isEquivalent_const_iff_tends
to {c : β} (h : c != 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_sub_smoothingFn_one`：isEquivalent_o
ne_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma eventually_one_sub_smoothingFn_gt_const_real (c : ℝ) (hc : c < 1) :
    ∀ᶠ (x : ℝ) in atTop, c < 1 - ε x := by
  have h₁ : Tendsto (fun x => 1 - ε x) atTop (𝓝 1) := by
    rw [← isEquivalent_const_iff_tendsto one_ne_zero]
    exact isEquivalent_one_sub_smoothingFn_one
  rw [tendsto_order] at h₁
  exact h₁.1 c hc
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const** 是 Mathlib 中的一个引理
，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_gt_const (c : Real) (hc : c < 1) : forallᶠ 
(n : Nat) in atTop, c < 1 - ε n
参数：c : Real；hc : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const_real`：eventu
ally_one_sub_smoothingFn_gt_const_real (c : Real) (hc : c < 1) : forallᶠ (x : Re
al) in atTop, c < 1 - ε x
-/
lemma eventually_one_sub_smoothingFn_gt_const (c : ℝ) (hc : c < 1) :
    ∀ᶠ (n : ℕ) in atTop, c < 1 - ε n :=
  Eventually.natCast_atTop (p := fun n => c < 1 - ε n)
    <| eventually_one_sub_smoothingFn_gt_const_real c hc
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos_real** 是 Mathlib 中的一个引理
，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_pos_real : forallᶠ (x : Real) in atTop, 0 <
 1 - ε x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const_real`：eventu
ally_one_sub_smoothingFn_gt_const_real (c : Real) (hc : c < 1) : forallᶠ (x : Re
al) in atTop, c < 1 - ε x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma eventually_one_sub_smoothingFn_pos_real : ∀ᶠ (x : ℝ) in atTop, 0 < 1 - ε x :=
  eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos** 是 Mathlib 中的一个引理，位于命名
空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 - ε
 n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos_real`：eventually_
one_sub_smoothingFn_pos_real : forallᶠ (x : Real) in atTop, 0 < 1 - ε x
-/
lemma eventually_one_sub_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 - ε n :=
  eventually_one_sub_smoothingFn_pos_real.natCast_atTop
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_nonneg** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_nonneg : forallᶠ (n : Nat) in atTop, 0 <= 1
 - ε n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos`：eventually_one_s
ub_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 - ε n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma eventually_one_sub_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 - ε n := by
  filter_upwards [eventually_one_sub_smoothingFn_pos] with n hn; exact le_of_lt hn

include R in
/-
**AkraBazziRecurrence.eventually_one_sub_smoothingFn_r_pos** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_sub_smoothingFn_r_pos : forallᶠ (n : Nat) in atTop, forall 
i, 0 < 1 - ε (r i n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_r_real`：tendsto_atTop_r_real (i : α) :
 Tendsto (fun n => (r i n : Real)) atTop atTop
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos_real`：eventually_
one_sub_smoothingFn_pos_real : forallᶠ (x : Real) in atTop, 0 < 1 - ε x
-/
lemma eventually_one_sub_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 - ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r_real i).eventually eventually_one_sub_smoothingFn_pos_real

@[aesop safe apply]
/-
**AkraBazziRecurrence.differentiableAt_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间 `Ak
raBazziRecurrence`。
形式化陈述：differentiableAt_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Re
al ε x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_ne_zero_of_pos_of_ne_one`：log_ne_zero_of_pos_of_ne_one {x : Rea
l} (hx_pos : 0 < x) (hx : x != 1) : log x != 0
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `DifferentiableAt.inv`：DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z)
 (hz : h z != 0) : DifferentiableAt 𝕜 (h⁻¹) z
· 使用定理 `Real.differentiableAt_log`：∀ {x : ℝ}, x ≠ 0 → DifferentiableAt ℝ Real.lo
g x
-/
lemma differentiableAt_smoothingFn {x : ℝ} (hx : 1 < x) : DifferentiableAt ℝ ε x := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change DifferentiableAt ℝ (fun z => 1 / log z) x
  simp_rw [one_div]
  exact DifferentiableAt.inv (differentiableAt_log (by positivity)) this

@[aesop safe apply]
/-
**AkraBazziRecurrence.differentiableAt_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：differentiableAt_one_sub_smoothingFn {x : Real} (hx : 1 < x) : Differentia
bleAt Real (fun z => 1 - ε z) x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
-/
lemma differentiableAt_one_sub_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 - ε z) x :=
  DifferentiableAt.sub (differentiableAt_const _) <| differentiableAt_smoothingFn hx
/-
**AkraBazziRecurrence.differentiableOn_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：differentiableOn_one_sub_smoothingFn : DifferentiableOn Real (fun z => 1 -
 ε z) (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `AkraBazziRecurrence.differentiableAt_one_sub_smoothingFn`：differentiable
At_one_sub_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real (fun z =>
 1 - ε z) x
-/
lemma differentiableOn_one_sub_smoothingFn : DifferentiableOn ℝ (fun z => 1 - ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt

@[aesop safe apply]
/-
**AkraBazziRecurrence.differentiableAt_one_add_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：differentiableAt_one_add_smoothingFn {x : Real} (hx : 1 < x) : Differentia
bleAt Real (fun z => 1 + ε z) x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
-/
lemma differentiableAt_one_add_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 + ε z) x :=
  DifferentiableAt.add (differentiableAt_const _) <| differentiableAt_smoothingFn hx
/-
**AkraBazziRecurrence.differentiableOn_one_add_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：differentiableOn_one_add_smoothingFn : DifferentiableOn Real (fun z => 1 +
 ε z) (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `AkraBazziRecurrence.differentiableAt_one_add_smoothingFn`：differentiable
At_one_add_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real (fun z =>
 1 + ε z) x
-/
lemma differentiableOn_one_add_smoothingFn : DifferentiableOn ℝ (fun z => 1 + ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_add_smoothingFn hx).differentiableWithinAt
/-
**AkraBazziRecurrence.deriv_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：deriv_smoothingFn {x : Real} : deriv ε x = -x⁻¹ / (log x ^ 2)
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_inv_log`：deriv_inv_log : deriv (fun x => (log x)⁻¹) = fun x =
> -x⁻¹ / log x ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_smoothingFn {x : ℝ} : deriv ε x = -x⁻¹ / (log x ^ 2) := by
  unfold smoothingFn
  simp
/-
**AkraBazziRecurrence.isLittleO_deriv_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间 `Akr
aBazziRecurrence`。
形式化陈述：isLittleO_deriv_smoothingFn : deriv ε =o[atTop] fun x => x⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AkraBazziRecurrence.deriv_smoothingFn`：deriv_smoothingFn {x : Real} : de
riv ε x = -x⁻¹ / (log x ^ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Ty
pe u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : F
ilter α} {f : α → 𝕜…
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_neg_right`：isBigO_neg_right : (f =O[l] fun x => -g' x
) ↔ f =O[l] g'
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.isLittleO_one_left_iff`：isLittleO_one_left_iff : (fun _x => 
1 : α -> F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_atTop_atTop`：tendsto_norm_atTop_atTop : Tendsto (norm : Rea
l -> Real) atTop atTop
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
（共 35 条，此处仅展示前 30 条）
-/
lemma isLittleO_deriv_smoothingFn : deriv ε =o[atTop] fun x => x⁻¹ :=
  calc deriv ε
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      rw [deriv_smoothingFn]
    _ = fun x => (-x * log x ^ 2)⁻¹ := by
      simp_rw [neg_div, div_eq_mul_inv, ← mul_inv, neg_inv, neg_mul]
    _ =o[atTop] fun x => (x * 1)⁻¹ := by
      refine IsLittleO.inv_rev ?_ ?_
      · refine IsBigO.mul_isLittleO
          (by rw [isBigO_neg_right]; aesop (add safe isBigO_refl)) ?_
        rw [isLittleO_one_left_iff]
        exact Tendsto.comp tendsto_norm_atTop_atTop
          <| Tendsto.comp (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
      · exact Filter.Eventually.of_forall (fun x hx => by rw [mul_one] at hx; simp [hx])
    _ = fun x => x⁻¹ := by simp
/-
**AkraBazziRecurrence.eventually_deriv_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_deriv_one_sub_smoothingFn : deriv (fun x => 1 - ε x) =ᶠ[atTop] 
fun x => x⁻¹ / (log x ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_sub`：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y - g y) x = deriv f x - deriv g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AkraBazziRecurrence.deriv_smoothingFn`：deriv_smoothingFn {x : Real} : de
riv ε x = -x⁻¹ / (log x ^ 2)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma eventually_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) :=
  calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] -(deriv ε) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn, neg_div]
/-
**AkraBazziRecurrence.eventually_deriv_one_add_smoothingFn** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_deriv_one_add_smoothingFn : deriv (fun x => 1 + ε x) =ᶠ[atTop] 
fun x => -x⁻¹ / (log x ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_add`：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AkraBazziRecurrence.deriv_smoothingFn`：deriv_smoothingFn {x : Real} : de
riv ε x = -x⁻¹ / (log x ^ 2)
-/
lemma eventually_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) :=
  calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] deriv ε := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn]
/-
**AkraBazziRecurrence.isLittleO_deriv_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位于命
名空间 `AkraBazziRecurrence`。
形式化陈述：isLittleO_deriv_one_sub_smoothingFn : deriv (fun x => 1 - ε x) =o[atTop] f
un (x : Real) => x⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_sub`：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y - g y) x = deriv f x - deriv g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.isLittleO_neg_left`：isLittleO_neg_left : (fun x => -f' x) =o
[l] g ↔ f' =o[l] g
· 使用引理 `AkraBazziRecurrence.isLittleO_deriv_smoothingFn`：isLittleO_deriv_smoothi
ngFn : deriv ε =o[atTop] fun x => x⁻¹
-/
lemma isLittleO_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =o[atTop] fun (x : ℝ) => x⁻¹ :=
  calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] fun z => -(deriv ε z) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn
/-
**AkraBazziRecurrence.isLittleO_deriv_one_add_smoothingFn** 是 Mathlib 中的一个引理，位于命
名空间 `AkraBazziRecurrence`。
形式化陈述：isLittleO_deriv_one_add_smoothingFn : deriv (fun x => 1 + ε x) =o[atTop] f
un (x : Real) => x⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_add`：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AkraBazziRecurrence.isLittleO_deriv_smoothingFn`：isLittleO_deriv_smoothi
ngFn : deriv ε =o[atTop] fun x => x⁻¹
-/
lemma isLittleO_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =o[atTop] fun (x : ℝ) => x⁻¹ :=
  calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] fun z => deriv ε z := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn
/-
**AkraBazziRecurrence.eventually_one_add_smoothingFn_pos** 是 Mathlib 中的一个引理，位于命名
空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_add_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 + ε
 n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.isLittleO_smoothingFn_one`：isLittleO_smoothingFn_one
 : ε =o[atTop] (fun _ => (1 : Real))
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
-/
lemma eventually_one_add_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 + ε n := by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by simp : (0 : ℝ) < 1 / 2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  change 0 < 1 + 1 / log x
  positivity

include R in
/-
**AkraBazziRecurrence.eventually_one_add_smoothingFn_r_pos** 是 Mathlib 中的一个引理，位于
命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_add_smoothingFn_r_pos : forallᶠ (n : Nat) in atTop, forall 
i, 0 < 1 + ε (r i n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_r`：tendsto_atTop_r (i : α) : Tendsto (
r i) atTop atTop
· 使用引理 `AkraBazziRecurrence.eventually_one_add_smoothingFn_pos`：eventually_one_a
dd_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 + ε n
-/
lemma eventually_one_add_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 + ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos
/-
**AkraBazziRecurrence.eventually_one_add_smoothingFn_nonneg** 是 Mathlib 中的一个引理，位
于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_one_add_smoothingFn_nonneg : forallᶠ (n : Nat) in atTop, 0 <= 1
 + ε n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_one_add_smoothingFn_pos`：eventually_one_a
dd_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 + ε n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma eventually_one_add_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 + ε n := by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn
/-
**AkraBazziRecurrence.strictAntiOn_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间 `AkraBa
zziRecurrence`。
形式化陈述：strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `StrictAntiOn.comp_strictMonoOn`：StrictAntiOn.comp_strictMonoOn (hg : Str
ictAntiOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g
 ∘ f) s
· 使用定理 `inv_strictAntiOn`：inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Se
t.Ioi 0)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1) := by
  change StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
  simp_rw [one_div]
  refine StrictAntiOn.comp_strictMonoOn inv_strictAntiOn ?log fun _ hx => log_pos hx
  refine StrictMonoOn.mono strictMonoOn_log (fun x hx => ?_)
  exact Set.Ioi_subset_Ioi zero_le_one hx
/-
**AkraBazziRecurrence.strictMonoOn_one_sub_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：strictMonoOn_one_sub_smoothingFn : StrictMonoOn (fun (x : Real) => (1 : Re
al) - ε x) (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `StrictMonoOn.const_add`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [
inst_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} {s : Set β}   [AddLeftStr
ictMono α], …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `StrictAntiOn.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [ins
t_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]   [inst_4 : Preor
der β]…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `AkraBazziRecurrence.strictAntiOn_smoothingFn`：strictAntiOn_smoothingFn :
 StrictAntiOn ε (Set.Ioi 1)
-/
lemma strictMonoOn_one_sub_smoothingFn :
    StrictMonoOn (fun (x : ℝ) => (1 : ℝ) - ε x) (Set.Ioi 1) := by
  simp_rw [sub_eq_add_neg]
  exact StrictMonoOn.const_add (StrictAntiOn.neg <| strictAntiOn_smoothingFn) 1
/-
**AkraBazziRecurrence.strictAntiOn_one_add_smoothingFn** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：strictAntiOn_one_add_smoothingFn : StrictAntiOn (fun (x : Real) => (1 : Re
al) + ε x) (Set.Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.const_add`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [
inst_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} {s : Set β}   [AddLeftStr
ictMono α], …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `AkraBazziRecurrence.strictAntiOn_smoothingFn`：strictAntiOn_smoothingFn :
 StrictAntiOn ε (Set.Ioi 1)
-/
lemma strictAntiOn_one_add_smoothingFn : StrictAntiOn (fun (x : ℝ) => (1 : ℝ) + ε x) (Set.Ioi 1) :=
  StrictAntiOn.const_add strictAntiOn_smoothingFn 1

section
include R

/-
**AkraBazziRecurrence.isEquivalent_smoothingFn_sub_self** 是 Mathlib 中的一个引理，位于命名空
间 `AkraBazziRecurrence`。
形式化陈述：isEquivalent_smoothingFn_sub_self (i : α) : (fun (n : Nat) => ε (b i * n) 
- ε n) ~[atTop] fun n => -log (b i) / (log n) ^ 2
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_log_b_mul_pos`：eventually_log_b_mul_pos :
 forallᶠ (n : Nat) in atTop, forall i, 0 < log (b i * n)
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_sub_inv`：inv_sub_inv {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ - b
⁻¹ = (b - a) / (a * b)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - (b + c) = a - b - c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 58 条，此处仅展示前 30 条）
-/
lemma isEquivalent_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) ~[atTop] fun n => -log (b i) / (log n) ^ 2 := by
  calc (fun (n : ℕ) => 1 / log (b i * n) - 1 / log n)
    _ =ᶠ[atTop] fun (n : ℕ) => (log n - log (b i * n)) / (log (b i * n) * log n) := by
      filter_upwards [eventually_gt_atTop 1, R.eventually_log_b_mul_pos] with n hn hn'
      have h_log_pos : 0 < log n := Real.log_pos <| by simp_all
      simp only [one_div]
      rw [inv_sub_inv (by have := hn' i; positivity) (by aesop)]
    _ =ᶠ[atTop] (fun (n : ℕ) ↦ (log n - log (b i) - log n) / ((log (b i) + log n) * log n)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      have : 0 < b i := R.b_pos i
      rw [log_mul (by positivity) (by simp_all), sub_add_eq_sub_sub]
    _ = (fun (n : ℕ) => -log (b i) / ((log (b i) + log n) * log n)) := by ext; congr; ring
    _ ~[atTop] (fun (n : ℕ) => -log (b i) / (log n * log n)) := by
      refine IsEquivalent.div (IsEquivalent.refl) <| IsEquivalent.mul ?_ (IsEquivalent.refl)
      have : (fun (n : ℕ) => log (b i) + log n) = fun (n : ℕ) => log n + log (b i) := by
        ext; simp [add_comm]
      rw [this]
      exact IsEquivalent.add_isLittleO IsEquivalent.refl
        <| IsLittleO.natCast_atTop (f := fun (_ : ℝ) => log (b i))
          isLittleO_const_log_atTop
    _ = (fun (n : ℕ) => -log (b i) / (log n) ^ 2) := by ext; congr 1; rw [← pow_two]
/-
**AkraBazziRecurrence.isTheta_smoothingFn_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `Ak
raBazziRecurrence`。
形式化陈述：isTheta_smoothingFn_sub_self (i : α) : (fun (n : Nat) => ε (b i * n) - ε n
) =Θ[atTop] fun n => 1 / (log n) ^ 2
参数：i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
· 使用引理 `AkraBazziRecurrence.isEquivalent_smoothingFn_sub_self`：isEquivalent_smoo
thingFn_sub_self (i : α) : (fun (n : Nat) => ε (b i * n) - ε n) ~[atTop] fun n =
> -log (b i) / (log n) ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Real.log_ne_zero_of_pos_of_ne_one`：log_ne_zero_of_pos_of_ne_one {x : Rea
l} (hx_pos : 0 < x) (hx : x != 1) : log x != 0
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `AkraBazziRecurrence.b_lt_one`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isTheta_const_mul_right`：isTheta_const_mul_right {c : 𝕜} {g 
: α -> 𝕜} (hc : c != 0) : (f =Θ[l] fun x => c * g x) ↔ f =Θ[l] g
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
-/
lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => 1 / (log n) ^ 2 := by
  calc (fun (n : ℕ) => ε (b i * n) - ε n)
    _ =Θ[atTop] fun n => (-log (b i)) / (log n) ^ 2 :=
      (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : ℕ) => (-log (b i)) * 1 / (log n) ^ 2 := by simp only [mul_one]
    _ = fun (n : ℕ) => -log (b i) * (1 / (log n) ^ 2) := by simp_rw [← mul_div_assoc]
    _ =Θ[atTop] fun (n : ℕ) => 1 / (log n) ^ 2 := by
      have : -log (b i) ≠ 0 := by
        rw [neg_ne_zero]
        exact Real.log_ne_zero_of_pos_of_ne_one (R.b_pos i) (ne_of_lt <| R.b_lt_one i)
      rw [← isTheta_const_mul_right this]

/-!
### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such that
`∑ a_i b_i^p = 1`. This section shows the existence and uniqueness of this exponent `p` for any
`R : AkraBazziRecurrence`. These results are used in the next section to define the asymptotic
bound expression. -/

@[continuity, fun_prop]
/-
**AkraBazziRecurrence.continuous_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `AkraBaz
ziRecurrence`。
形式化陈述：continuous_sumCoeffsExp : Continuous (fun (p : Real) => ∑ i, a i * (b i) ^
 p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.rpow`：Continuous.rpow (hf : Continuous f) (hg : Continuous g)
 (h : forall x, f x != 0 ∨ 0 < g x) : Continuous fun x => f x ^ g x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…

--- 原说明 ---
### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such
 that
`∑ a_i b_i^p = 1`. This section shows the existence and uniqueness of this expon
ent `p` for any
`R : AkraBazziRecurrence`. These results are used in the next section to define 
the asymptotic
bound expression.
-/
lemma continuous_sumCoeffsExp : Continuous (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine continuous_finsetSum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))
/-
**AkraBazziRecurrence.strictAnti_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `AkraBaz
ziRecurrence`。
形式化陈述：strictAnti_sumCoeffsExp : StrictAnti (fun (p : Real) => ∑ i, a i * (b i) ^
 p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用定理 `Finset.sum_induction_nonempty`：∀ {ι : Type u_1} {s : Finset ι} {M : Type
 u_7} [inst : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a →
 p b → p (a + b)) →…
· 使用定理 `StrictAnti.add`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [inst_1 :
 Preorder α] [inst_2 : Preorder β] {f g : β → α}   [AddLeftStrictMono α] [AddRig
htSt…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用引理 `StrictAnti.const_mul`：StrictAnti.const_mul [PosMulStrictMono M₀] (hf : S
trictAnti f) (ha : 0 < a) : StrictAnti fun x => a * f x
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Real.strictAnti_rpow_of_base_lt_one`：strictAnti_rpow_of_base_lt_one {b :
 Real} (hb₀ : 0 < b) (hb₁ : b < 1) : StrictAnti (b ^ · : Real -> Real)
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `AkraBazziRecurrence.b_lt_one`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `AkraBazziRecurrence.a_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
-/
lemma strictAnti_sumCoeffsExp : StrictAnti (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)
/-
**AkraBazziRecurrence.tendsto_zero_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `AkraB
azziRecurrence`。
形式化陈述：tendsto_zero_sumCoeffsExp : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ 
p) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `tendsto_rpow_atTop_of_base_lt_one`：tendsto_rpow_atTop_of_base_lt_one (b 
: Real) (hb₀ : -1 < b) (hb₁ : b < 1) : Tendsto (b ^ · : Real -> Real) atTop (𝓝 (
0 : Real))
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 60 条，此处仅展示前 30 条）
-/
lemma tendsto_zero_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0) := by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : ℝ)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finsetSum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
  refine Tendsto.mul (by simp) <| tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith
/-
**AkraBazziRecurrence.tendsto_atTop_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `Akra
BazziRecurrence`。
形式化陈述：tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^
 p) atBot atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `AkraBazziRecurrence.a_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用引理 `tendsto_rpow_atBot_of_base_lt_one`：tendsto_rpow_atBot_of_base_lt_one (b 
: Real) (hb₀ : 0 < b) (hb₁ : b < 1) : Tendsto (b ^ · : Real -> Real) atBot atTop
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 43 条，此处仅展示前 30 条）
-/
lemma tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atBot atTop := by
  have h₁ : Tendsto (fun p : ℝ => (a (max_bi b) : ℝ) * b (max_bi b) ^ p) atBot atTop :=
    Tendsto.const_mul_atTop (R.a_pos (max_bi b)) <| tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finset.single_le_sum (f := fun i => (a i : ℝ) * b i ^ p) (fun i _ => ?_) (mem_univ _)
  positivity [R.a_pos i, R.b_pos i]
/-
**AkraBazziRecurrence.one_mem_range_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `Akra
BazziRecurrence`。
形式化陈述：one_mem_range_sumCoeffsExp : 1 in Set.range (fun (p : Real) => ∑ i, a i * 
(b i) ^ p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_range_of_exists_le_of_exists_ge`：mem_range_of_exists_le_of_exists_ge
 [PreconnectedSpace X] {c : α} {f : X -> α} (hf : Continuous f) (h₁ : exists a, 
f a <= c) (h₂ : exists b,…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用引理 `AkraBazziRecurrence.continuous_sumCoeffsExp`：continuous_sumCoeffsExp : C
ontinuous (fun (p : Real) => ∑ i, a i * (b i) ^ p)
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_le_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `AkraBazziRecurrence.tendsto_zero_sumCoeffsExp`：tendsto_zero_sumCoeffsExp
 : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0)
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_sumCoeffsExp`：tendsto_atTop_sumCoeffsE
xp : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atBot atTop
-/
lemma one_mem_range_sumCoeffsExp : 1 ∈ Set.range (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
    exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one |>.exists
  case ge_one =>
    exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _ |>.exists

/-- The function x ↦ ∑ a_i b_i^x is injective. This implies the uniqueness of `p`. -/
/-
**AkraBazziRecurrence.injective_sumCoeffsExp** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazz
iRecurrence`。
形式化陈述：injective_sumCoeffsExp : Function.Injective (fun (p : Real) => ∑ i, a i * 
(b i) ^ p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用引理 `AkraBazziRecurrence.strictAnti_sumCoeffsExp`：strictAnti_sumCoeffsExp : S
trictAnti (fun (p : Real) => ∑ i, a i * (b i) ^ p)

--- 原说明 ---
The function x ↦ ∑ a_i b_i^x is injective. This implies the uniqueness of `p`.
-/
lemma injective_sumCoeffsExp : Function.Injective (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) :=
    R.strictAnti_sumCoeffsExp.injective

end

variable (a b) in
/-- The exponent `p` associated with a particular Akra-Bazzi recurrence. -/
noncomputable irreducible_def p : ℝ := Function.invFun (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) 1

include R in
-- Cannot be @[simp] because `T`, `g`, `r`, and `R` cannot be inferred by `simp`.
/-
**AkraBazziRecurrence.sumCoeffsExp_p_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazzi
Recurrence`。
形式化陈述：sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AkraBazziRecurrence.p_def`：∀ {α : Type u_2} [inst : Fintype α] (a b : α 
→ ℝ),   AkraBazziRecurrence.p a b = Function.invFun (fun p => ∑ i, a i * b i ^ p
) 1
· 使用定理 `Function.invFun_eq`：invFun_eq (h : exists a, f a = b) : f (invFun f b) =
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用引理 `AkraBazziRecurrence.one_mem_range_sumCoeffsExp`：one_mem_range_sumCoeffsE
xp : 1 in Set.range (fun (p : Real) => ∑ i, a i * (b i) ^ p)
-/
lemma sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1 := by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

/-!
### The sum transform

This section defines the "sum transform" of a function `g` as
`∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`, and uses it to define `asympBound` as the bound
satisfied by an Akra-Bazzi recurrence, namely `n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. Here, the
exponent `p` refers to the one established in the previous section.

Several properties of the sum transform are then proven.
-/

/-- The transformation that turns a function `g` into
`n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`. -/
/-
**AkraBazziRecurrence.sumTransform** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecurrenc
e`。
形式化陈述：sumTransform (p : Real) (g : Real -> Real) (n₀ n : Nat)
参数：p : Real；g : Real -> Real；n₀ n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transformation that turns a function `g` into
`n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`.
-/
noncomputable def sumTransform (p : ℝ) (g : ℝ → ℝ) (n₀ n : ℕ) :=
  n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)
/-
**AkraBazziRecurrence.sumTransform_def** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecur
rence`。
形式化陈述：sumTransform_def {p : Real} {g : Real -> Real} {n₀ n : Nat} : sumTransform
 p g n₀ n = n ^ p * ∑ u in Finset.Ico n₀ n, g u / u ^ (p + 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumTransform_def {p : ℝ} {g : ℝ → ℝ} {n₀ n : ℕ} :
    sumTransform p g n₀ n = n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1) := rfl


variable (g) (a) (b)
/-- The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
`n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/
/-
**AkraBazziRecurrence.asympBound** 是 Mathlib 中的一个定义，位于命名空间 `AkraBazziRecurrence`
。
形式化陈述：asympBound (n : Nat) : Real
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
`n^p (1 + ∑_{u < n} g(u) / u^(p+1))`.
-/
noncomputable def asympBound (n : ℕ) : ℝ := n ^ p a b + sumTransform (p a b) g 0 n
/-
**AkraBazziRecurrence.asympBound_def** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurre
nce`。
形式化陈述：asympBound_def {α} [Fintype α] (a b : α -> Real) {n : Nat} : asympBound g 
a b n = n ^ p a b + sumTransform (p a b) g 0 n
参数：a b : α -> Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma asympBound_def {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := rfl

variable {g} {a} {b}
/-
**AkraBazziRecurrence.asympBound_def'** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurr
ence`。
形式化陈述：asympBound_def' {α} [Fintype α] (a b : α -> Real) {n : Nat} : asympBound g
 a b n = n ^ p a b * (1 + (∑ u in range n, g u / u ^ (p a b + 1)))
参数：a b : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma asympBound_def' {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b * (1 + (∑ u ∈ range n, g u / u ^ (p a b + 1))) := by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

section
include R

/-
**AkraBazziRecurrence.asympBound_pos** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurre
nce`。
形式化陈述：asympBound_pos (n : Nat) (hn : 0 < n) : 0 < asympBound g a b n
参数：n : Nat；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `AkraBazziRecurrence.asympBound_def'`：asympBound_def' {α} [Fintype α] (a 
b : α -> Real) {n : Nat} : asympBound g a b n = n ^ p a b * (1 + (∑ u in range n
, g u / u ^ (p a b + 1)))
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AkraBazziRecurrence.g_nonneg`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma asympBound_pos (n : ℕ) (hn : 0 < n) : 0 < asympBound g a b n := by
  calc 0 < (n : ℝ) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ ≤ asympBound g a b n := by
        simp only [asympBound_def']
        gcongr n ^ p a b * (1 + ?_)
        have := R.g_nonneg
        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)
/-
**AkraBazziRecurrence.eventually_asympBound_pos** 是 Mathlib 中的一个引理，位于命名空间 `AkraB
azziRecurrence`。
形式化陈述：eventually_asympBound_pos : forallᶠ (n : Nat) in atTop, 0 < asympBound g a
 b n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `AkraBazziRecurrence.asympBound_pos`：asympBound_pos (n : Nat) (hn : 0 < n
) : 0 < asympBound g a b n
-/
lemma eventually_asympBound_pos : ∀ᶠ (n : ℕ) in atTop, 0 < asympBound g a b n := by
  filter_upwards [eventually_gt_atTop 0] with n hn using R.asympBound_pos n hn
/-
**AkraBazziRecurrence.eventually_asympBound_r_pos** 是 Mathlib 中的一个引理，位于命名空间 `Akr
aBazziRecurrence`。
形式化陈述：eventually_asympBound_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < as
ympBound g a b (r i n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `AkraBazziRecurrence.tendsto_atTop_r`：tendsto_atTop_r (i : α) : Tendsto (
r i) atTop atTop
· 使用引理 `AkraBazziRecurrence.eventually_asympBound_pos`：eventually_asympBound_pos
 : forallᶠ (n : Nat) in atTop, 0 < asympBound g a b n
-/
lemma eventually_asympBound_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < asympBound g a b (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos
/-
**AkraBazziRecurrence.eventually_atTop_sumTransform_le** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：eventually_atTop_sumTransform_le : exists c > 0, forallᶠ (n : Nat) in atTo
p, forall i, sumTransform (p a b) g (r i n) n <= c * g n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.exists_eventually_const_mul_le_r`：exists_eventually_
const_mul_le_r : exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, f
orall i, c * n <= r i n
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_le_nat`：eventuall
y_atTop_le_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) : e
xists c > 0, forallᶠ (n : Nat) in atTop, forall u i…
· 使用定理 `AkraBazziRecurrence.g_grows_poly`：∀ {α : Type u_1} [inst : Fintype α] [i
nst_1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (sel
f : AkraBazziRecurrenc…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用引理 `AkraBazziRecurrence.eventually_r_lt_n`：eventually_r_lt_n : forallᶠ (n : 
Nat) in atTop, forall i, r i n < n
· 使用引理 `AkraBazziRecurrence.eventually_r_pos`：eventually_r_pos : forallᶠ (n : Na
t) in atTop, forall i, 0 < r i n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `AkraBazziRecurrence.g_nonneg`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
（共 86 条，此处仅展示前 30 条）
-/
lemma eventually_atTop_sumTransform_le :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, sumTransform (p a b) g (r i n) n ≤ c * g n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_le_nat hc₁_mem
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  refine ⟨max c₂ (c₂ / c₁ ^ (p a b + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hrpos hr_lt_n hn_pos i
  have hrpos_i := hrpos i
  have g_nonneg : 0 ≤ g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ p a b + 1
    calc sumTransform (p a b) g (r i n) n
           = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
         _ ≤ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
          gcongr with u hu
          rw [Finset.mem_Ico] at hu
          have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by lia⟩
          refine hn₂ u ?_
          rw [Set.mem_Icc]
          refine ⟨?_, by norm_cast; lia⟩
          calc c₁ * n ≤ r i n := by exact hn₁ i
                    _ ≤ u := by exact_mod_cast hu'.1
         _ ≤ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          gcongr with u hu; rw [Finset.mem_Ico] at hu; exact hu.1
         _ ≤ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
          gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
         _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
          rw [nsmul_eq_mul, mul_assoc]
         _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
         _ ≤ n ^ (p a b) * n * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
         _ ≤ n ^ (p a b) * n * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          gcongr; exact hn₁ i
         _ = c₂ * g n * n ^ ((p a b) + 1) / (c₁ * n) ^ ((p a b) + 1) := by
          rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
         _ = c₂ * g n * n ^ ((p a b) + 1) / (n ^ ((p a b) + 1) * c₁ ^ ((p a b) + 1)) := by
          rw [mul_comm c₁, Real.mul_rpow (by positivity) (by positivity)]
         _ = c₂ * g n * (n ^ ((p a b) + 1) / (n ^ ((p a b) + 1))) / c₁ ^ ((p a b) + 1) := by ring
         _ = c₂ * g n / c₁ ^ ((p a b) + 1) := by rw [div_self (by positivity), mul_one]
         _ = (c₂ / c₁ ^ ((p a b) + 1)) * g n := by ring
         _ ≤ max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_right _ _
  | inr hp => -- p a b + 1 < 0
    calc sumTransform (p a b) g (r i n) n
      _ = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
      _ ≤ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n ≤ r i n := by exact hn₁ i
                  _ ≤ u := by exact_mod_cast hu'.1
      _ ≤ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr n ^ (p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
        rw [Finset.mem_Ico] at hu
        have : 0 < u := calc
          0 < r i n := by exact hrpos_i
          _ ≤ u := by exact hu.1
        exact rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast (le_of_lt hu.2)) (le_of_lt hp)
      _ ≤ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
        gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
        rw [nsmul_eq_mul, mul_assoc]
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ ≤ n ^ (p a b) * n * (c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
      _ = c₂ * (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) * g n := by
        rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = c₂ * g n := by rw [div_self (by positivity), mul_one]
      _ ≤ max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_left _ _
/-
**AkraBazziRecurrence.eventually_atTop_sumTransform_ge** 是 Mathlib 中的一个引理，位于命名空间
 `AkraBazziRecurrence`。
形式化陈述：eventually_atTop_sumTransform_ge : exists c > 0, forallᶠ (n : Nat) in atTo
p, forall i, c * g n <= sumTransform (p a b) g (r i n) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.exists_eventually_const_mul_le_r`：exists_eventually_
const_mul_le_r : exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, f
orall i, c * n <= r i n
· 使用引理 `AkraBazziRecurrence.GrowsPolynomially.eventually_atTop_ge_nat`：eventuall
y_atTop_ge_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) : e
xists c > 0, forallᶠ (n : Nat) in atTop, forall u i…
· 使用定理 `AkraBazziRecurrence.g_grows_poly`：∀ {α : Type u_1} [inst : Fintype α] [i
nst_1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (sel
f : AkraBazziRecurrenc…
· 使用引理 `AkraBazziRecurrence.exists_eventually_r_le_const_mul`：exists_eventually_
r_le_const_mul : exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, f
orall i, r i n <= c * n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 115 条，此处仅展示前 30 条）
-/
lemma eventually_atTop_sumTransform_ge :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * g n ≤ sumTransform (p a b) g (r i n) n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc₁_mem
  obtain ⟨c₃, hc₃_mem, hc₃⟩ := R.exists_eventually_r_le_const_mul
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  have hc₃' : 0 < (1 - c₃) := by have := hc₃_mem.2; linarith
  refine ⟨min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁^((p a b) + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, hc₃, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hn₃ hrpos hr_lt_n hn_pos
  intro i
  have hrpos_i := hrpos i
  have g_nonneg : 0 ≤ g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ (p a b) + 1
    calc sumTransform (p a b) g (r i n) n
      _ = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := rfl
      _ ≥ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n ≤ r i n := by exact hn₁ i
                  _ ≤ u := by exact_mod_cast hu'.1
      _ ≥ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr with u hu
        · rw [Finset.mem_Ico] at hu
          have := calc 0 < r i n := hrpos_i
                      _ ≤ u := hu.1
          positivity
        · rw [Finset.mem_Ico] at hu
          exact le_of_lt hu.2
      _ ≥ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
        gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
        rw [nsmul_eq_mul, mul_assoc]
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ ≥ n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr; exact hn₃ i
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / n ^ ((p a b) + 1)) := by ring
      _ = c₂ * (1 - c₃) * g n * (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) := by
        rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = c₂ * (1 - c₃) * g n := by rw [div_self (by positivity), mul_one]
      _ ≥ min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
        gcongr; exact min_le_left _ _
  | inr hp => -- (p a b) + 1 < 0
    calc sumTransform (p a b) g (r i n) n
        = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
      _ ≥ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n ≤ r i n := by exact hn₁ i
                  _ ≤ u := by exact_mod_cast hu'.1
      _ ≥ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
        gcongr n ^ (p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
        · rw [Finset.mem_Ico] at hu
          have := calc 0 < r i n := hrpos_i
                      _ ≤ u := hu.1
          positivity
        · rw [Finset.mem_Ico] at hu
          exact rpow_le_rpow_of_nonpos (by positivity)
            (by exact_mod_cast hu.1) (le_of_lt hp)
      _ ≥ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
          gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
          rw [nsmul_eq_mul, mul_assoc]
      _ ≥ n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / (c₁ * n) ^ (p a b + 1)) := by
          gcongr n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / ?_)
          exact rpow_le_rpow_of_nonpos (by positivity) (hn₁ i) (le_of_lt hp)
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ ≥ n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          gcongr; exact hn₃ i
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by ring
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ ^ ((p a b) + 1) * n ^ ((p a b) + 1))) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) * (1 - c₃) * c₂ * g n / c₁ ^ ((p a b) + 1) := by
          rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = (1 - c₃) * c₂ / c₁ ^ ((p a b) + 1) * g n := by
          rw [div_self (by positivity), one_mul]; ring
      _ ≥ min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
          gcongr; exact min_le_right _ _

end

end AkraBazziRecurrence

