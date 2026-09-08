/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Discrete Grönwall inequality

Various forms of the discrete Grönwall inequality, bounding solutions to recurrence
inequalities `u (n+1) ≤ c n * u n + b n` and `u (n+1) ≤ (1 + c n) * u n + b n`.

## Main results

* `discrete_gronwall_prod_general`: product form, over any ordered commutative semiring.
* `discrete_gronwall`: classical exponential bound for the `(1 + c)` form, over `ℝ`.
* `discrete_gronwall_Ico`: uniform bound over an interval, over `ℝ`.

## References

* [T. H. Grönwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*][Gronwall_1919]

## See also

* `Mathlib.Analysis.ODE.Gronwall` for the continuous Grönwall inequality for ODEs.
-/

@[expose] public section

open Real Finset

section General

/-! ### Generalized product form -/

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {u b c : ℕ → R}

/-- Discrete Grönwall inequality, product form: if `u (n+1) ≤ c n * u n + b n` and `0 ≤ c n`
then `u n ≤ u n₀ * ∏ c i + ∑ b k * ∏ c i` over the appropriate ranges. -/
/-
**discrete_gronwall_prod_general** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discrete_gronwall_prod_general {n₀ : Nat} (hu : forall n >= n₀, u (n + 1) 
<= c n * u n + b n) (hc : forall n >= n₀, 0 <= c n) ⦃n : Nat⦄ (hn : n₀ <= n) : u
 n <= u n₀ * ∏ i in Ico n₀ n, c i + ∑ k in Ico n₀ n, b k * ∏ i in Ico (k + 1) n,
 c i
参数：hu : forall n >= n₀, u (n + 1) <= c n * u n + b n；hc : forall n >= n₀, 0 <= c
 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_Ico_succ_top`：∀ {M : Type u_3} [inst : AddCommMonoid M] {a b 
: ℕ},   a ≤ b → ∀ (f : ℕ → M), ∑ k ∈ Finset.Ico a (b + 1), f k = ∑ k ∈ Finset.Ic
o a b, f k + …
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.prod_Ico_succ_top`：prod_Ico_succ_top {a b : Nat} (hab : a <= b) (
f : Nat -> M) : (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Discrete Grönwall inequality, product form: if `u (n+1) ≤ c n * u n + b n` and `
0 ≤ c n`
then `u n ≤ u n₀ * ∏ c i + ∑ b k * ∏ c i` over the appropriate ranges.
-/
theorem discrete_gronwall_prod_general {n₀ : ℕ} (hu : ∀ n ≥ n₀, u (n + 1) ≤ c n * u n + b n)
    (hc : ∀ n ≥ n₀, 0 ≤ c n) ⦃n : ℕ⦄ (hn : n₀ ≤ n) :
    u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, c i +
      ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, c i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hck : 0 ≤ c k := hc k hk
    have heq : c k * ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i + b k =
        ∑ j ∈ Ico n₀ (k + 1), b j * ∏ i ∈ Ico (j + 1) (k + 1), c i := by
      rw [sum_Ico_succ_top hk, mul_sum, Ico_self, prod_empty, mul_one]
      refine congr_arg (· + b k) (sum_congr rfl fun j hj ↦ ?_)
      rw [prod_Ico_succ_top (by have := mem_Ico.mp hj; omega)]; ring
    calc u (k + 1)
      _ ≤ c k * u k + b k := hu k hk
      _ ≤ c k * (u n₀ * ∏ i ∈ Ico n₀ k, c i +
            ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            ∑ j ∈ Ico n₀ (k + 1), b j * ∏ i ∈ Ico (j + 1) (k + 1), c i := by
          rw [← heq, ← prod_Ico_mul_eq_prod_Ico_add_one hk]; ring

end General

/-! ### Real-valued exponential form -/

variable {u b c : ℕ → ℝ}

/-- Discrete Grönwall inequality, exponential form: if `u (n+1) ≤ (1 + c n) * u n + b n` with
`b`, `c`, and `u n₀` non-negative, then `u n ≤ (u n₀ + ∑ b k) * exp (∑ c i)`. -/
/-
**discrete_gronwall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discrete_gronwall {n₀ : Nat} (hun₀ : 0 <= u n₀) (hu : forall n >= n₀, u (n
 + 1) <= (1 + c n) * u n + b n) (hc : forall n >= n₀, 0 <= c n) (hb : forall n >
= n₀, 0 <= b n) ⦃n : Nat⦄ (hn : n₀ <= n) : u n <= (u n₀ + ∑ k in Ico n₀ n, b k) 
* exp (∑ i in Ico n₀ n, c i)
参数：hun₀ : 0 <= u n₀；hu : forall n >= n₀, u (n + 1) <= (1 + c n) * u n + b n；hc :
 forall n >= n₀, 0 <= c n；hb : forall n >= n₀, 0 <= b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discrete_gronwall_prod_general`：discrete_gronwall_prod_general {n₀ : Nat
} (hu : forall n >= n₀, u (n + 1) <= c n * u n + b n) (hc : forall n >= n₀, 0 <=
 c n) ⦃n : Nat⦄ (hn …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le`：prod_le_prod_of_subset_of_one_l
e (h : s subseteq t) (hf0 : forall i in s, 0 <= f i) (hf : forall i in t, i ∉ s 
-> 1 <= f i) : ∏ i in s, f i …
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Real.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Real) : exp (
∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…

--- 原说明 ---
Discrete Grönwall inequality, exponential form: if `u (n+1) ≤ (1 + c n) * u n + 
b n` with
`b`, `c`, and `u n₀` non-negative, then `u n ≤ (u n₀ + ∑ b k) * exp (∑ c i)`.
-/
theorem discrete_gronwall {n₀ : ℕ} (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n) (hc : ∀ n ≥ n₀, 0 ≤ c n)
    (hb : ∀ n ≥ n₀, 0 ≤ b n) ⦃n : ℕ⦄ (hn : n₀ ≤ n) :
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
  calc u n
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (by grind) hn
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico n₀ n, (1 + c i) := by
        gcongr <;> grind
    _ = (u n₀ + ∑ k ∈ Ico n₀ n, b k) * ∏ i ∈ Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
        gcongr <;> try exact add_nonneg hun₀ <| sum_nonneg <| by grind
        simpa [exp_sum] using prod_le_prod (by grind) (by grind [add_one_le_exp])

/-- Discrete Grönwall inequality, uniform bound: a single bound holding for all `n ∈ [n₀, n₁)`. -/
/-
**discrete_gronwall_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：discrete_gronwall_Ico {n₀ n₁ : Nat} (hun₀ : 0 <= u n₀) (hu : forall n >= n
₀, u (n + 1) <= (1 + c n) * u n + b n) (hc : forall n >= n₀, 0 <= c n) (hb : for
all n >= n₀, 0 <= b n) ⦃n : Nat⦄ (hn : n in Ico n₀ n₁) : u n <= (u n₀ + ∑ k in I
co n₀ n₁, b k) * exp (∑ i in Ico n₀ n₁, c i)
参数：hun₀ : 0 <= u n₀；hu : forall n >= n₀, u (n + 1) <= (1 + c n) * u n + b n；hc :
 forall n >= n₀, 0 <= c n；hb : forall n >= n₀, 0 <= b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `discrete_gronwall`：discrete_gronwall {n₀ : Nat} (hun₀ : 0 <= u n₀) (hu :
 forall n >= n₀, u (n + 1) <= (1 + c n) * u n + b n) (hc : forall n >= n₀, 0 <= 
c n) (h…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b

--- 原说明 ---
Discrete Grönwall inequality, uniform bound: a single bound holding for all `n ∈
 [n₀, n₁)`.
-/
theorem discrete_gronwall_Ico {n₀ n₁ : ℕ} (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
    (hc : ∀ n ≥ n₀, 0 ≤ c n) (hb : ∀ n ≥ n₀, 0 ≤ b n) ⦃n : ℕ⦄ (hn : n ∈ Ico n₀ n₁) :
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
  have : 0 ≤ ∑ k ∈ Ico n₀ n₁, b k := sum_nonneg <| by grind
  exact (discrete_gronwall hun₀ hu hc hb (mem_Ico.mp hn).1).trans (by gcongr <;> grind)
