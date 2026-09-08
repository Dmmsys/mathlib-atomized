/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_eval_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions_of_sum_lt`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/

public section


universe u v

section FiniteField

open MvPolynomial

open Function hiding eval

open Finset FiniteField

variable {K σ ι : Type*} [Fintype K] [Field K] [Fintype σ] [DecidableEq σ]

local notation "q" => Fintype.card K

/-
**MvPolynomial.sum_eval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K) (h : f.totalDegree < 
(q - 1) * Fintype.card σ) : ∑ x, eval x f = 0
参数：f : MvPolynomial σ K；h : f.totalDegree < (q - 1) * Fintype.card σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.eval_eq'`：eval_eq' [Fintype σ] (X : σ -> R) (f : MvPolynomi
al σ R) : eval X f = ∑ d in f.support, f.coeff d * ∏ i, X i ^ d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `MvPolynomial.exists_degree_lt`：exists_degree_lt [Fintype σ] (f : MvPolyn
omial σ R) (n : Nat) (h : f.totalDegree < n * Fintype.card σ) {d : σ ->₀ Nat} (h
d : d in f.support)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Fintype.sum_fiberwise`：∀ {M : Type u_4} {κ : Type u_6} {ι : Type u_7} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   [inst_3 : Dec
idableEq κ]…
· 使用定理 `Fintype.sum_eq_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] 
[inst_1 : AddCommMonoid M] (f : α → M),   (∀ (a : α), f a = 0) → ∑ a, f a = 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Fintype.prod_sum_type`：Fintype.prod_sum_type (f : α₁ oplus α₂ -> M) : ∏ 
x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂)
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Equiv.subtypeEquivCodomain_symm_apply_eq`：subtypeEquivCodomain_symm_appl
y_eq (f : { x' // x' != x } -> Y) (y : Y) : ((subtypeEquivCodomain f).symm y : X
 -> Y) x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Fintype.prod_congr`：prod_congr (f g : α -> M) (h : forall a, f a = g a) 
: ∏ a, f a = ∏ a, g a
· 使用定理 `Equiv.subtypeEquivCodomain_symm_apply_ne`：subtypeEquivCodomain_symm_appl
y_ne (f : { x' // x' != x } -> Y) (y : Y) (x' : X) (h : x' != x) : ((subtypeEqui
vCodomain f).symm y : X -> Y) …
（共 33 条，此处仅展示前 30 条）
-/
theorem MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K)
    (h : f.totalDegree < (q - 1) * Fintype.card σ) : ∑ x, eval x f = 0 := by
  have : DecidableEq K := Classical.decEq K
  calc
    ∑ x, eval x f = ∑ x : σ → K, ∑ d ∈ f.support, f.coeff d * ∏ i, x i ^ d i := by
      simp only [eval_eq']
    _ = ∑ d ∈ f.support, ∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i := sum_comm
    _ = 0 := sum_eq_zero ?_
  intro d hd
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1 := f.exists_degree_lt (q - 1) h hd
  calc
    (∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i) = f.coeff d * ∑ x : σ → K, ∏ i, x i ^ d i :=
      (mul_sum ..).symm
    _ = 0 := (mul_eq_zero.mpr ∘ Or.inr) ?_
  calc
    (∑ x : σ → K, ∏ i, x i ^ d i) =
        ∑ x₀ : { j // j ≠ i } → K, ∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j :=
      (Fintype.sum_fiberwise _ _).symm
    _ = 0 := Fintype.sum_eq_zero _ ?_
  intro x₀
  let e : K ≃ { x // x ∘ ((↑) : _ → σ) = x₀ } := (Equiv.subtypeEquivCodomain _).symm
  calc
    (∑ x : { x : σ → K // x ∘ (↑) = x₀ }, ∏ j, (x : σ → K) j ^ d j) =
        ∑ a : K, ∏ j : σ, (e a : σ → K) j ^ d j := (e.sum_comp _).symm
    _ = ∑ a : K, (∏ j, x₀ j ^ d j) * a ^ d i := Fintype.sum_congr _ _ ?_
    _ = (∏ j, x₀ j ^ d j) * ∑ a : K, a ^ d i := by rw [mul_sum]
    _ = 0 := by rw [sum_pow_lt_card_sub_one K _ hi, mul_zero]
  intro a
  let e' : { j // j = i } ⊕ { j // j ≠ i } ≃ σ := Equiv.sumCompl _
  let : Unique { j // j = i } :=
    { default := ⟨i, rfl⟩
      uniq := fun ⟨j, h⟩ => Subtype.val_injective h }
  calc
    (∏ j : σ, (e a : σ → K) j ^ d j) =
        (e a : σ → K) i ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [← e'.prod_comp, Fintype.prod_sum_type, univ_unique, prod_singleton]; rfl
    _ = a ^ d i * ∏ j : { j // j ≠ i }, (e a : σ → K) j ^ d j := by
      rw [Equiv.subtypeEquivCodomain_symm_apply_eq]
    _ = a ^ d i * ∏ j, x₀ j ^ d j := congr_arg _ (Fintype.prod_congr _ _ ?_)
    -- see below
    _ = (∏ j, x₀ j ^ d j) * a ^ d i := mul_comm _ _
  -- the remaining step of the calculation above
  rintro ⟨j, hj⟩
  change (e a : σ → K) j ^ d j = x₀ ⟨j, hj⟩ ^ d j
  rw [Equiv.subtypeEquivCodomain_symm_apply_ne]

variable [DecidableEq K] (p : ℕ) [CharP K p]

/-- The **Chevalley–Warning theorem**, finitary version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
/-
**char_dvd_card_solutions_of_sum_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：char_dvd_card_solutions_of_sum_lt {s : Finset ι} {f : ι -> MvPolynomial σ 
K} (h : (∑ i in s, (f i).totalDegree) < Fintype.card σ) : p ∣ Fintype.card { x :
 σ -> K // forall i in s, eval x (f i) = 0 }
参数：h : (∑ i in s, (f i).totalDegree) < Fintype.card σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MvPolynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (f : ι -> M
vPolynomial σ R) (g : σ -> R) : eval g (∏ i in s, f i) = ∏ i in s, eval g (f i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Fintype.sum_extend_by_zero`：∀ {α : Type u_1} {ι : Type u_4} [inst : Deci
dableEq ι] [inst_1 : Fintype ι] [inst_2 : AddCommMonoid α] (s : Finset ι)   (f :
 ι → α), (∑ i, i…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The **Chevalley–Warning theorem**, finitary version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristi
c `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinali
ty of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`.
-/
theorem char_dvd_card_solutions_of_sum_lt {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
  have hq : 0 < q - 1 := by rw [← Fintype.card_units, Fintype.card_pos_iff]; exact ⟨1⟩
  let S : Finset (σ → K) := {x | ∀ i ∈ s, eval x (f i) = 0}
  have hS (x : σ → K) : x ∈ S ↔ ∀ i ∈ s, eval x (f i) = 0 := by simp [S]
  /- The polynomial `F = ∏ i ∈ s, (1 - (f i)^(q - 1))` has the nice property
    that it takes the value `1` on elements of `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}`
    while it is `0` outside that locus.
    Hence the sum of its values is equal to the cardinality of
    `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}` modulo `p`. -/
  let F : MvPolynomial σ K := ∏ i ∈ s, (1 - f i ^ (q - 1))
  have hF : ∀ x, eval x F = if x ∈ S then 1 else 0 := by
    intro x
    calc
      eval x F = ∏ i ∈ s, eval x (1 - f i ^ (q - 1)) := eval_prod s _ x
      _ = if x ∈ S then 1 else 0 := ?_
    simp only [(eval x).map_sub, (eval x).map_pow, (eval x).map_one]
    split_ifs with hx
    · apply Finset.prod_eq_one
      intro i hi
      rw [hS] at hx
      rw [hx i hi, zero_pow hq.ne', sub_zero]
    · obtain ⟨i, hi, hx⟩ : ∃ i ∈ s, eval x (f i) ≠ 0 := by
        simpa [hS, not_forall, Classical.not_imp] using hx
      apply Finset.prod_eq_zero hi
      rw [pow_card_sub_one_eq_one (eval x (f i)) hx, sub_self]
  -- In particular, we can now show:
  have key : ∑ x, eval x F = Fintype.card { x : σ → K // ∀ i ∈ s, eval x (f i) = 0 } := by
    rw [Fintype.card_of_subtype S hS, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ←
      Fintype.sum_extend_by_zero S, sum_congr rfl fun x _ => hF x]
  -- With these preparations under our belt, we will approach the main goal.
  change p ∣ Fintype.card { x // ∀ i : ι, i ∈ s → eval x (f i) = 0 }
  rw [← CharP.cast_eq_zero_iff K, ← key]
  change (∑ x, eval x F) = 0
  -- We are now ready to apply the main machine, proven before.
  apply F.sum_eval_eq_zero
  -- It remains to verify the crucial assumption of this machine
  show F.totalDegree < (q - 1) * Fintype.card σ
  calc
    F.totalDegree ≤ ∑ i ∈ s, (1 - f i ^ (q - 1)).totalDegree := totalDegree_finsetProd s _
    _ ≤ ∑ i ∈ s, (q - 1) * (f i).totalDegree := sum_le_sum fun i _ => ?_
    -- see ↓
    _ = (q - 1) * ∑ i ∈ s, (f i).totalDegree := (mul_sum ..).symm
    _ < (q - 1) * Fintype.card σ := by gcongr
  -- Now we prove the remaining step from the preceding calculation
  change (1 - f i ^ (q - 1)).totalDegree ≤ (q - 1) * (f i).totalDegree
  calc
    (1 - f i ^ (q - 1)).totalDegree ≤
        max (1 : MvPolynomial σ K).totalDegree (f i ^ (q - 1)).totalDegree := totalDegree_sub _ _
    _ ≤ (f i ^ (q - 1)).totalDegree := by simp
    _ ≤ (q - 1) * (f i).totalDegree := totalDegree_pow _ _

/-- The **Chevalley–Warning theorem**, `Fintype` version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
/-
**char_dvd_card_solutions_of_fintype_sum_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：char_dvd_card_solutions_of_fintype_sum_lt [Fintype ι] {f : ι -> MvPolynomi
al σ K} (h : (∑ i, (f i).totalDegree) < Fintype.card σ) : p ∣ Fintype.card { x :
 σ -> K // forall i, eval x (f i) = 0 }
参数：h : (∑ i, (f i).totalDegree) < Fintype.card σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `char_dvd_card_solutions_of_sum_lt`：char_dvd_card_solutions_of_sum_lt {s 
: Finset ι} {f : ι -> MvPolynomial σ K} (h : (∑ i in s, (f i).totalDegree) < Fin
type.card σ) : p ∣ Fint…

--- 原说明 ---
The **Chevalley–Warning theorem**, `Fintype` version.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristi
c `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinali
ty of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`.
-/
theorem char_dvd_card_solutions_of_fintype_sum_lt [Fintype ι] {f : ι → MvPolynomial σ K}
    (h : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // ∀ i, eval x (f i) = 0 } := by
  simpa using char_dvd_card_solutions_of_sum_lt p h

/-- The **Chevalley–Warning theorem**, unary version.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_of_sum_lt` for a version that takes a family of polynomials `f i`. -/
/-
**char_dvd_card_solutions** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintyp
e.card σ) : p ∣ Fintype.card { x : σ -> K // eval x f = 0 }
参数：h : f.totalDegree < Fintype.card σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `char_dvd_card_solutions_of_sum_lt`：char_dvd_card_solutions_of_sum_lt {s 
: Finset ι} {f : ι -> MvPolynomial σ K} (h : (∑ i in s, (f i).totalDegree) < Fin
type.card σ) : p ∣ Fint…

--- 原说明 ---
The **Chevalley–Warning theorem**, unary version.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_of_sum_lt` for a version that takes a family of pol
ynomials `f i`.
-/
theorem char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f = 0 } := by
  let F : Unit → MvPolynomial σ K := fun _ => f
  have : (∑ i : Unit, (F i).totalDegree) < Fintype.card σ := h
  convert! char_dvd_card_solutions_of_sum_lt p this
  aesop

/-- The **Chevalley–Warning theorem**, binary version.
Let `f₁`, `f₂` be two multivariate polynomials in finitely many variables (`X s`, `s : σ`) over a
finite field of characteristic `p`.
Assume that the sum of the total degrees of `f₁` and `f₂` is less than the cardinality of `σ`.
Then the number of common solutions of the `f₁` and `f₂` is divisible by `p`. -/
/-
**char_dvd_card_solutions_of_add_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：char_dvd_card_solutions_of_add_lt {f₁ f₂ : MvPolynomial σ K} (h : f₁.total
Degree + f₂.totalDegree < Fintype.card σ) : p ∣ Fintype.card { x : σ -> K // eva
l x f₁ = 0 ∧ eval x f₂ = 0 }
参数：h : f₁.totalDegree + f₂.totalDegree < Fintype.card σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `char_dvd_card_solutions_of_fintype_sum_lt`：char_dvd_card_solutions_of_fi
ntype_sum_lt [Fintype ι] {f : ι -> MvPolynomial σ K} (h : (∑ i, (f i).totalDegre
e) < Fintype.card σ) : p ∣ Fint…

--- 原说明 ---
The **Chevalley–Warning theorem**, binary version.
Let `f₁`, `f₂` be two multivariate polynomials in finitely many variables (`X s`
, `s : σ`) over a
finite field of characteristic `p`.
Assume that the sum of the total degrees of `f₁` and `f₂` is less than the cardi
nality of `σ`.
Then the number of common solutions of the `f₁` and `f₂` is divisible by `p`.
-/
theorem char_dvd_card_solutions_of_add_lt {f₁ f₂ : MvPolynomial σ K}
    (h : f₁.totalDegree + f₂.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f₁ = 0 ∧ eval x f₂ = 0 } := by
  let F : Bool → MvPolynomial σ K := fun b => cond b f₂ f₁
  have : (∑ b : Bool, (F b).totalDegree) < Fintype.card σ := (add_comm _ _).trans_lt h
  simpa only [Bool.forall_bool] using! char_dvd_card_solutions_of_fintype_sum_lt p this

end FiniteField

