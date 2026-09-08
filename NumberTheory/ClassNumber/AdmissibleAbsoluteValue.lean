/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.Order.AbsoluteValue.Euclidean

/-!
# Admissible absolute values

This file defines a structure `AbsoluteValue.IsAdmissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

* `AbsoluteValue.IsAdmissible abv` states the absolute value `abv : R → ℤ`
  respects the Euclidean domain structure on `R`, and that a large enough set
  of elements of `R^n` contains a pair of elements whose remainders are
  pointwise close together.

## Main results

* `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is admissible.
* `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
  mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

public section

local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

variable {R : Type*} [EuclideanDomain R]
variable (abv : AbsoluteValue R ℤ)

/-- An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
/-
**AbsoluteValue.IsAdmissible** 是 Mathlib 中的一个归纳类型，位于命名空间 `AbsoluteValue`。
形式化陈述：{R : Type u_1} → [inst : EuclideanDomain R] → AbsoluteValue R ℤ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together.
-/
structure IsAdmissible extends IsEuclidean abv where
  /-- The cardinality required for a given `ε`. -/
  protected card : ℝ → ℕ
  /-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
  into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
  exists_partition' :
    ∀ (n : ℕ) {ε : ℝ} (_ : 0 < ε) {b : R} (_ : b ≠ 0) (A : Fin n → R),
      ∃ t : Fin n → Fin (card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε

namespace IsAdmissible

variable {abv}

/-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
/-
**AbsoluteValue.IsAdmissible.exists_partition** 是 Mathlib 中的一个定理，位于命名空间 `Absolut
eValue.IsAdmissible`。
形式化陈述：exists_partition {ι : Type*} [Finite ι] {ε : Real} (hε : 0 < ε) {b : R} (h
b : b != 0) (A : ι -> R) (h : abv.IsAdmissible) : exists t : ι -> Fin (h.card ε)
, forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ % b - A i₀ % b) : Real) < abv b • ε
参数：hε : 0 < ε；hb : b != 0；A : ι -> R；h : abv.IsAdmissible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AbsoluteValue.IsAdmissible.exists_partition'`：∀ {R : Type u_1} [inst : E
uclideanDomain R] {abv : AbsoluteValue R ℤ} (self : abv.IsAdmissible) (n : ℕ) {ε
 : ℝ},   0 < ε →     ∀ {b : R}, b …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For all `ε > 0` and finite families `A`, we can partition the remainders of `A` 
mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are cl
ose together.
-/
theorem exists_partition {ι : Type*} [Finite ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (A : ι → R) (h : abv.IsAdmissible) : ∃ t : ι → Fin (h.card ε),
      ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h ↦ ?_⟩
  convert! (config := { transparency := .default }) ht (e i₀) (e i₁) h <;>
    simp only [e.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
/-
**AbsoluteValue.IsAdmissible.exists_approx_aux** 是 Mathlib 中的一个定理，位于命名空间 `Absolu
teValue.IsAdmissible`。
形式化陈述：exists_approx_aux (n : Nat) (h : abv.IsAdmissible) : forall {ε : Real} (_h
ε : 0 < ε) {b : R} (_hb : b != 0) (A : Fin (h.card ε ^ n).succ -> Fin n -> R), e
xists i₀ i₁, i₀ != i₁ ∧ forall k, (abv (A i₁ k % b - A i₀ k % b) : Real) < abv b
 • ε
参数：n : Nat；h : abv.IsAdmissible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `AbsoluteValue.IsAdmissible.exists_partition`：exists_partition {ι : Type*
} [Finite ι] {ε : Real} (hε : 0 < ε) {b : R} (hb : b != 0) (A : ι -> R) (h : abv
.IsAdmissible) : exists t : ι -> …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.exists_lt_card_fiber_of_mul_lt_card`：exists_lt_card_fiber_of_mul
_lt_card (hn : card β * n < card α) : exists y : β, n < #{x | f x = y}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Finset.length_toList`：length_toList (s : Finset α) : s.toList.length = #
s
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `List.Nodup.getElem_inj_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i 
: ℕ} {hi : i < l.length} {j : ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_toList`：mem_toList {a : α} {s : Finset α} : a in s.toList ↔ a
 in s
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise.
-/
theorem exists_approx_aux (n : ℕ) (h : abv.IsAdmissible) :
    ∀ {ε : ℝ} (_hε : 0 < ε) {b : R} (_hb : b ≠ 0) (A : Fin (h.card ε ^ n).succ → Fin n → R),
      ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  have := Classical.decEq R
  induction n with
  | zero =>
    intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  | succ n ih =>
  intro ε hε b hb A
  let M := h.card ε
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M ^ n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ :
    ∃ s : Fin (M ^ n).succ → Fin (M ^ n.succ).succ,
      Function.Injective s ∧ ∀ i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abv b • ε := by
    -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ :
      ∃ t : Fin (M ^ n.succ).succ → Fin M,
        ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abv b • ε :=
      h.exists_partition hε hb fun x ↦ A x 0
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    have : (M ^ n).succ ≤ (Finset.toList {x | t x = s}).length := by
      rwa [Finset.length_toList]
    refine ⟨fun i ↦ (Finset.toList {x | t x = s})[i.castLE this], fun i j h ↦ ?_,
      fun i₀ i₁ ↦ ht _ _ ?_⟩
    · simpa [(Finset.nodup_toList _).getElem_inj_iff, Fin.val_inj] using h
    · have (i : Fin (M ^ n).succ) : t (Finset.toList {x | t x = s})[i.castLE this] = s :=
        (Finset.mem_filter.mp ((Finset.mem_toList (s := {x | t x = s})).mp (List.getElem_mem _))).2
      simp_rw [this]
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x ↦ Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h ↦ hk (s_inj h), fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i⟩
  · exact hs k₀ k₁
  · exact h i

/-- Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise. -/
/-
**AbsoluteValue.IsAdmissible.exists_approx** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteVa
lue.IsAdmissible`。
形式化陈述：exists_approx {ι : Type*} [Fintype ι] {ε : Real} (hε : 0 < ε) {b : R} (hb 
: b != 0) (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ -> ι 
-> R) : exists i₀ i₁, i₀ != i₁ ∧ forall k, (abv (A i₁ k % b - A i₀ k % b) : Real
) < abv b • ε
参数：hε : 0 < ε；hb : b != 0；h : abv.IsAdmissible；A : Fin (h.card ε ^ Fintype.card 
ι).succ -> ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AbsoluteValue.IsAdmissible.exists_approx_aux`：exists_approx_aux (n : Nat
) (h : abv.IsAdmissible) : forall {ε : Real} (_hε : 0 < ε) {b : R} (_hb : b != 0
) (A : Fin (h.card ε ^ n).succ -> …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise.
-/
theorem exists_approx {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ → ι → R) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y ↦ A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k ↦ ?_⟩
  convert! h (e k) <;> simp only [e.symm_apply_apply]

end IsAdmissible

end AbsoluteValue

