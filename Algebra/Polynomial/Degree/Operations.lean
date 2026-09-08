/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Lemmas for calculating the degree of univariate polynomials

## Main results
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees
-/

@[expose] public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [Semiring S] {p q r : R[X]}

/-
**Polynomial.supDegree_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.de
gree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.max_eq_sup_coe`：max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑)
-/
theorem supDegree_eq_degree (p : R[X]) : p.toFinsupp.supDegree WithBot.some = p.degree :=
  max_eq_sup_coe
/-
**Polynomial.degree_lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wf degree wellFounded_lt
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

@[nontriviality]
/-
**Polynomial.monic_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elim _ _

@[nontriviality]
/-
**Polynomial.degree_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_of_subsingleton [Subsingleton R] : degree p = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
-/
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]

@[nontriviality]
/-
**Polynomial.natDegree_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
-/
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, natDegree_zero]
/-
**Polynomial.le_natDegree_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：le_natDegree_of_ne_zero (h : coeff p n != 0) : n <= natDegree p
参数：h : coeff p n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
-/
theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl
/-
**Polynomial.degree_eq_of_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：degree_eq_of_le_of_coeff_ne_zero (pn : p.degree <= n) (p1 : p.coeff n != 0
) : p.degree = n
参数：pn : p.degree <= n；p1 : p.coeff n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
-/
theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree ≤ n) (p1 : p.coeff n ≠ 0) : p.degree = n :=
  pn.antisymm (le_degree_of_ne_zero p1)
/-
**Polynomial.natDegree_eq_of_le_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff 
n != 0) : p.natDegree = n
参数：pn : p.natDegree <= n；p1 : p.coeff n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
-/
theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree ≤ n) (p1 : p.coeff n ≠ 0) :
    p.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)
/-
**Polynomial.natDegree_lt_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_lt_natDegree {q : S[X]} (hp : p != 0) (hpq : p.degree < q.degree
) : p.natDegree < q.natDegree
参数：hp : p != 0；hpq : p.degree < q.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem natDegree_lt_natDegree {q : S[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq
/-
**Polynomial.natDegree_eq_natDegree** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) : p.natDegre
e = q.natDegree
参数：hpq : p.degree = q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_eq_natDegree {q : S[X]} (hpq : p.degree = q.degree) :
    p.natDegree = q.natDegree := by simp [natDegree, hpq]
/-
**Polynomial.coeff_eq_zero_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0
参数：h : degree p < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))
/-
**Polynomial.coeff_eq_zero_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : Nat} (h : p.natDegree < n) :
 p.coeff n = 0
参数：h : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]
/-
**Polynomial.ext_iff_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ext_iff_natDegree_le {p q : R[X]} {n : Nat} (hp : p.natDegree <= n) (hq : 
q.natDegree <= n) : p = q ↔ forall i <= n, p.coeff i = q.coeff i
参数：hp : p.natDegree <= n；hq : q.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_iff_natDegree_le {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i := by
  refine Iff.trans Polynomial.ext_iff ?_
  refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  refine (le_or_gt i n).elim h fun k => ?_
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm
/-
**Polynomial.ext_iff_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ext_iff_degree_le {p q : R[X]} {n : Nat} (hp : p.degree <= n) (hq : q.degr
ee <= n) : p = q ↔ forall i <= n, p.coeff i = q.coeff i
参数：hp : p.degree <= n；hq : q.degree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext_iff_natDegree_le`：ext_iff_natDegree_le {p q : R[X]} {n : 
Nat} (hp : p.natDegree <= n) (hq : q.natDegree <= n) : p = q ↔ forall i <= n, p.
coeff i = q.coeff i
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
/-
**Polynomial.coeff_natDegree_succ_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
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
-/
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
/-
**Polynomial.ite_le_natDegree_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ite_le_natDegree_coeff (p : R[X]) (n : Nat) (I : Decidable (n < 1 + natDeg
ree p)) : @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n
参数：p : R[X]；n : Nat；I : Decidable (n < 1 + natDegree p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_one_add_iff`：∀ {m n : ℕ}, m < 1 + n ↔ m ≤ n
-/
theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

end Semiring

section Ring

variable [Ring R]

/-
**Polynomial.coeff_mul_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mul_X_sub_C {p : R[X]} {r : R} {a : Nat} : coeff (p * (X - C r)) (a 
+ 1) = coeff p a - coeff p (a + 1) * r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]
/-
**Polynomial.coeff_X_sub_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_X_sub_C_mul {p : R[X]} {r : R} {a : Nat} : coeff ((X - C r) * p) (a 
+ 1) = coeff p a - r * coeff p (a + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_mul`：coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_X_sub_C_mul {p : R[X]} {r : R} {a : ℕ} :
    coeff ((X - C r) * p) (a + 1) = coeff p a - r * coeff p (a + 1) := by simp [sub_mul]

end Ring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/-
**Polynomial.coeff_natDegree_eq_zero_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) : coeff p (
natDegree q) = 0
参数：h : degree p < degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
-/
theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)
/-
**Polynomial.ne_zero_of_degree_gt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_degree_gt {n : WithBot Nat} (h : n < degree p) : p != 0
参数：h : n < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
-/
theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 h.ne_bot
/-
**Polynomial.ne_zero_of_degree_ge_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_degree_ge_degree (hpq : p.degree <= q.degree) (hp : p != 0) : q
 != 0
参数：hpq : p.degree <= q.degree；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
-/
theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)
/-
**Polynomial.ne_zero_of_natDegree_gt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_natDegree_gt {n : Nat} (h : n < natDegree p) : p != 0
参数：h : n < natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simp [H] at h
/-
**Polynomial.degree_lt_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q
参数：h : natDegree p < natDegree q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by
  by_cases hp : p = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]
/-
**Polynomial.natDegree_lt_natDegree_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_lt_natDegree_iff (hp : p != 0) : natDegree p < natDegree q ↔ deg
ree p < degree q
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, fun h ↦ by
    have hq : q ≠ 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩
/-
**Polynomial.eq_C_of_degree_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_C_of_degree_le_zero (h : degree p <= 0) : p = C (coeff p 0)
参数：h : degree p <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) := by
  ext (_ | n)
  · simp
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)
/-
**Polynomial.eq_C_of_degree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0)
参数：h : degree p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero h.le
/-
**Polynomial.degree_le_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_zero_iff : degree p <= 0 ↔ p = C (coeff p 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩
/-
**Polynomial.degree_add_eq_left_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q)
 = degree p
参数：h : degree q < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用定理 `Polynomial.degree_le_degree`：degree_le_degree (h : coeff q (natDegree p)
 != 0) : degree p <= degree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_natDegree_eq_zero_of_degree_lt`：coeff_natDegree_eq_zero
_of_degree_lt (h : degree p < degree q) : coeff p (natDegree q) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
-/
theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [coeff_add, coeff_natDegree_eq_zero_of_degree_lt h, add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)
/-
**Polynomial.degree_add_eq_right_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q
) = degree q
参数：h : degree p < degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
-/
theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]
/-
**Polynomial.natDegree_add_eq_left_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) : natDegree (
p + q) = natDegree p
参数：h : degree q < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
-/
theorem natDegree_add_eq_left_of_degree_lt (h : degree q < degree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)
/-
**Polynomial.natDegree_add_eq_left_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) : na
tDegree (p + q) = natDegree p
参数：h : natDegree q < natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_add_eq_left_of_degree_lt`：natDegree_add_eq_left_of_
degree_lt (h : degree q < degree p) : natDegree (p + q) = natDegree p
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)
/-
**Polynomial.natDegree_add_eq_right_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：natDegree_add_eq_right_of_degree_lt (h : degree p < degree q) : natDegree 
(p + q) = natDegree q
参数：h : degree p < degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
-/
theorem natDegree_add_eq_right_of_degree_lt (h : degree p < degree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)
/-
**Polynomial.natDegree_add_eq_right_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) : n
atDegree (p + q) = natDegree q
参数：h : natDegree p < natDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_add_eq_right_of_degree_lt`：natDegree_add_eq_right_o
f_degree_lt (h : degree p < degree q) : natDegree (p + q) = natDegree q
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)
/-
**Polynomial.degree_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p
参数：hp : 0 < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
-/
theorem degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
  add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp
/-
**Polynomial.natDegree_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R} {a : R}, (p + Polyno
mial.C a).natDegree = p.natDegree
参数：p + Polynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Polynomial.natDegree_add_eq_left_of_natDegree_lt`：natDegree_add_eq_left_
of_natDegree_lt (h : natDegree q < natDegree p) : natDegree (p + q) = natDegree 
p
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
@[simp, grind =] theorem natDegree_add_C {a : R} : (p + C a).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  by_cases! hpd : p.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd
/-
**Polynomial.natDegree_C_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R} {a : R}, (Polynomial
.C a + p).natDegree = p.natDegree
参数：Polynomial.C a + p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem natDegree_C_add {a : R} : (C a + p).natDegree = p.natDegree := by
  simp [add_comm _ p]
/-
**Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoe
ff q != 0) : degree (p + q) = max p.degree q.degree
参数：h : leadingCoeff p + leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `max_eq_right_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a
 < b → max a b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_natDegree_eq_zero_of_degree_lt`：coeff_natDegree_eq_zero
_of_degree_lt (h : degree p < degree q) : coeff p (natDegree q) = 0
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
-/
theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_self] at hlt
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← coeff_add]
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]
/-
**Polynomial.natDegree_eq_of_natDegree_add_lt_left** 是 Mathlib 中的一个引理，位于命名空间 `Po
lynomial`。
形式化陈述：natDegree_eq_of_natDegree_add_lt_left (p q : R[X]) (H : natDegree (p + q) 
< natDegree p) : natDegree p = natDegree q
参数：p q : R[X]；H : natDegree (p + q) < natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.lt_or_lt_of_ne`：∀ {a b : ℕ}, a ≠ b → a < b ∨ b < a
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_add_eq_right_of_natDegree_lt`：natDegree_add_eq_righ
t_of_natDegree_lt (h : natDegree p < natDegree q) : natDegree (p + q) = natDegre
e q
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Polynomial.natDegree_add_eq_left_of_natDegree_lt`：natDegree_add_eq_left_
of_natDegree_lt (h : natDegree q < natDegree p) : natDegree (p + q) = natDegree 
p
-/
lemma natDegree_eq_of_natDegree_add_lt_left (p q : R[X])
    (H : natDegree (p + q) < natDegree p) : natDegree p = natDegree q := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H
/-
**Polynomial.natDegree_eq_of_natDegree_add_lt_right** 是 Mathlib 中的一个引理，位于命名空间 `P
olynomial`。
形式化陈述：natDegree_eq_of_natDegree_add_lt_right (p q : R[X]) (H : natDegree (p + q)
 < natDegree q) : natDegree p = natDegree q
参数：p q : R[X]；H : natDegree (p + q) < natDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.natDegree_eq_of_natDegree_add_lt_left`：natDegree_eq_of_natDeg
ree_add_lt_left (p q : R[X]) (H : natDegree (p + q) < natDegree p) : natDegree p
 = natDegree q
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma natDegree_eq_of_natDegree_add_lt_right (p q : R[X])
    (H : natDegree (p + q) < natDegree q) : natDegree p = natDegree q :=
  (natDegree_eq_of_natDegree_add_lt_left q p (add_comm p q ▸ H)).symm
/-
**Polynomial.natDegree_eq_of_natDegree_add_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Po
lynomial`。
形式化陈述：natDegree_eq_of_natDegree_add_eq_zero (p q : R[X]) (H : natDegree (p + q) 
= 0) : natDegree p = natDegree q
参数：p q : R[X]；H : natDegree (p + q) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.natDegree_eq_of_natDegree_add_lt_right`：natDegree_eq_of_natDe
gree_add_lt_right (p q : R[X]) (H : natDegree (p + q) < natDegree q) : natDegree
 p = natDegree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `Polynomial.natDegree_eq_of_natDegree_add_lt_left`：natDegree_eq_of_natDeg
ree_add_lt_left (p q : R[X]) (H : natDegree (p + q) < natDegree p) : natDegree p
 = natDegree q
-/
lemma natDegree_eq_of_natDegree_add_eq_zero (p q : R[X])
    (H : natDegree (p + q) = 0) : natDegree p = natDegree q := by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]
/-
**Polynomial.monic_of_natDegree_le_of_coeff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：monic_of_natDegree_le_of_coeff_eq_one (n : Nat) (pn : p.natDegree <= n) (p
1 : p.coeff n = 1) : Monic p
参数：n : Nat；pn : p.natDegree <= n；p1 : p.coeff n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Monic p := by
  unfold Monic
  nontriviality
  refine (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero
/-
**Polynomial.monic_of_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_of_degree_le (n : Nat) (pn : p.degree <= n) (p1 : p.coeff n = 1) : M
onic p
参数：n : Nat；pn : p.degree <= n；p1 : p.coeff n = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_of_natDegree_le_of_coeff_eq_one`：monic_of_natDegree_le_
of_coeff_eq_one (n : Nat) (pn : p.natDegree <= n) (p1 : p.coeff n = 1) : Monic p
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem monic_of_degree_le (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) : Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1
/-
**Polynomial.leadingCoeff_add_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_add_of_degree_lt (h : degree p < degree q) : leadingCoeff (p 
+ q) = leadingCoeff q
参数：h : degree p < degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_natDegree_eq_zero_of_degree_lt`：coeff_natDegree_eq_zero
_of_degree_lt (h : degree p < degree q) : coeff p (natDegree q) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]
/-
**Polynomial.leadingCoeff_add_of_degree_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：leadingCoeff_add_of_degree_lt' (h : degree q < degree p) : leadingCoeff (p
 + q) = leadingCoeff p
参数：h : degree q < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
-/
theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h
/-
**Polynomial.leadingCoeff_add_of_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_add_of_degree_eq (h : degree p = degree q) (hlc : leadingCoef
f p + leadingCoeff q != 0) : leadingCoeff (p + q) = leadingCoeff p + leadingCoef
f q
参数：h : degree p = degree q；hlc : leadingCoeff p + leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero`：degree_add_eq_of_l
eadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q != 0) : degree (p +
 q) = max p.degree q.degree
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]

@[simp]
/-
**Polynomial.coeff_mul_degree_add_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mul_degree_add_degree (p q : R[X]) : coeff (p * q) (natDegree p + na
tDegree q) = leadingCoeff p * leadingCoeff q
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `not_lt_iff_eq_or_lt`：not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x ∈ antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine Finset.sum_eq_single (natDegree p, natDegree q) ?_ ?_
      · rintro ⟨i, j⟩ h₁ h₂
        rw [mem_antidiagonal] at h₁
        by_cases H : natDegree p < i
        · rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          rcases H with H | H
          · simp_all
          · suffices natDegree q < j by
              rw [coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            by_contra! H'
            exact
              ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                h₁
      · intro H
        exfalso
        apply H
        rw [mem_antidiagonal]
/-
**Polynomial.degree_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul' (h : leadingCoeff p * leadingCoeff q != 0) : degree (p * q) = 
degree p + degree q
参数：h : leadingCoeff p * leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `Polynomial.coeff_mul_degree_add_degree`：coeff_mul_degree_add_degree (p q
 : R[X]) : coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingC
oeff q
-/
theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
  have hq : q ≠ 0 := by refine mt ?_ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
      refine le_degree_of_ne_zero (n := natDegree p + natDegree q) ?_
      rwa [coeff_mul_degree_add_degree])
/-
**Polynomial.Monic.degree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p q : Polynomial R}, q.Monic → (p * q)
.degree = p.degree + q.degree
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
  else degree_mul' <| by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]
/-
**Polynomial.natDegree_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul' (h : leadingCoeff p * leadingCoeff q != 0) : natDegree (p *
 q) = natDegree p + natDegree q
参数：h : leadingCoeff p * leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_mul]
  have hq : q ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, mul_zero]
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, Nat.cast_add, degree_eq_natDegree hp, degree_eq_natDegree hq]
/-
**Polynomial.leadingCoeff_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q != 0) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
参数：h : leadingCoeff p * leadingCoeff q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.coeff_mul_degree_add_degree`：coeff_mul_degree_add_degree (p q
 : R[X]) : coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingC
oeff q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  simp [← coeff_natDegree, natDegree_mul' h, coeff_mul_degree_add_degree]
/-
**Polynomial.Monic.leadingCoeff_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Moni
c`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → ∀ (r : R)
, (Polynomial.C r * p).leadingCoeff = r
参数：r : R；Polynomial.C r * p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma Monic.leadingCoeff_C_mul (hp : p.Monic) (r : R) : (C r * p).leadingCoeff = r := by
  by_cases hr : r = 0 <;> simp_all [leadingCoeff_mul']
/-
**Polynomial.leadingCoeff_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_pow' : leadingCoeff p ^ n != 0 -> leadingCoeff (p ^ n) = lead
ingCoeff p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
-/
theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ', ← ih h₁] at h
    rw [pow_succ', pow_succ', leadingCoeff_mul' h₂, ih h₁]
/-
**Polynomial.degree_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pow' : forall {n : Nat}, leadingCoeff p ^ n != 0 -> degree (p ^ n) 
= n • degree p | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zer
o_nsmul] | n + 1 => fun h => by have h₁ : leadingCoeff p ^ n != 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zero_nsmul]
  | n + 1 => fun h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, zero_mul]
    have h₂ : leadingCoeff (p ^ n) * leadingCoeff p ≠ 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]
/-
**Polynomial.natDegree_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pow' {n : Nat} (h : leadingCoeff p ^ n != 0) : natDegree (p ^ n)
 = n * natDegree p
参数：h : leadingCoeff p ^ n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree_pow'`：degree_pow' : forall {n : Nat}, leadingCoeff p ^
 n != 0 -> degree (p ^ n) = n • degree p | 0 => fun h => by rw [pow_zero, ← C_1]
 at *; rw [d…
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← leadingCoeff_pow' h1, hpn0, leadingCoeff_zero] at h; exact h rfl
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_natDegree hpn, degree_pow' h, degree_eq_natDegree hp0]; simp
/-
**Polynomial.leadingCoeff_monic_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) : leadingCoeff (p * q) 
= leadingCoeff q
参数：hp : Monic p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    rwa [hp.leadingCoeff, one_mul, Ne, leadingCoeff_eq_zero]
/-
**Polynomial.leadingCoeff_mul_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) : leadingCoeff (p * q) 
= leadingCoeff p
参数：hq : Monic q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  letI := Classical.decEq R
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leadingCoeff_eq_zero.1 H, zero_mul, leadingCoeff_zero])
    fun H : leadingCoeff p ≠ 0 => by
      rw [leadingCoeff_mul', hq.leadingCoeff, mul_one]
      rwa [hq.leadingCoeff, mul_one]
/-
**Polynomial.degree_C_mul_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).degree = p.d
egree
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `IsUnit.mul_right_eq_zero`：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) :
 a * b = 0 ↔ b = 0
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma degree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul', degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_right_eq_zero]
/-
**Polynomial.degree_mul_C_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).degree = p.d
egree
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [degree_mul', degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]
/-
**Polynomial.natDegree_C_mul_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).natDegree
 = p.natDegree
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_C_mul_of_isUnit`：degree_C_mul_of_isUnit (ha : IsUnit a
) (p : R[X]) : (C a * p).degree = p.degree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).natDegree = p.natDegree := by
  simp [natDegree, degree_C_mul_of_isUnit ha]
/-
**Polynomial.natDegree_mul_C_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).natDegree
 = p.natDegree
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul_C_of_isUnit`：degree_mul_C_of_isUnit (ha : IsUnit a
) (p : R[X]) : (p * C a).degree = p.degree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).natDegree = p.natDegree := by
  simp [natDegree, degree_mul_C_of_isUnit ha]
/-
**Polynomial.leadingCoeff_C_mul_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：leadingCoeff_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) : (C a * p).leadin
gCoeff = a * p.leadingCoeff
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用引理 `Polynomial.natDegree_C_mul_of_isUnit`：natDegree_C_mul_of_isUnit (ha : Is
Unit a) (p : R[X]) : (C a * p).natDegree = p.natDegree
-/
lemma leadingCoeff_C_mul_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (C a * p).leadingCoeff = a * p.leadingCoeff := by
  rwa [leadingCoeff, coeff_C_mul, natDegree_C_mul_of_isUnit, leadingCoeff]
/-
**Polynomial.leadingCoeff_mul_C_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * C a).leadin
gCoeff = p.leadingCoeff * a
参数：ha : IsUnit a；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用引理 `Polynomial.natDegree_mul_C_of_isUnit`：natDegree_mul_C_of_isUnit (ha : Is
Unit a) (p : R[X]) : (p * C a).natDegree = p.natDegree
-/
lemma leadingCoeff_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) :
    (p * C a).leadingCoeff = p.leadingCoeff * a := by
  rwa [leadingCoeff, coeff_mul_C, natDegree_mul_C_of_isUnit, leadingCoeff]

@[simp]
/-
**Polynomial.leadingCoeff_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_mul_X_pow {p : R[X]} {n : Nat} : leadingCoeff (p * X ^ n) = l
eadingCoeff p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
-/
theorem leadingCoeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  leadingCoeff_mul_monic (monic_X_pow n)

@[simp]
/-
**Polynomial.leadingCoeff_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
-/
theorem leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_X

@[simp]
/-
**Polynomial.coeff_pow_mul_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_pow_mul_natDegree (p : R[X]) (n : Nat) : (p ^ n).coeff (n * p.natDeg
ree) = p.leadingCoeff ^ n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Polynomial.natDegree_pow_le`：natDegree_pow_le {p : R[X]} {n : Nat} : (p 
^ n).natDegree <= n * p.natDegree
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.natDegree_pow'`：natDegree_pow' {n : Nat} (h : leadingCoeff p 
^ n != 0) : natDegree (p ^ n) = n * natDegree p
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Polynomial.coeff_mul_degree_add_degree`：coeff_mul_degree_add_degree (p q
 : R[X]) : coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingC
oeff q
-/
theorem coeff_pow_mul_natDegree (p : R[X]) (n : ℕ) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    by_cases hp1 : p.leadingCoeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have h1 : (p ^ i).natDegree < i * p.natDegree := by
          refine lt_of_le_of_ne natDegree_pow_le fun h => hp2 ?_
          rw [← h, hp1] at hi
          exact leadingCoeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.natDegree := natDegree_mul_le
          _ < i * p.natDegree + p.natDegree := by gcongr
    · rw [← natDegree_pow' hp1, ← leadingCoeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _
/-
**Polynomial.coeff_mul_add_eq_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：coeff_mul_add_eq_of_natDegree_le {df dg : Nat} {f g : R[X]} (hdf : natDegr
ee f <= df) (hdg : natDegree g <= dg) : (f * g).coeff (df + dg) = f.coeff df * g
.coeff dg
参数：hdf : natDegree f <= df；hdg : natDegree g <= dg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_add_iff_eq_and_eq`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Part
ialOrder α] [AddLeftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a ≤ c 
→ b ≤ d → (a +…
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
-/
theorem coeff_mul_add_eq_of_natDegree_le {df dg : ℕ} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (df, dg)]
  · rw [mem_antidiagonal]
  rintro ⟨df', dg'⟩ hmem hne
  obtain h | hdf' := lt_or_ge df df'
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
  obtain h | hdg' := lt_or_ge dg dg'
  · rw [coeff_eq_zero_of_natDegree_lt (hdg.trans_lt h), mul_zero]
  obtain ⟨rfl, rfl⟩ :=
    (add_eq_add_iff_eq_and_eq hdf' hdg').mp (mem_antidiagonal.1 hmem)
  exact (hne rfl).elim
/-
**Polynomial.degree_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) : degree
 (a • p) <= degree p
参数：a : S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.degree_lt_iff_coeff_zero`：degree_lt_iff_coeff_zero (f : R[X])
 (n : Nat) : degree f < n ↔ forall m : Nat, n <= m -> coeff f m = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    degree (a • p) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]
/-
**Polynomial.natDegree_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) : nat
Degree (a • p) <= natDegree p
参数：a : S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
-/
theorem natDegree_smul_le {S : Type*} [SMulZeroClass S R] (a : S) (p : R[X]) :
    natDegree (a • p) ≤ natDegree p :=
  natDegree_le_natDegree (degree_smul_le a p)
/-
**Polynomial.degree_smul_of_isRightRegular_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：degree_smul_of_isRightRegular_leadingCoeff (ha : a != 0) (hp : IsRightRegu
lar p.leadingCoeff) : (a • p).degree = p.degree
参数：ha : a != 0；hp : IsRightRegular p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
· 使用定理 `Polynomial.degree_le_degree`：degree_le_degree (h : coeff q (natDegree p)
 != 0) : degree p <= degree q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `IsRightRegular.mul_right_eq_zero_iff`：∀ {R : Type u_1} [inst : MulZeroCl
ass R] {a b : R}, IsRightRegular b → (a * b = 0 ↔ a = 0)
-/
theorem degree_smul_of_isRightRegular_leadingCoeff (ha : a ≠ 0)
    (hp : IsRightRegular p.leadingCoeff) : (a • p).degree = p.degree := by
  refine le_antisymm (degree_smul_le a p) <| degree_le_degree ?_
  rw [coeff_smul, coeff_natDegree, smul_eq_mul, ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha
/-
**Polynomial.degree_lt_degree_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_lt_degree_mul_X (hp : p != 0) : p.degree < (p * X).degree
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree := by
  have := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff X ≠ 0 := by simpa
  rw [degree_mul' this, degree_eq_natDegree hp, degree_X, ← Nat.cast_one, ← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _
/-
**Polynomial.eq_C_of_natDegree_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_C_of_natDegree_le_zero (h : natDegree p <= 0) : p = C (coeff p 0)
参数：h : natDegree p <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
-/
theorem eq_C_of_natDegree_le_zero (h : natDegree p ≤ 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero <| degree_le_of_natDegree_le h
/-
**Polynomial.eq_C_of_natDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0)
参数：h : natDegree p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_C_of_natDegree_le_zero`：eq_C_of_natDegree_le_zero (h : nat
Degree p <= 0) : p = C (coeff p 0)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0) :=
  eq_C_of_natDegree_le_zero h.le
/-
**Polynomial.natDegree_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ exists x, C x = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ ∃ x, C x = p :=
  ⟨fun h ↦ ⟨_, (eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩
/-
**Polynomial.eq_C_coeff_zero_iff_natDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
-/
theorem eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0 :=
  ⟨fun h ↦ by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩
/-
**Polynomial.eq_one_of_monic_natDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p 
= 1
参数：hf : p.Monic；hfd : p.natDegree = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1 := by
  rw [Monic.def, leadingCoeff, hfd] at hf
  rw [eq_C_of_natDegree_eq_zero hfd, hf, map_one]

@[simp]
/-
**Polynomial.Monic.natDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic
`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {p : Polynomial R}, p.Monic → (p.natDeg
ree = 0 ↔ p = 1)
参数：p.natDegree = 0 ↔ p = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_one_of_monic_natDegree_zero`：eq_one_of_monic_natDegree_zer
o (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.natDegree_eq_zero (hf : p.Monic) : p.natDegree = 0 ↔ p = 1 :=
  ⟨eq_one_of_monic_natDegree_zero hf, by rintro rfl; simp⟩
/-
**Polynomial.degree_sum_fin_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sum_fin_lt {n : Nat} (f : Fin n -> R) : degree (∑ i : Fin n, C (f i
) * X ^ (i : Nat)) < n
参数：f : Fin n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Polynomial.degree_C_mul_X_pow_le`：degree_C_mul_X_pow_le (n : Nat) (a : R
) : degree (C a * X ^ n) <= n
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, C (f i) * X ^ (i : ℕ)) < n :=
  (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
      (degree_C_mul_X_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt
/-
**Polynomial.degree_C_lt_degree_C_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_lt_degree_C_mul_X (ha : a != 0) : degree (C b) < degree (C a * X)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_C_mul_X`：degree_C_mul_X (ha : a != 0) : degree (C a * 
X) = 1
· 使用定理 `Polynomial.degree_C_lt`：degree_C_lt : degree (C a) < 1
-/
theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (C b) < degree (C a * X) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

/-
**Polynomial.natDegree_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {p : Polynomial R},   p 
≠ 0 → (p * Polynomial.X).natDegree = p.natDegree + 1
参数：p * Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
-/
@[simp] lemma natDegree_mul_X (hp : p ≠ 0) : natDegree (p * X) = natDegree p + 1 := by
  rw [natDegree_mul' (by simpa), natDegree_X]
/-
**Polynomial.natDegree_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {p : Polynomial R},   p 
≠ 0 → (Polynomial.X * p).natDegree = p.natDegree + 1
参数：Polynomial.X * p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `Polynomial.natDegree_mul_X`：∀ {R : Type u} [inst : Semiring R] [Nontrivi
al R] {p : Polynomial R},   p ≠ 0 → (p * Polynomial.X).natDegree = p.natDegree +
 1
-/
@[simp] lemma natDegree_X_mul (hp : p ≠ 0) : natDegree (X * p) = natDegree p + 1 := by
  rw [commute_X p, natDegree_mul_X hp]
/-
**Polynomial.natDegree_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {p : Polynomial R} (n : 
ℕ),   p ≠ 0 → (p * Polynomial.X ^ n).natDegree = p.natDegree + n
参数：n : ℕ；p * Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
-/
@[simp] lemma natDegree_mul_X_pow (hp : p ≠ 0) : natDegree (p * X ^ n) = natDegree p + n := by
  rw [natDegree_mul' (by simpa), natDegree_X_pow]
/-
**Polynomial.natDegree_X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] [Nontrivial R] {p : Polynomial R} (n : 
ℕ),   p ≠ 0 → (Polynomial.X ^ n * p).natDegree = p.natDegree + n
参数：n : ℕ；Polynomial.X ^ n * p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.commute_X_pow`：commute_X_pow (p : R[X]) (n : Nat) : Commute (
X ^ n) p
· 使用定理 `Polynomial.natDegree_mul_X_pow`：∀ {R : Type u} [inst : Semiring R] [Nont
rivial R] {p : Polynomial R} (n : ℕ),   p ≠ 0 → (p * Polynomial.X ^ n).natDegree
 = p.natDegree + n
-/
@[simp] lemma natDegree_X_pow_mul (hp : p ≠ 0) : natDegree (X ^ n * p) = natDegree p + n := by
  rw [commute_X_pow, natDegree_mul_X_pow n hp]

--  This lemma explicitly does not require the `Nontrivial R` assumption.
/-
**Polynomial.natDegree_X_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_pow_le {R : Type*} [Semiring R] (n : Nat) : (X ^ n : R[X]).nat
Degree <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : ℕ) : (X ^ n : R[X]).natDegree ≤ n := by
  nontriviality R
  rw [Polynomial.natDegree_X_pow]
/-
**Polynomial.not_isUnit_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_isUnit_X : ¬IsUnit (X : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_monomial_succ`：coeff_monomial_succ : coeff (monomial (n
 + 1) a) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem not_isUnit_X : ¬IsUnit (X : R[X]) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
  zero_ne_one' R <| by
    rw [← coeff_one_zero, ← hgf]
    simp

@[simp]
/-
**Polynomial.degree_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_X : degree (p * X) = degree p + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]

@[simp]
/-
**Polynomial.degree_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_X_pow : degree (p * X ^ n) = degree p + n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.degree_mul`：∀ {R : Type u} [inst : Semiring R] {p q : P
olynomial R}, q.Monic → (p * q).degree = p.degree + q.degree
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

/-
**Polynomial.degree_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sub_C (hp : 0 < degree p) : degree (p - C a) = degree p
参数：hp : 0 < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.degree_add_C`：degree_add_C (hp : 0 < degree p) : degree (p + 
C a) = degree p
-/
theorem degree_sub_C (hp : 0 < degree p) : degree (p - C a) = degree p := by
  rw [sub_eq_add_neg, ← C_neg, degree_add_C hp]

@[simp]
/-
**Polynomial.natDegree_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_C {a : R} : natDegree (p - C a) = natDegree p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
-/
theorem natDegree_sub_C {a : R} : natDegree (p - C a) = natDegree p := by
  rw [sub_eq_add_neg, ← C_neg, natDegree_add_C]
/-
**Polynomial.leadingCoeff_sub_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree
 p) : (p - q).leadingCoeff = p.leadingCoeff
参数：h : Polynomial.degree q < Polynomial.degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt'`：leadingCoeff_add_of_degree_lt
' (h : degree q < degree p) : leadingCoeff (p + q) = leadingCoeff p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree p) :
    (p - q).leadingCoeff = p.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt' h]
/-
**Polynomial.leadingCoeff_sub_of_degree_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degre
e q) : (p - q).leadingCoeff = -q.leadingCoeff
参数：h : Polynomial.degree p < Polynomial.degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_lt`：leadingCoeff_add_of_degree_lt 
(h : degree p < degree q) : leadingCoeff (p + q) = leadingCoeff q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
-/
theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by
  rw [← q.degree_neg] at h
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt h, leadingCoeff_neg]
/-
**Polynomial.leadingCoeff_sub_of_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_sub_of_degree_eq (h : degree p = degree q) (hlc : leadingCoef
f p != leadingCoeff q) : leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q
参数：h : degree p = degree q；hlc : leadingCoeff p != leadingCoeff q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Polynomial.leadingCoeff_add_of_degree_eq`：leadingCoeff_add_of_degree_eq 
(h : degree p = degree q) (hlc : leadingCoeff p + leadingCoeff q != 0) : leading
Coeff (p + q) = leadingCoeff p…
-/
theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p ≠ leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  replace hlc : leadingCoeff p + leadingCoeff (-q) ≠ 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_eq h hlc, leadingCoeff_neg, sub_eq_add_neg]
/-
**Polynomial.degree_sub_eq_left_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q)
 = degree p
参数：h : degree q < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]
/-
**Polynomial.degree_sub_eq_right_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q
) = degree q
参数：h : degree p < degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
-/
theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]
/-
**Polynomial.natDegree_sub_eq_left_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) : na
tDegree (p - q) = natDegree p
参数：h : natDegree q < natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))
/-
**Polynomial.natDegree_sub_eq_right_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) : n
atDegree (p - q) = natDegree q
参数：h : natDegree p < natDegree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_sub_eq_right_of_degree_lt`：degree_sub_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p - q) = degree q
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
-/
theorem natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p - q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))

end Ring

section NonzeroRing

variable [Nontrivial R]

section Semiring

variable [Semiring R]

@[simp]
/-
**Polynomial.degree_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_add_C (a : R) : degree (X + C a) = 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
-/
theorem degree_X_add_C (a : R) : degree (X + C a) = 1 := by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) ≤ 0 := degree_C_le
      _ < 1 := WithBot.coe_lt_coe.mpr zero_lt_one
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this, degree_X]
/-
**Polynomial.natDegree_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_add_C (x : R) : (X + C x).natDegree = 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.degree_X_add_C`：degree_X_add_C (a : R) : degree (X + C a) = 1
-/
theorem natDegree_X_add_C (x : R) : (X + C x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_X_add_C x

@[simp]
/-
**Polynomial.nextCoeff_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c
参数：c : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeff_of_natDegree_pos`：nextCoeff_of_natDegree_pos (hp : 
0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1)
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c := by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]
/-
**Polynomial.degree_X_pow_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_pow_add_C {n : Nat} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n
 + C a) = n
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Polynomial.degree_add_eq_left_of_degree_lt`：degree_add_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p + q) = degree p
-/
theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n + C a) = n := by
  have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt <| by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]
/-
**Polynomial.X_pow_add_C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_add_C_ne_zero {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a 
!= 0
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_pow_add_C`：degree_X_pow_add_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n + C a) = n
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) ≠ ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)
/-
**Polynomial.X_add_C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_add_C_ne_zero (r : R) : X + C r != 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_add_C_ne_zero`：X_pow_add_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n + C a != 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem X_add_C_ne_zero (r : R) : X + C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r
/-
**Polynomial.zero_notMem_multiset_map_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：zero_notMem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α -> R)
 : (0 : R[X]) ∉ m.map fun a => X + C (f a)
参数：m : Multiset α；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Polynomial.X_add_C_ne_zero`：X_add_C_ne_zero (r : R) : X + C r != 0
-/
theorem zero_notMem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X + C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha
/-
**Polynomial.natDegree_X_pow_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_pow_add_C {n : Nat} {r : R} : (X ^ n + C r).natDegree = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_X_pow_add_C {n : ℕ} {r : R} : (X ^ n + C r).natDegree = n := by
  simp
/-
**Polynomial.X_pow_add_C_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_add_C_ne_one {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a !
= 1
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_X_pow_add_C`：natDegree_X_pow_add_C {n : Nat} {r : R
} : (X ^ n + C r).natDegree = n
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem X_pow_add_C_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 1 := fun h =>
  hn.ne' <| by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h
/-
**Polynomial.X_add_C_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_add_C_ne_one (r : R) : X + C r != 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_add_C_ne_one`：X_pow_add_C_ne_one {n : Nat} (hn : 0 < n)
 (a : R) : (X : R[X]) ^ n + C a != 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem X_add_C_ne_one (r : R) : X + C r ≠ 1 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
/-
**Polynomial.leadingCoeff_X_pow_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_pow_add_C {n : Nat} (hn : 0 < n) {r : R} : (X ^ n + C r).le
adingCoeff = 1
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_X_pow_add_C`：natDegree_X_pow_add_C {n : Nat} {r : R
} : (X ^ n + C r).natDegree = n
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_X_pow_self`：coeff_X_pow_self (n : Nat) : coeff (X ^ n :
 R[X]) n = 1
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem leadingCoeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n + C r).leadingCoeff = 1 := by
  nontriviality R
  rw [leadingCoeff, natDegree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]

@[simp]
/-
**Polynomial.leadingCoeff_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.leadingCoeff_X_pow_add_C`：leadingCoeff_X_pow_add_C {n : Nat} 
(hn : 0 < n) {r : R} : (X ^ n + C r).leadingCoeff = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1 := by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]

@[simp]
/-
**Polynomial.leadingCoeff_X_pow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_pow_add_one {n : Nat} (hn : 0 < n) : (X ^ n + 1 : R[X]).lea
dingCoeff = 1
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_X_pow_add_C`：leadingCoeff_X_pow_add_C {n : Nat} 
(hn : 0 < n) {r : R} : (X ^ n + C r).leadingCoeff = 1
-/
theorem leadingCoeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_add_C hn

@[simp]
/-
**Polynomial.leadingCoeff_pow_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_pow_X_add_C (r : R) (i : Nat) : leadingCoeff ((X + C r) ^ i) 
= 1
参数：r : R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Polynomial.leadingCoeff_X_add_C`：leadingCoeff_X_add_C [Semiring S] (r : 
S) : (X + C r).leadingCoeff = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem leadingCoeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((X + C r) ^ i) = 1 := by
  nontriviality
  rw [leadingCoeff_pow'] <;> simp

variable [NoZeroDivisors R] {p q : R[X]}

@[simp]
/-
**Polynomial.degree_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul : degree (p * q) = degree p + degree q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
lemma degree_mul : degree (p * q) = degree p + degree q :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

/-- `degree` as a monoid homomorphism between `R[X]` and `Multiplicative (WithBot ℕ)`.
  This is useful to prove results about multiplication and degree. -/
/-
**Polynomial.degreeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：degreeMonoidHom [Nontrivial R] : R[X] ->* Multiplicative (WithBot Nat) whe
re toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q

--- 原说明 ---
`degree` as a monoid homomorphism between `R[X]` and `Multiplicative (WithBot ℕ)
`.
  This is useful to prove results about multiplication and degree.
-/
def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ) where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul

@[simp]
/-
**Polynomial.degree_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : degree (p ^ n) = n • degr
ee p
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
lemma degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p :=
  map_pow (@degreeMonoidHom R _ _ _) _ _

@[simp]
/-
**Polynomial.leadingCoeff_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * le
adingCoeff q
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
lemma leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

/-- `Polynomial.leadingCoeff` bundled as a `MonoidHom` when `R` has `NoZeroDivisors`, and thus
  `leadingCoeff` is multiplicative -/
/-
**Polynomial.leadingCoeffHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeffHom : R[X] ->* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q

--- 原说明 ---
`Polynomial.leadingCoeff` bundled as a `MonoidHom` when `R` has `NoZeroDivisors`
, and thus
  `leadingCoeff` is multiplicative
-/
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul

@[simp]
/-
**Polynomial.leadingCoeffHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  rfl

@[simp]
/-
**Polynomial.leadingCoeff_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_pow (p : R[X]) (n : Nat) : leadingCoeff (p ^ n) = leadingCoef
f p ^ n
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
lemma leadingCoeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (leadingCoeffHom : R[X] →* R).map_pow p n
/-
**Polynomial.leadingCoeff_dvd_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) : a.leadingCoeff 
∣ p.leadingCoeff
参数：hap : a ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma leadingCoeff_dvd_leadingCoeff {a p : R[X]} (hap : a ∣ p) :
    a.leadingCoeff ∣ p.leadingCoeff :=
  map_dvd leadingCoeffHom hap
/-
**Polynomial.degree_le_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_mul_left (p : R[X]) (hq : q != 0) : degree p <= degree (p * q)
参数：p : R[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
lemma degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · rw [degree_mul, degree_eq_natDegree hp, degree_eq_natDegree hq]
    exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)

end Semiring

section CommSemiring
variable [CommSemiring R] {a p : R[X]} (hp : p.Monic)
include hp

/-
**Polynomial.Monic.natDegree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → (0 < 
p.natDegree ↔ p ≠ 1)
参数：0 < p.natDegree ↔ p ≠ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
-/
lemma Monic.natDegree_pos : 0 < natDegree p ↔ p ≠ 1 :=
  Nat.pos_iff_ne_zero.trans hp.natDegree_eq_zero.not
/-
**Polynomial.Monic.degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → (0 < 
p.degree ↔ p ≠ 1)
参数：0 < p.degree ↔ p ≠ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.Monic.natDegree_pos`：∀ {R : Type u} [inst : CommSemiring R] {
p : Polynomial R}, p.Monic → (0 < p.natDegree ↔ p ≠ 1)
-/
lemma Monic.degree_pos : 0 < degree p ↔ p ≠ 1 :=
  natDegree_pos_iff_degree_pos.symm.trans hp.natDegree_pos

end CommSemiring

section Ring

variable [Ring R]

@[simp]
/-
**Polynomial.leadingCoeff_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_pow_sub_C {n : Nat} (hn : 0 < n) {r : R} : (X ^ n - C r).le
adingCoeff = 1
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.leadingCoeff_X_pow_add_C`：leadingCoeff_X_pow_add_C {n : Nat} 
(hn : 0 < n) {r : R} : (X ^ n + C r).leadingCoeff = 1
-/
theorem leadingCoeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_pow_add_C hn]

@[simp]
/-
**Polynomial.leadingCoeff_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_pow_sub_one {n : Nat} (hn : 0 < n) : (X ^ n - 1 : R[X]).lea
dingCoeff = 1
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_X_pow_sub_C`：leadingCoeff_X_pow_sub_C {n : Nat} 
(hn : 0 < n) {r : R} : (X ^ n - C r).leadingCoeff = 1
-/
theorem leadingCoeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_sub_C hn

variable [Nontrivial R]

@[simp]
/-
**Polynomial.degree_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_sub_C (a : R) : degree (X - C a) = 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.degree_X_add_C`：degree_X_add_C (a : R) : degree (X + C a) = 1
-/
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]
/-
**Polynomial.natDegree_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
-/
theorem natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1 := by
  rw [natDegree_sub_C, natDegree_X]

@[simp]
/-
**Polynomial.nextCoeff_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c
参数：c : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.nextCoeff_X_add_C`：nextCoeff_X_add_C [Semiring S] (c : S) : n
extCoeff (X + C c) = c
-/
theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, nextCoeff_X_add_C]
/-
**Polynomial.degree_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_X_pow_sub_C {n : Nat} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n
 - C a) = n
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.degree_X_pow_add_C`：degree_X_pow_add_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n + C a) = n
-/
theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n - C a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn]
/-
**Polynomial.X_pow_sub_C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a 
!= 0
参数：hn : 0 < n；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.X_pow_add_C_ne_zero`：X_pow_add_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n + C a != 0
-/
theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a ≠ 0 := by
  rw [sub_eq_add_neg, ← map_neg C a]
  exact X_pow_add_C_ne_zero hn _
/-
**Polynomial.X_sub_C_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_sub_C_ne_zero (r : R) : X - C r != 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r
/-
**Polynomial.zero_notMem_multiset_map_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：zero_notMem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α -> R)
 : (0 : R[X]) ∉ m.map fun a => X - C (f a)
参数：m : Multiset α；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
-/
theorem zero_notMem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X - C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha
/-
**Polynomial.natDegree_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_X_pow_sub_C {n : Nat} {r : R} : (X ^ n - C r).natDegree = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.natDegree_X_pow_add_C`：natDegree_X_pow_add_C {n : Nat} {r : R
} : (X ^ n + C r).natDegree = n
-/
theorem natDegree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - C r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg C r, natDegree_X_pow_add_C]

@[simp]
/-
**Polynomial.leadingCoeff_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.leadingCoeff_X_add_C`：leadingCoeff_X_add_C [Semiring S] (r : 
S) : (X + C r).leadingCoeff = 1
-/
theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_add_C]

end Ring
end Polynomial

