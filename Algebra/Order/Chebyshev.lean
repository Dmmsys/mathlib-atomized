/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev's sum inequality

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i`
when `f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.


## Main declarations

* `MonovaryOn.sum_mul_sum_le_card_mul_sum`: Chebyshev's inequality.
* `AntivaryOn.card_mul_sum_le_sum_mul_sum`: Chebyshev's inequality, dual version.
* `sq_sum_le_card_mul_sum_sq`: Special case of Chebyshev's inequality when `f = g`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `Monotone`/`Antitone` pairs of functions over a `LinearOrder` is not deduced in this
file because it is easily deducible from the `Monovary` API.
-/

public section


open Equiv Equiv.Perm Finset Function OrderDual

variable {ι α β : Type*}

/-! ### Scalar multiplication versions -/


section SMul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
/-
**MonovaryOn.sum_smul_sum_le_card_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) : (∑ i i
n s, f i) • ∑ i in s, g i <= #s • ∑ i in s, f i • g i
参数：hfg : MonovaryOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.exists_cycleOn`：∀ {α : Type u_2} {s : Set α}, s.Countable 
→ ∃ f, f.IsCycleOn s ∧ {x | f x ≠ x} ⊆ s
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.sum_smul_sum_eq_sum_perm`：sum_smul_sum_eq_sum_perm (hσ : σ.IsCycl
eOn s) (f : ι -> α) (g : ι -> β) : (∑ i in s, f i) • ∑ i in s, g i = ∑ k in rang
e #s, ∑ i in s, f i •…
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `Function.IsFixedPt.perm_pow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α}
, Function.IsFixedPt (⇑e) x → ∀ (n : ℕ), Function.IsFixedPt (⇑(e ^ n)) x

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they ar
e both
monotone/antitone), the scalar product of their sum is less than the size of the
 set times their
scalar product.
-/
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) • ∑ i ∈ s, g i ≤ #s • ∑ i ∈ s, f i • g i := by
  obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
  rw [← card_range #s, sum_smul_sum_eq_sum_perm hσ]
  exact sum_le_card_nsmul _ _ _ fun n _ ↦
    hfg.sum_smul_comp_perm_le_sum_smul fun x hx ↦ hs fun h ↦ hx <| IsFixedPt.perm_pow h _

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
/-
**AntivaryOn.card_smul_sum_le_sum_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) : #s • ∑
 i in s, f i • g i <= (∑ i in s, f i) • ∑ i in s, g i
参数：hfg : AntivaryOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_sum_le_card_smul_sum`：MonovaryOn.sum_smul_sum_le_car
d_smul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) • ∑ i in s, g i <= #s • ∑ 
i in s, f i • g i
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `AntivaryOn.dual_right`：AntivaryOn.dual_right : AntivaryOn f g s -> Monov
aryOn f (toDual ∘ g) s

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is 
monotone, the
other is antitone), the scalar product of their sum is less than the size of the
 set times their
scalar product.
-/
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    #s • ∑ i ∈ s, f i • g i ≤ (∑ i ∈ s, f i) • ∑ i ∈ s, g i :=
  hfg.dual_right.sum_smul_sum_le_card_smul_sum

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
/-
**Monovary.sum_smul_sum_le_card_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) : (∑ i, f i) •
 ∑ i, g i <= Fintype.card ι • ∑ i, f i • g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_sum_le_card_smul_sum`：MonovaryOn.sum_smul_sum_le_car
d_smul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) • ∑ i in s, g i <= #s • ∑ 
i in s, f i • g i
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they ar
e both
monotone/antitone), the scalar product of their sum is less than the size of the
 set times their
scalar product.
-/
theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    (∑ i, f i) • ∑ i, g i ≤ Fintype.card ι • ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
/-
**Antivary.card_smul_sum_le_sum_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) : Fintype.card
 ι • ∑ i, f i • g i <= (∑ i, f i) • ∑ i, g i
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_sum_le_card_smul_sum`：MonovaryOn.sum_smul_sum_le_car
d_smul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) • ∑ i in s, g i <= #s • ∑ 
i in s, f i • g i
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Antivary.dual_right`：Antivary.dual_right : Antivary f g -> Monovary f (t
oDual ∘ g)

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is 
monotone, the
other is antitone), the scalar product of their sum is less than the size of the
 set times their
scalar product.
-/
theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    Fintype.card ι • ∑ i, f i • g i ≤ (∑ i, f i) • ∑ i, g i :=
  (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
/-
**MonovaryOn.sum_mul_sum_le_card_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) : (∑ i in 
s, f i) * ∑ i in s, g i <= #s * ∑ i in s, f i * g i
参数：hfg : MonovaryOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MonovaryOn.sum_smul_sum_le_card_smul_sum`：MonovaryOn.sum_smul_sum_le_car
d_smul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) • ∑ i in s, g i <= #s • ∑ 
i in s, f i • g i
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they ar
e both
monotone/antitone), the product of their sum is less than the size of the set ti
mes their scalar
product.
-/
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * ∑ i ∈ s, g i ≤ #s * ∑ i ∈ s, f i * g i := by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the product of their sum is greater than the size of the set times their scalar
product. -/
/-
**AntivaryOn.card_mul_sum_le_sum_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) : (#s : α)
 * ∑ i in s, f i * g i <= (∑ i in s, f i) * ∑ i in s, g i
参数：hfg : AntivaryOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `AntivaryOn.card_smul_sum_le_sum_smul_sum`：AntivaryOn.card_smul_sum_le_su
m_smul_sum (hfg : AntivaryOn f g s) : #s • ∑ i in s, f i • g i <= (∑ i in s, f i
) • ∑ i in s, g i
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is 
monotone, the
other is antitone), the product of their sum is greater than the size of the set
 times their scalar
product.
-/
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    (#s : α) * ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

/-- Special case of **Jensen's inequality** for sums of powers. -/
/-
**pow_sum_le_card_mul_sum_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sum_le_card_mul_sum_pow (hf : forall i in s, 0 <= f i) : forall n, (∑ 
i in s, f i) ^ (n + 1) <= (#s : α) ^ n * ∑ i in s, f i ^ (n + 1) | 0 => by simp 
| n + 1 => calc _ = (∑ i in s, f i) ^ (n + 1) * ∑ i in s, f i
参数：hf : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Special case of **Jensen's inequality** for sums of powers.
-/
lemma pow_sum_le_card_mul_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∀ n, (∑ i ∈ s, f i) ^ (n + 1) ≤ (#s : α) ^ n * ∑ i ∈ s, f i ^ (n + 1)
  | 0 => by simp
  | n + 1 =>
    calc
      _ = (∑ i ∈ s, f i) ^ (n + 1) * ∑ i ∈ s, f i := by rw [pow_succ]
      _ ≤ (#s ^ n * ∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i ∈ s, f i ^ (n + 1)) * ∑ i ∈ s, f i) := by rw [mul_assoc]
      _ ≤ #s ^ n * (#s * ∑ i ∈ s, f i ^ (n + 1) * f i) := by
        gcongr _ * ?_
        exact ((monovaryOn_self ..).pow_left₀ hf _).sum_mul_sum_le_card_mul_sum
      _ = _ := by simp_rw [← mul_assoc, ← pow_succ]

/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequality**: The square
of the sum is less than the size of the set times the sum of the squares. -/
/-
**sq_sum_le_card_mul_sum_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sq_sum_le_card_mul_sum_sq : (∑ i in s, f i) ^ 2 <= #s * ∑ i in s, f i ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonovaryOn.sum_mul_sum_le_card_mul_sum`：MonovaryOn.sum_mul_sum_le_card_m
ul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) * ∑ i in s, g i <= #s * ∑ i in
 s, f i * g i
· 使用定理 `monovaryOn_self`：monovaryOn_self (f : ι -> α) (s : Set ι) : MonovaryOn f
 f s

--- 原说明 ---
Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequalit
y**: The square
of the sum is less than the size of the set times the sum of the squares.
-/
theorem sq_sum_le_card_mul_sum_sq : (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

variable [Fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
/-
**Monovary.sum_mul_sum_le_card_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) : (∑ i, f i) * ∑
 i, g i <= Fintype.card ι * ∑ i, f i * g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_mul_sum_le_card_mul_sum`：MonovaryOn.sum_mul_sum_le_card_m
ul_sum (hfg : MonovaryOn f g s) : (∑ i in s, f i) * ∑ i in s, g i <= #s * ∑ i in
 s, f i * g i
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` monovary together (e.g. they ar
e both
monotone/antitone), the product of their sum is less than the size of the set ti
mes their scalar
product.
-/
theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    (∑ i, f i) * ∑ i, g i ≤ Fintype.card ι * ∑ i, f i * g i :=
  (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is monotone, the
other is antitone), the product of their sum is less than the size of the set times their scalar
product. -/
/-
**Antivary.card_mul_sum_le_sum_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) : Fintype.card ι
 * ∑ i, f i * g i <= (∑ i, f i) * ∑ i, g i
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.card_mul_sum_le_sum_mul_sum`：AntivaryOn.card_mul_sum_le_sum_m
ul_sum (hfg : AntivaryOn f g s) : (#s : α) * ∑ i in s, f i * g i <= (∑ i in s, f
 i) * ∑ i in s, g i
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…

--- 原说明 ---
**Chebyshev's Sum Inequality**: When `f` and `g` antivary together (e.g. one is 
monotone, the
other is antitone), the product of their sum is less than the size of the set ti
mes their scalar
product.
-/
theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    Fintype.card ι * ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i :=
  (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

end Mul

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {f : ι → α}

/-- Special case of **Jensen's inequality** for sums of powers. -/
/-
**pow_sum_div_card_le_sum_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sum_div_card_le_sum_pow (hf : forall i in s, 0 <= f i) (n : Nat) : (∑ 
i in s, f i) ^ (n + 1) / #s ^ n <= ∑ i in s, f i ^ (n + 1)
参数：hf : forall i in s, 0 <= f i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用引理 `pow_sum_le_card_mul_sum_pow`：pow_sum_le_card_mul_sum_pow (hf : forall i 
in s, 0 <= f i) : forall n, (∑ i in s, f i) ^ (n + 1) <= (#s : α) ^ n * ∑ i in s
, f i ^ (n + 1) |…

--- 原说明 ---
Special case of **Jensen's inequality** for sums of powers.
-/
lemma pow_sum_div_card_le_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (n + 1) / #s ^ n ≤ ∑ i ∈ s, f i ^ (n + 1) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _
/-
**sum_div_card_sq_le_sum_sq_div_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_div_card_sq_le_sum_sq_div_card : ((∑ i in s, f i) / #s) ^ 2 <= (∑ i in
 s, f i ^ 2) / #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 34 条，此处仅展示前 30 条）
-/
theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i ∈ s, f i) / #s) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) / #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), sq (#s : α), mul_left_comm,
    ← mul_assoc]
  gcongr
  exact sq_sum_le_card_mul_sum_sq
