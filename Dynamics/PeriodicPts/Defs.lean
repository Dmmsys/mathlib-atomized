/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.Cycle
public import Mathlib.Data.PNat.Notation
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `IsPeriodicPt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `ptsOfPeriod f n` : the set `{x | IsPeriodicPt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodicPts f` : the set of all periodic points of `f`.
* `minimalPeriod f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.
* `orbit f x`: the cycle `[x, f x, f (f x), ...]` for a periodic point.
* `MulAction.period g x` : the minimal period of a point `x` under the multiplicative action of `g`;
  an equivalent `AddAction.period g x` is defined for additive actions.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : IsPeriodicPt f n x` including
arithmetic operations on `n` and `h.map (hg : SemiconjBy g f f')`. We also prove that `f`
is bijective on each set `ptsOfPeriod f n` and on `periodicPts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimalPeriod f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

@[expose] public section

assert_not_exists MonoidWithZero


open Set

namespace Function

open Function (Commute)

variable {α : Type*} {β : Type*} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
/-
**Function.IsPeriodicPt** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：IsPeriodicPt (f : α -> α) (n : Nat) (x : α)
参数：f : α -> α；n : Nat；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about peri
odic points
need this assumption.
-/
def IsPeriodicPt (f : α → α) (n : ℕ) (x : α) :=
  IsFixedPt f^[n] x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
/-
**Function.IsFixedPt.isPeriodicPt** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`
。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α}, Function.IsFixedPt f x → ∀ (n : ℕ), 
Function.IsPeriodicPt f n x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x

--- 原说明 ---
A fixed point of `f` is a periodic point of `f` of any prescribed period.
-/
theorem IsFixedPt.isPeriodicPt (hf : IsFixedPt f x) (n : ℕ) : IsPeriodicPt f n x :=
  hf.iterate n

/-- For the identity map, all points are periodic. -/
/-
**Function.is_periodic_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：is_periodic_id (n : Nat) (x : α) : IsPeriodicPt id n x
参数：n : Nat；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.isPeriodicPt`：∀ {α : Type u_1} {f : α → α} {x : α}, F
unction.IsFixedPt f x → ∀ (n : ℕ), Function.IsPeriodicPt f n x
· 使用定理 `Function.isFixedPt_id`：isFixedPt_id (x : α) : IsFixedPt id x

--- 原说明 ---
For the identity map, all points are periodic.
-/
theorem is_periodic_id (n : ℕ) (x : α) : IsPeriodicPt id n x :=
  (isFixedPt_id x).isPeriodicPt n

/-- Any point is a periodic point of period `0`. -/
/-
**Function.isPeriodicPt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：isPeriodicPt_zero (f : α -> α) (x : α) : IsPeriodicPt f 0 x
参数：f : α -> α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isFixedPt_id`：isFixedPt_id (x : α) : IsFixedPt id x

--- 原说明 ---
Any point is a periodic point of period `0`.
-/
theorem isPeriodicPt_zero (f : α → α) (x : α) : IsPeriodicPt f 0 x :=
  isFixedPt_id x

namespace IsPeriodicPt

@[nontriviality]
/-
**Function.IsPeriodicPt.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPe
riodicPt`。
形式化陈述：of_subsingleton [Subsingleton α] (f : α -> α) (n : Nat) (x : α) : IsPeriod
icPt f n x
参数：f : α -> α；n : Nat；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.of_subsingleton`：∀ {α : Type u₁} [Subsingleton α] (f 
: α → α) (x : α), Function.IsFixedPt f x
-/
theorem of_subsingleton [Subsingleton α] (f : α → α) (n : ℕ) (x : α) : IsPeriodicPt f n x :=
  IsFixedPt.of_subsingleton _ _
/-
**Function.IsPeriodicPt.** 是 Mathlib 中的一个实例，位于命名空间 `Function.IsPeriodicPt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (IsPeriodicPt f n x) :=
  IsFixedPt.decidable
/-
**Function.IsPeriodicPt.isFixedPt** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodic
Pt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x 
→ Function.IsFixedPt f^[n] x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem isFixedPt (hf : IsPeriodicPt f n x) : IsFixedPt f^[n] x :=
  hf
/-
**Function.IsPeriodicPt.map** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {x : α} {n : ℕ},
   Function.IsPeriodicPt fa n x → ∀ {g : α → β}, Function.Semiconj g fa fb → Fun
ction.IsPeriodicPt fb n (g x)
参数：g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.map`：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb
 : β → β} {x : α},   Function.IsFixedPt fa x → ∀ {g : α → β}, Function.Semiconj 
g fa fb → Fu…
· 使用定理 `Function.Semiconj.iterate_right`：iterate_right {f : α -> β} {ga : α -> α
} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
-/
protected theorem map (hx : IsPeriodicPt fa n x) {g : α → β} (hg : Semiconj g fa fb) :
    IsPeriodicPt fb n (g x) :=
  IsFixedPt.map hx (hg.iterate_right n)
/-
**Function.IsPeriodicPt.apply_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeri
odicPt`。
形式化陈述：apply_iterate (hx : IsPeriodicPt f n x) (m : Nat) : IsPeriodicPt f n (f^[m
] x)
参数：hx : IsPeriodicPt f n x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.map`：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} 
{fb : β → β} {x : α} {n : ℕ},   Function.IsPeriodicPt fa n x → ∀ {g : α → β}, Fu
nction.Semiconj…
· 使用定理 `Function.Commute.iterate_self`：iterate_self (n : Nat) : Commute f^[n] f
-/
theorem apply_iterate (hx : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f n (f^[m] x) :=
  hx.map <| Commute.iterate_self f m
/-
**Function.IsPeriodicPt.apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x 
→ Function.IsPeriodicPt f n (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.apply_iterate`：apply_iterate (hx : IsPeriodicPt f 
n x) (m : Nat) : IsPeriodicPt f n (f^[m] x)
-/
protected theorem apply (hx : IsPeriodicPt f n x) : IsPeriodicPt f n (f x) :=
  hx.apply_iterate 1
/-
**Function.IsPeriodicPt.add** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ},   Function.IsPeriodicPt f 
n x → Function.IsPeriodicPt f m x → Function.IsPeriodicPt f (n + m) x
参数：n + m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Function.IsFixedPt.comp`：∀ {α : Type u_1} {f g : α → α} {x : α}, Functio
n.IsFixedPt f x → Function.IsFixedPt g x → Function.IsFixedPt (f ∘ g) x
-/
protected theorem add (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f (n + m) x := by
  rw [IsPeriodicPt, iterate_add]
  exact hn.comp hm
/-
**Function.IsPeriodicPt.left_of_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriod
icPt`。
形式化陈述：left_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x) : Is
PeriodicPt f n x
参数：hn : IsPeriodicPt f (n + m) x；hm : IsPeriodicPt f m x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.left_of_comp`：left_of_comp (hfg : IsFixedPt (f ∘ g) x
) (hg : IsFixedPt g x) : IsFixedPt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
-/
theorem left_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f n x := by
  rw [IsPeriodicPt, iterate_add] at hn
  exact hn.left_of_comp hm
/-
**Function.IsPeriodicPt.right_of_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPerio
dicPt`。
形式化陈述：right_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x) : I
sPeriodicPt f m x
参数：hn : IsPeriodicPt f (n + m) x；hm : IsPeriodicPt f n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.left_of_add`：left_of_add (hn : IsPeriodicPt f (n +
 m) x) (hm : IsPeriodicPt f m x) : IsPeriodicPt f n x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem right_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x) :
    IsPeriodicPt f m x := by
  rw [add_comm] at hn
  exact hn.left_of_add hm
/-
**Function.IsPeriodicPt.sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ},   Function.IsPeriodicPt f 
m x → Function.IsPeriodicPt f n x → Function.IsPeriodicPt f (m - n) x
参数：m - n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Function.IsPeriodicPt.left_of_add`：left_of_add (hn : IsPeriodicPt f (n +
 m) x) (hm : IsPeriodicPt f m x) : IsPeriodicPt f n x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `Function.isPeriodicPt_zero`：isPeriodicPt_zero (f : α -> α) (x : α) : IsP
eriodicPt f 0 x
-/
protected theorem sub (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m - n) x := by
  rcases le_total n m with h | h
  · refine left_of_add ?_ hn
    rwa [tsub_add_cancel_of_le h]
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply isPeriodicPt_zero
/-
**Function.IsPeriodicPt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodic
Pt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m : ℕ}, Function.IsPeriodicPt f m x 
→ ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) x
参数：n : ℕ；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
· 使用定理 `Function.IsPeriodicPt.isFixedPt`：∀ {α : Type u_1} {f : α → α} {x : α} {n
 : ℕ}, Function.IsPeriodicPt f n x → Function.IsFixedPt f^[n] x
-/
protected theorem mul_const (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (m * n) x := by
  simp only [IsPeriodicPt, iterate_mul, hm.isFixedPt.iterate n]
/-
**Function.IsPeriodicPt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodic
Pt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m : ℕ}, Function.IsPeriodicPt f m x 
→ ∀ (n : ℕ), Function.IsPeriodicPt f (n * m) x
参数：n : ℕ；n * m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
-/
protected theorem const_mul (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (n * m) x := by
  simp only [mul_comm n, hm.mul_const n]
/-
**Function.IsPeriodicPt.trans_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodic
Pt`。
形式化陈述：trans_dvd (hm : IsPeriodicPt f m x) {n : Nat} (hn : m ∣ n) : IsPeriodicPt 
f n x
参数：hm : IsPeriodicPt f m x；hn : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem trans_dvd (hm : IsPeriodicPt f m x) {n : ℕ} (hn : m ∣ n) : IsPeriodicPt f n x :=
  let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k
/-
**Function.IsPeriodicPt.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt
`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x 
→ ∀ (m : ℕ), Function.IsPeriodicPt f^[m] n x
参数：m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
· 使用定理 `Function.IsPeriodicPt.isFixedPt`：∀ {α : Type u_1} {f : α → α} {x : α} {n
 : ℕ}, Function.IsPeriodicPt f n x → Function.IsFixedPt f^[n] x
-/
protected theorem iterate (hf : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f^[m] n x := by
  rw [IsPeriodicPt, ← iterate_mul, mul_comm, iterate_mul]
  exact hf.isFixedPt.iterate m
/-
**Function.IsPeriodicPt.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：comp {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPe
riodicPt g n x) : IsPeriodicPt (f ∘ g) n x
参数：hco : Commute f g；hf : IsPeriodicPt f n x；hg : IsPeriodicPt g n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `Function.IsFixedPt.comp`：∀ {α : Type u_1} {f g : α → α} {x : α}, Functio
n.IsFixedPt f x → Function.IsFixedPt g x → Function.IsFixedPt (f ∘ g) x
-/
theorem comp {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt (f ∘ g) n x := by
  rw [IsPeriodicPt, hco.comp_iterate]
  exact IsFixedPt.comp hf hg
/-
**Function.IsPeriodicPt.comp_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicP
t`。
形式化陈述：comp_lcm {g : α -> α} (hco : Commute f g) (hf : IsPeriodicPt f m x) (hg : 
IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) (Nat.lcm m n) x
参数：hco : Commute f g；hf : IsPeriodicPt f m x；hg : IsPeriodicPt g n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.comp`：comp {g : α -> α} (hco : Commute f g) (hf : 
IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) n x
· 使用定理 `Function.IsPeriodicPt.trans_dvd`：trans_dvd (hm : IsPeriodicPt f m x) {n 
: Nat} (hn : m ∣ n) : IsPeriodicPt f n x
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem comp_lcm {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f m x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) (Nat.lcm m n) x :=
  (hf.trans_dvd <| Nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_right _ _)
/-
**Function.IsPeriodicPt.left_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPerio
dicPt`。
形式化陈述：left_of_comp {g : α -> α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) 
n x) (hg : IsPeriodicPt g n x) : IsPeriodicPt f n x
参数：hco : Commute f g；hfg : IsPeriodicPt (f ∘ g) n x；hg : IsPeriodicPt g n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsFixedPt.left_of_comp`：left_of_comp (hfg : IsFixedPt (f ∘ g) x
) (hg : IsFixedPt g x) : IsFixedPt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
-/
theorem left_of_comp {g : α → α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt f n x := by
  rw [IsPeriodicPt, hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg
/-
**Function.IsPeriodicPt.iterate_mod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Is
PeriodicPt`。
形式化陈述：iterate_mod_apply (h : IsPeriodicPt f n x) (m : Nat) : f^[m % n] x = f^[m]
 x
参数：h : IsPeriodicPt f n x；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
-/
theorem iterate_mod_apply (h : IsPeriodicPt f n x) (m : ℕ) : f^[m % n] x = f^[m] x := by
  conv_rhs => rw [← Nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq]
/-
**Function.IsPeriodicPt.mod** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ},   Function.IsPeriodicPt f 
m x → Function.IsPeriodicPt f n x → Function.IsPeriodicPt f (m % n) x
参数：m % n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.IsPeriodicPt.iterate_mod_apply`：iterate_mod_apply (h : IsPeriod
icPt f n x) (m : Nat) : f^[m % n] x = f^[m] x
-/
protected theorem mod (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m % n) x :=
  (hn.iterate_mod_apply m).trans hm
/-
**Function.IsPeriodicPt.gcd** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ},   Function.IsPeriodicPt f 
m x → Function.IsPeriodicPt f n x → Function.IsPeriodicPt f (m.gcd n) x
参数：m.gcd n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd.induction`：∀ {P : ℕ → ℕ → Prop} (m n : ℕ), (∀ (n : ℕ), P 0 n) → 
(∀ (m n : ℕ), 0 < m → P (n % m) m → P m n) → P m n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
· 使用定理 `Function.IsPeriodicPt.mod`：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ
},   Function.IsPeriodicPt f m x → Function.IsPeriodicPt f n x → Function.IsPeri
odicPt f (m % n…
-/
protected theorem gcd (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m.gcd n) x := by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hn.mod hm) hm

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
/-
**Function.IsPeriodicPt.eq_of_apply_eq_same** 是 Mathlib 中的一个定理，位于命名空间 `Function.
IsPeriodicPt`。
形式化陈述：eq_of_apply_eq_same (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (h
n : 0 < n) (h : f x = f y) : x = y
参数：hx : IsPeriodicPt f n x；hy : IsPeriodicPt f n y；hn : 0 < n；h : f x = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.iterate_pred_comp_of_pos`：iterate_pred_comp_of_pos {n : Nat} (h
n : 0 < n) : f^[n.pred] ∘ f = f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)

--- 原说明 ---
If `f` sends two periodic points `x` and `y` of the same positive period to the 
same point,
then `x = y`. For a similar statement about points of different periods see `eq_
of_apply_eq`.
-/
theorem eq_of_apply_eq_same (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n)
    (h : f x = f y) : x = y := by
  rw [← hx.eq, ← hy.eq, ← iterate_pred_comp_of_pos f hn, comp_apply, comp_apply, h]

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
/-
**Function.IsPeriodicPt.eq_of_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPer
iodicPt`。
形式化陈述：eq_of_apply_eq (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0
 < m) (hn : 0 < n) (h : f x = f y) : x = y
参数：hx : IsPeriodicPt f m x；hy : IsPeriodicPt f n y；hm : 0 < m；hn : 0 < n；h : f x
 = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.eq_of_apply_eq_same`：eq_of_apply_eq_same (hx : IsP
eriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n) (h : f x = f y) : x = y
· 使用定理 `Function.IsPeriodicPt.mul_const`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (m * n) 
x
· 使用定理 `Function.IsPeriodicPt.const_mul`：∀ {α : Type u_1} {f : α → α} {x : α} {m
 : ℕ}, Function.IsPeriodicPt f m x → ∀ (n : ℕ), Function.IsPeriodicPt f (n * m) 
x
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m

--- 原说明 ---
If `f` sends two periodic points `x` and `y` of positive periods to the same poi
nt,
then `x = y`.
-/
theorem eq_of_apply_eq (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n)
    (h : f x = f y) : x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (Nat.mul_pos hm hn) h

end IsPeriodicPt

/-- The set of periodic points of a given (possibly non-minimal) period. -/
/-
**Function.ptsOfPeriod** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：ptsOfPeriod (f : α -> α) (n : Nat) : Set α
参数：f : α -> α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of periodic points of a given (possibly non-minimal) period.
-/
def ptsOfPeriod (f : α → α) (n : ℕ) : Set α :=
  { x : α | IsPeriodicPt f n x }

@[simp]
/-
**Function.mem_ptsOfPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mem_ptsOfPeriod : x in ptsOfPeriod f n ↔ IsPeriodicPt f n x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ptsOfPeriod : x ∈ ptsOfPeriod f n ↔ IsPeriodicPt f n x :=
  Iff.rfl
/-
**Function.Semiconj.mapsTo_ptsOfPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semic
onj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {g : α → β},   F
unction.Semiconj g fa fb → ∀ (n : ℕ), Set.MapsTo g (Function.ptsOfPeriod fa n) (
Function.ptsOfPeriod fb n)
参数：n : ℕ；Function.ptsOfPeriod fa n；Function.ptsOfPeriod fb n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.mapsTo_fixedPoints`：∀ {α : Type u_1} {β : Type u_2} {f
a : α → α} {fb : β → β} {g : α → β},   Function.Semiconj g fa fb → Set.MapsTo g 
(Function.fixedPoints fa) …
· 使用定理 `Function.Semiconj.iterate_right`：iterate_right {f : α -> β} {ga : α -> α
} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
-/
theorem Semiconj.mapsTo_ptsOfPeriod {g : α → β} (h : Semiconj g fa fb) (n : ℕ) :
    MapsTo g (ptsOfPeriod fa n) (ptsOfPeriod fb n) :=
  (h.iterate_right n).mapsTo_fixedPoints
/-
**Function.bijOn_ptsOfPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijOn_ptsOfPeriod (f : α -> α) {n : Nat} (hn : 0 < n) : BijOn f (ptsOfPeri
od f n) (ptsOfPeriod f n)
参数：f : α -> α；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.mapsTo_ptsOfPeriod`：∀ {α : Type u_1} {β : Type u_2} {f
a : α → α} {fb : β → β} {g : α → β},   Function.Semiconj g fa fb → ∀ (n : ℕ), Se
t.MapsTo g (Function.ptsOf…
· 使用定理 `Function.Commute.refl`：refl (f : α -> α) : Commute f f
· 使用定理 `Function.IsPeriodicPt.eq_of_apply_eq_same`：eq_of_apply_eq_same (hx : IsP
eriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n) (h : f x = f y) : x = y
· 使用定理 `Function.IsPeriodicPt.apply_iterate`：apply_iterate (hx : IsPeriodicPt f 
n x) (m : Nat) : IsPeriodicPt f n (f^[m] x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.comp_iterate_pred_of_pos`：comp_iterate_pred_of_pos {n : Nat} (h
n : 0 < n) : f ∘ f^[n.pred] = f^[n]
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
-/
theorem bijOn_ptsOfPeriod (f : α → α) {n : ℕ} (hn : 0 < n) :
    BijOn f (ptsOfPeriod f n) (ptsOfPeriod f n) :=
  ⟨(Commute.refl f).mapsTo_ptsOfPeriod n, fun _ hx _ hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
    ⟨f^[n.pred] x, hx.apply_iterate _, by
      rw [← comp_apply (f := f), comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

/-- The set of periodic points of a map `f : α → α`. -/
/-
**Function.periodicPts** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：periodicPts (f : α -> α) : Set α
参数：f : α -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of periodic points of a map `f : α → α`.
-/
def periodicPts (f : α → α) : Set α :=
  { x : α | ∃ n > 0, IsPeriodicPt f n x }
/-
**Function.mk_mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mk_mem_periodicPts (hn : 0 < n) (hx : IsPeriodicPt f n x) : x in periodicP
ts f
参数：hn : 0 < n；hx : IsPeriodicPt f n x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mem_periodicPts (hn : 0 < n) (hx : IsPeriodicPt f n x) : x ∈ periodicPts f :=
  ⟨n, hn, hx⟩
/-
**Function.mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mem_periodicPts : x in periodicPts f ↔ exists n > 0, IsPeriodicPt f n x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_periodicPts : x ∈ periodicPts f ↔ ∃ n > 0, IsPeriodicPt f n x :=
  Iff.rfl
/-
**Function.periodicPts_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicPts_subset_range : periodicPts f subseteq range f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_periodicPts`：mem_periodicPts : x in periodicPts f ↔ exists 
n > 0, IsPeriodicPt f n x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
-/
theorem periodicPts_subset_range : periodicPts f ⊆ range f := by
  intro x h
  rw [mem_periodicPts] at h
  rcases h with ⟨n, _, h⟩
  use f^[n - 1] x
  nth_rw 1 [← iterate_one f]
  rw [← iterate_add_apply, Nat.add_sub_cancel' (by lia)]
  exact h
/-
**Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate** 是 Mathlib 中
的一个定理，位于命名空间 `Function`。
形式化陈述：isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x in periodi
cPts f) (hm : IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x
参数：hx : x in periodicPts f；hm : IsPeriodicPt f m (f^[n] x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_div_mul_add`：∀ {a b : ℕ}, 0 < b → a < a / b * b + b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.IsPeriodicPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α} {n :
 ℕ}, Function.IsPeriodicPt f n x → ∀ (m : ℕ), Function.IsPeriodicPt f^[m] n x
· 使用定理 `Function.IsPeriodicPt.apply_iterate`：apply_iterate (hx : IsPeriodicPt f 
n x) (m : Nat) : IsPeriodicPt f n (f^[m] x)
-/
theorem isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x ∈ periodicPts f)
    (hm : IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x := by
  rcases hx with ⟨r, hr, hr'⟩
  suffices n ≤ (n / r + 1) * r by
    unfold IsPeriodicPt IsFixedPt
    convert! (hm.apply_iterate ((n / r + 1) * r - n)).eq <;>
      rw [← iterate_add_apply, Nat.sub_add_cancel this, iterate_mul, (hr'.iterate _).eq]
  rw [Nat.add_mul, one_mul]
  exact (Nat.lt_div_mul_add hr).le

variable (f)
/-
**Function.bUnion_ptsOfPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bUnion_ptsOfPeriod : ⋃ n > 0, ptsOfPeriod f n = periodicPts f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bUnion_ptsOfPeriod : ⋃ n > 0, ptsOfPeriod f n = periodicPts f :=
  Set.ext fun x => by simp [mem_periodicPts]
/-
**Function.iUnion_pnat_ptsOfPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iUnion_pnat_ptsOfPeriod : ⋃ n : Nat+, ptsOfPeriod f n = periodicPts f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Function.bUnion_ptsOfPeriod`：bUnion_ptsOfPeriod : ⋃ n > 0, ptsOfPeriod f
 n = periodicPts f
-/
theorem iUnion_pnat_ptsOfPeriod : ⋃ n : ℕ+, ptsOfPeriod f n = periodicPts f :=
  iSup_subtype.trans <| bUnion_ptsOfPeriod f

variable {f}
/-
**Function.Semiconj.mapsTo_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semic
onj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} {fb : β → β} {g : α → β},   F
unction.Semiconj g fa fb → Set.MapsTo g (Function.periodicPts fa) (Function.peri
odicPts fb)
参数：Function.periodicPts fa；Function.periodicPts fb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.map`：∀ {α : Type u_1} {β : Type u_2} {fa : α → α} 
{fb : β → β} {x : α} {n : ℕ},   Function.IsPeriodicPt fa n x → ∀ {g : α → β}, Fu
nction.Semiconj…
-/
theorem Semiconj.mapsTo_periodicPts {g : α → β} (h : Semiconj g fa fb) :
    MapsTo g (periodicPts fa) (periodicPts fb) := fun _ ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

noncomputable section

open scoped Classical in
/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimalPeriod f x = 0`. -/
/-
**Function.minimalPeriod** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：minimalPeriod (f : α -> α) (x : α)
参数：f : α -> α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodi
c point of `f`,
then `minimalPeriod f x = 0`.
-/
def minimalPeriod (f : α → α) (x : α) :=
  if h : x ∈ periodicPts f then Nat.find h else 0
/-
**Function.isPeriodicPt_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：isPeriodicPt_minimalPeriod (f : α -> α) (x : α) : IsPeriodicPt f (minimalP
eriod f x) x
参数：f : α -> α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Function.isPeriodicPt_zero`：isPeriodicPt_zero (f : α -> α) (x : α) : IsP
eriodicPt f 0 x
-/
theorem isPeriodicPt_minimalPeriod (f : α → α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x := by
  classical
  delta minimalPeriod
  split_ifs with hx
  · exact (Nat.find_spec hx).2
  · exact isPeriodicPt_zero f x

@[simp]
/-
**Function.iterate_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_minimalPeriod : f^[minimalPeriod f x] x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem iterate_minimalPeriod : f^[minimalPeriod f x] x = x :=
  isPeriodicPt_minimalPeriod f x

@[simp]
/-
**Function.iterate_add_minimalPeriod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_add_minimalPeriod_eq : f^[n + minimalPeriod f x] x = f^[n] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem iterate_add_minimalPeriod_eq : f^[n + minimalPeriod f x] x = f^[n] x := by
  rw [iterate_add_apply]
  congr
  exact isPeriodicPt_minimalPeriod f x

@[simp]
/-
**Function.iterate_mod_minimalPeriod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_mod_minimalPeriod_eq : f^[n % minimalPeriod f x] x = f^[n] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.iterate_mod_apply`：iterate_mod_apply (h : IsPeriod
icPt f n x) (m : Nat) : f^[m % n] x = f^[m] x
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem iterate_mod_minimalPeriod_eq : f^[n % minimalPeriod f x] x = f^[n] x :=
  (isPeriodicPt_minimalPeriod f x).iterate_mod_apply n
/-
**Function.minimalPeriod_pos_of_mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion`。
形式化陈述：minimalPeriod_pos_of_mem_periodicPts (hx : x in periodicPts f) : 0 < minim
alPeriod f x
参数：hx : x in periodicPts f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem minimalPeriod_pos_of_mem_periodicPts (hx : x ∈ periodicPts f) : 0 < minimalPeriod f x := by
  classical
  simp only [minimalPeriod, dif_pos hx, (Nat.find_spec hx).1.lt]
/-
**Function.minimalPeriod_eq_zero_of_notMem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间
 `Function`。
形式化陈述：minimalPeriod_eq_zero_of_notMem_periodicPts (hx : x ∉ periodicPts f) : min
imalPeriod f x = 0
参数：hx : x ∉ periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem minimalPeriod_eq_zero_of_notMem_periodicPts (hx : x ∉ periodicPts f) :
    minimalPeriod f x = 0 := by simp only [minimalPeriod, dif_neg hx]
/-
**Function.IsPeriodicPt.minimalPeriod_pos** 是 Mathlib 中的一个定理，位于命名空间 `Function.Is
PeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, 0 < n → Function.IsPeriodicP
t f n x → 0 < Function.minimalPeriod f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
· 使用定理 `Function.mk_mem_periodicPts`：mk_mem_periodicPts (hn : 0 < n) (hx : IsPer
iodicPt f n x) : x in periodicPts f
-/
theorem IsPeriodicPt.minimalPeriod_pos (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    0 < minimalPeriod f x :=
  minimalPeriod_pos_of_mem_periodicPts <| mk_mem_periodicPts hn hx
/-
**Function.minimalPeriod_pos_iff_mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion`。
形式化陈述：minimalPeriod_pos_iff_mem_periodicPts : 0 < minimalPeriod f x ↔ x in perio
dicPts f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
-/
theorem minimalPeriod_pos_iff_mem_periodicPts : 0 < minimalPeriod f x ↔ x ∈ periodicPts f :=
  ⟨not_imp_not.1 fun h => by simp only [minimalPeriod, dif_neg h, lt_irrefl 0, not_false_iff],
    minimalPeriod_pos_of_mem_periodicPts⟩
/-
**Function.minimalPeriod_eq_zero_iff_notMem_periodicPts** 是 Mathlib 中的一个定理，位于命名空
间 `Function`。
形式化陈述：minimalPeriod_eq_zero_iff_notMem_periodicPts : minimalPeriod f x = 0 ↔ x ∉
 periodicPts f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.minimalPeriod_pos_iff_mem_periodicPts`：minimalPeriod_pos_iff_me
m_periodicPts : 0 < minimalPeriod f x ↔ x in periodicPts f
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem minimalPeriod_eq_zero_iff_notMem_periodicPts :
    minimalPeriod f x = 0 ↔ x ∉ periodicPts f := by
  rw [← minimalPeriod_pos_iff_mem_periodicPts, not_lt, nonpos_iff_eq_zero]
/-
**Function.IsPeriodicPt.minimalPeriod_le** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsP
eriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, 0 < n → Function.IsPeriodicP
t f n x → Function.minimalPeriod f x ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.minimalPeriod.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.minimalPeriod f x = if h : x ∈ Function.periodicPts f then Nat.find h else
 0
· 使用定理 `Function.mk_mem_periodicPts`：mk_mem_periodicPts (hn : 0 < n) (hx : IsPer
iodicPt f n x) : x in periodicPts f
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
theorem IsPeriodicPt.minimalPeriod_le (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    minimalPeriod f x ≤ n := by
  classical
  rw [minimalPeriod, dif_pos (mk_mem_periodicPts hn hx)]
  exact Nat.find_min' (mk_mem_periodicPts hn hx) ⟨hn, hx⟩
/-
**Function.minimalPeriod_apply_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_apply_iterate (hx : x in periodicPts f) (n : Nat) : minimalP
eriod f (f^[n] x) = minimalPeriod f x
参数：hx : x in periodicPts f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
· 使用定理 `Function.IsPeriodicPt.apply_iterate`：apply_iterate (hx : IsPeriodicPt f 
n x) (m : Nat) : IsPeriodicPt f n (f^[m] x)
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
· 使用定理 `Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate`：isPeri
odicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x in periodicPts f) (hm 
: IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x
-/
theorem minimalPeriod_apply_iterate (hx : x ∈ periodicPts f) (n : ℕ) :
    minimalPeriod f (f^[n] x) = minimalPeriod f x := by
  apply
    (IsPeriodicPt.minimalPeriod_le (minimalPeriod_pos_of_mem_periodicPts hx) _).antisymm
      ((isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hx
            (isPeriodicPt_minimalPeriod f _)).minimalPeriod_le
        (minimalPeriod_pos_of_mem_periodicPts _))
  · exact (isPeriodicPt_minimalPeriod f x).apply_iterate n
  · rcases hx with ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.apply_iterate n⟩
/-
**Function.minimalPeriod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：minimalPeriod_apply (hx : x in periodicPts f) : minimalPeriod f (f x) = mi
nimalPeriod f x
参数：hx : x in periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_apply_iterate`：minimalPeriod_apply_iterate (hx : 
x in periodicPts f) (n : Nat) : minimalPeriod f (f^[n] x) = minimalPeriod f x
-/
theorem minimalPeriod_apply (hx : x ∈ periodicPts f) : minimalPeriod f (f x) = minimalPeriod f x :=
  minimalPeriod_apply_iterate hx 1
/-
**Function.le_of_lt_minimalPeriod_of_iterate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion`。
形式化陈述：le_of_lt_minimalPeriod_of_iterate_eq {m n : Nat} (hm : m < minimalPeriod f
 x) (hmn : f^[m] x = f^[n] x) : m <= n
参数：hm : m < minimalPeriod f x；hmn : f^[m] x = f^[n] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate`：isPeri
odicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x in periodicPts f) (hm 
: IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.minimalPeriod_pos_iff_mem_periodicPts`：minimalPeriod_pos_iff_me
m_periodicPts : 0 < minimalPeriod f x ↔ x in periodicPts f
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
-/
theorem le_of_lt_minimalPeriod_of_iterate_eq {m n : ℕ} (hm : m < minimalPeriod f x)
    (hmn : f^[m] x = f^[n] x) : m ≤ n := by
  by_contra! hmn'
  rw [← Nat.add_sub_of_le hmn'.le, add_comm, iterate_add_apply] at hmn
  exact ((IsPeriodicPt.minimalPeriod_le (tsub_pos_of_lt hmn')
    (isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
      (minimalPeriod_pos_iff_mem_periodicPts.1 hm.pos) hmn)).trans (Nat.sub_le m n)).not_gt hm
/-
**Function.iterate_injOn_Iio_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_injOn_Iio_minimalPeriod : (Iio <| minimalPeriod f x).InjOn (f^[·] 
x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Function.le_of_lt_minimalPeriod_of_iterate_eq`：le_of_lt_minimalPeriod_of
_iterate_eq {m n : Nat} (hm : m < minimalPeriod f x) (hmn : f^[m] x = f^[n] x) :
 m <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iterate_injOn_Iio_minimalPeriod : (Iio <| minimalPeriod f x).InjOn (f^[·] x) :=
  fun _m hm _n hn hmn ↦ (le_of_lt_minimalPeriod_of_iterate_eq hm hmn).antisymm
    (le_of_lt_minimalPeriod_of_iterate_eq hn hmn.symm)
/-
**Function.iterate_eq_iterate_iff_of_lt_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 
`Function`。
形式化陈述：iterate_eq_iterate_iff_of_lt_minimalPeriod {m n : Nat} (hm : m < minimalPe
riod f x) (hn : n < minimalPeriod f x) : f^[m] x = f^[n] x ↔ m = n
参数：hm : m < minimalPeriod f x；hn : n < minimalPeriod f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Function.iterate_injOn_Iio_minimalPeriod`：iterate_injOn_Iio_minimalPerio
d : (Iio <| minimalPeriod f x).InjOn (f^[·] x)
-/
theorem iterate_eq_iterate_iff_of_lt_minimalPeriod {m n : ℕ} (hm : m < minimalPeriod f x)
    (hn : n < minimalPeriod f x) : f^[m] x = f^[n] x ↔ m = n :=
  iterate_injOn_Iio_minimalPeriod.eq_iff hm hn
/-
**Function.minimalPeriod_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {x : α}, Function.minimalPeriod id x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `Function.is_periodic_id`：is_periodic_id (n : Nat) (x : α) : IsPeriodicPt
 id n x
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_pos`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → 0 < Function.minimalPeriod 
f x
-/
@[simp] theorem minimalPeriod_id : minimalPeriod id x = 1 :=
  ((is_periodic_id _ _).minimalPeriod_le Nat.one_pos).antisymm
    (Nat.succ_le_of_lt ((is_periodic_id _ _).minimalPeriod_pos Nat.one_pos))

@[simp]
/-
**Function.minimalPeriod_eq_one_iff_isFixedPt** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n`。
形式化陈述：minimalPeriod_eq_one_iff_isFixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Function.IsPeriodicPt.isFixedPt`：∀ {α : Type u_1} {f : α → α} {x : α} {n
 : ℕ}, Function.IsPeriodicPt f n x → Function.IsFixedPt f^[n] x
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `Function.IsFixedPt.isPeriodicPt`：∀ {α : Type u_1} {f : α → α} {x : α}, F
unction.IsFixedPt f x → ∀ (n : ℕ), Function.IsPeriodicPt f n x
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_pos`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → 0 < Function.minimalPeriod 
f x
-/
theorem minimalPeriod_eq_one_iff_isFixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← iterate_one f]
    refine Function.IsPeriodicPt.isFixedPt ?_
    rw [← h]
    exact isPeriodicPt_minimalPeriod f x
  · exact
      ((h.isPeriodicPt 1).minimalPeriod_le Nat.one_pos).antisymm
        (Nat.succ_le_of_lt ((h.isPeriodicPt 1).minimalPeriod_pos Nat.one_pos))

@[nontriviality]
/-
**Function.minimalPeriod_eq_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion`。
形式化陈述：minimalPeriod_eq_one_of_subsingleton [Subsingleton α] : minimalPeriod f x 
= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem minimalPeriod_eq_one_of_subsingleton [Subsingleton α] : minimalPeriod f x = 1 := by
  simp [nontriviality]
/-
**Function.IsPeriodicPt.eq_zero_of_lt_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `F
unction.IsPeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x 
→ n < Function.minimalPeriod f x → n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
-/
theorem IsPeriodicPt.eq_zero_of_lt_minimalPeriod (hx : IsPeriodicPt f n x)
    (hn : n < minimalPeriod f x) : n = 0 :=
  Eq.symm <|
    (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_lt.2 (hx.minimalPeriod_le hn0) hn
/-
**Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间
 `Function`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, n ≠ 0 → n < Function.minimal
Period f x → ¬Function.IsPeriodicPt f n x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Function.IsPeriodicPt.eq_zero_of_lt_minimalPeriod`：∀ {α : Type u_1} {f :
 α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x → n < Function.minimalPerio
d f x → n = 0
-/
theorem not_isPeriodicPt_of_pos_of_lt_minimalPeriod :
    ∀ {n : ℕ} (_ : n ≠ 0) (_ : n < minimalPeriod f x), ¬IsPeriodicPt f n x
  | 0, n0, _ => (n0 rfl).elim
  | _ + 1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimalPeriod hn)
/-
**Function.IsPeriodicPt.minimalPeriod_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Function.Is
PeriodicPt`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x 
→ Function.minimalPeriod f x ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.dvd_zero`：∀ (a : ℕ), a ∣ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Function.IsPeriodicPt.eq_zero_of_lt_minimalPeriod`：∀ {α : Type u_1} {f :
 α → α} {x : α} {n : ℕ}, Function.IsPeriodicPt f n x → n < Function.minimalPerio
d f x → n = 0
· 使用定理 `Function.IsPeriodicPt.mod`：∀ {α : Type u_1} {f : α → α} {x : α} {m n : ℕ
},   Function.IsPeriodicPt f m x → Function.IsPeriodicPt f n x → Function.IsPeri
odicPt f (m % n…
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_pos`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → 0 < Function.minimalPeriod 
f x
-/
theorem IsPeriodicPt.minimalPeriod_dvd (hx : IsPeriodicPt f n x) : minimalPeriod f x ∣ n :=
  (eq_or_lt_of_le <| n.zero_le).elim (fun hn0 => hn0 ▸ Nat.dvd_zero _) fun hn0 =>
    Nat.dvd_iff_mod_eq_zero.2 <|
      (hx.mod <| isPeriodicPt_minimalPeriod f x).eq_zero_of_lt_minimalPeriod <|
        Nat.mod_lt _ <| hx.minimalPeriod_pos hn0
/-
**Function.isPeriodicPt_iff_minimalPeriod_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n`。
形式化陈述：isPeriodicPt_iff_minimalPeriod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f 
x ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_dvd`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, Function.IsPeriodicPt f n x → Function.minimalPeriod f x ∣ n
· 使用定理 `Function.IsPeriodicPt.trans_dvd`：trans_dvd (hm : IsPeriodicPt f m x) {n 
: Nat} (hn : m ∣ n) : IsPeriodicPt f n x
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem isPeriodicPt_iff_minimalPeriod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n :=
  ⟨IsPeriodicPt.minimalPeriod_dvd, fun h => (isPeriodicPt_minimalPeriod f x).trans_dvd h⟩

open Nat
/-
**Function.minimalPeriod_eq_minimalPeriod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n`。
形式化陈述：minimalPeriod_eq_minimalPeriod_iff {g : β -> β} {y : β} : minimalPeriod f 
x = minimalPeriod g y ↔ forall n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem minimalPeriod_eq_minimalPeriod_iff {g : β → β} {y : β} :
    minimalPeriod f x = minimalPeriod g y ↔ ∀ n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y := by
  simp_rw [isPeriodicPt_iff_minimalPeriod_dvd, dvd_right_iff_eq]
/-
**Function.Commute.minimalPeriod_of_comp_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Commute`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {x : α} {g : α → α},   Function.Commute f g →
     Function.minimalPeriod (f ∘ g) x ∣ (Function.minimalPeriod f x).lcm (Functi
on.minimalPeriod g x)
参数：f ∘ g；Function.minimalPeriod f x；Function.minimalPeriod g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.isPeriodicPt_iff_minimalPeriod_dvd`：isPeriodicPt_iff_minimalPer
iod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
· 使用定理 `Function.IsPeriodicPt.comp_lcm`：comp_lcm {g : α -> α} (hco : Commute f g
) (hf : IsPeriodicPt f m x) (hg : IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) (Na
t.lcm m n) x
· 使用定理 `Function.isPeriodicPt_minimalPeriod`：isPeriodicPt_minimalPeriod (f : α -
> α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x
-/
theorem Commute.minimalPeriod_of_comp_dvd_lcm {g : α → α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ Nat.lcm (minimalPeriod f x) (minimalPeriod g x) := by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (isPeriodicPt_minimalPeriod f x).comp_lcm h (isPeriodicPt_minimalPeriod g x)
/-
**Function.minimalPeriod_iterate_eq_div_gcd_aux** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem minimalPeriod_iterate_eq_div_gcd_aux (h : 0 < gcd (minimalPeriod f x) n) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, ← iterate_mul, ← Nat.mul_div_assoc _ (gcd_dvd_left _ _),
      mul_comm, Nat.mul_div_assoc _ (gcd_dvd_right _ _), mul_comm, iterate_mul]
    exact (isPeriodicPt_minimalPeriod f x).iterate _
  · apply Coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
    apply Nat.dvd_of_mul_dvd_mul_right h
    rw [Nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc, Nat.div_mul_cancel (gcd_dvd_right _ _),
      mul_comm]
    apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, iterate_mul]
    exact isPeriodicPt_minimalPeriod _ _
/-
**Function.minimalPeriod_iterate_eq_div_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Function`
。
形式化陈述：minimalPeriod_iterate_eq_div_gcd (h : n != 0) : minimalPeriod f^[n] x = mi
nimalPeriod f x / Nat.gcd (minimalPeriod f x) n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Dynamics.PeriodicPts.Defs.0.Function.minimalPeriod_iter
ate_eq_div_gcd_aux`：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ},   0 < (Functio
n.minimalPeriod f x).gcd n →     Function.minimalPeriod f^[n] x = Function.minim
…
· 使用定理 `Nat.gcd_pos_of_pos_right`：∀ (m : ℕ) {n : ℕ}, 0 < n → 0 < m.gcd n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem minimalPeriod_iterate_eq_div_gcd (h : n ≠ 0) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
  minimalPeriod_iterate_eq_div_gcd_aux <| gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h)
/-
**Function.minimalPeriod_iterate_eq_div_gcd'** 是 Mathlib 中的一个定理，位于命名空间 `Function
`。
形式化陈述：minimalPeriod_iterate_eq_div_gcd' (h : x in periodicPts f) : minimalPeriod
 f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n
参数：h : x in periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Dynamics.PeriodicPts.Defs.0.Function.minimalPeriod_iter
ate_eq_div_gcd_aux`：∀ {α : Type u_1} {f : α → α} {x : α} {n : ℕ},   0 < (Functio
n.minimalPeriod f x).gcd n →     Function.minimalPeriod f^[n] x = Function.minim
…
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.minimalPeriod_pos_iff_mem_periodicPts`：minimalPeriod_pos_iff_me
m_periodicPts : 0 < minimalPeriod f x ↔ x in periodicPts f
-/
theorem minimalPeriod_iterate_eq_div_gcd' (h : x ∈ periodicPts f) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
  minimalPeriod_iterate_eq_div_gcd_aux <|
    gcd_pos_of_pos_left n (minimalPeriod_pos_iff_mem_periodicPts.mpr h)

/-- The orbit of a periodic point `x` of `f` is the cycle `[x, f x, f (f x), ...]`. Its length is
the minimal period of `x`.

If `x` is not a periodic point, then this is the empty (aka nil) cycle. -/
/-
**Function.periodicOrbit** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：periodicOrbit (f : α -> α) (x : α) : Cycle α
参数：f : α -> α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orbit of a periodic point `x` of `f` is the cycle `[x, f x, f (f x), ...]`. 
Its length is
the minimal period of `x`.

If `x` is not a periodic point, then this is the empty (aka nil) cycle.
-/
def periodicOrbit (f : α → α) (x : α) : Cycle α :=
  (List.range (minimalPeriod f x)).map fun n => f^[n] x

/-- The definition of a periodic orbit, in terms of `List.map`. -/
/-
**Function.periodicOrbit_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_def (f : α -> α) (x : α) : periodicOrbit f x = (List.range (
minimalPeriod f x)).map fun n => f^[n] x
参数：f : α -> α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of a periodic orbit, in terms of `List.map`.
-/
theorem periodicOrbit_def (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => f^[n] x :=
  rfl

/-- The definition of a periodic orbit, in terms of `Cycle.map`. -/
/-
**Function.periodicOrbit_eq_cycle_map** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_eq_cycle_map (f : α -> α) (x : α) : periodicOrbit f x = (Lis
t.range (minimalPeriod f x) : Cycle Nat).map fun n => f^[n] x
参数：f : α -> α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of a periodic orbit, in terms of `Cycle.map`.
-/
theorem periodicOrbit_eq_cycle_map (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x) : Cycle ℕ).map fun n => f^[n] x :=
  rfl

@[simp]
/-
**Function.periodicOrbit_length** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_length : (periodicOrbit f x).length = minimalPeriod f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.periodicOrbit.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.periodicOrbit f x = ↑(List.map (fun n => f^[n] x) (List.range (Function.mi
nimalPeriod f x))…
· 使用定理 `Cycle.length_coe`：length_coe (l : List α) : length (l : Cycle α) = l.len
gth
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
-/
theorem periodicOrbit_length : (periodicOrbit f x).length = minimalPeriod f x := by
  rw [periodicOrbit, Cycle.length_coe, List.length_map, List.length_range]

@[simp]
/-
**Function.periodicOrbit_eq_nil_iff_not_periodic_pt** 是 Mathlib 中的一个定理，位于命名空间 `F
unction`。
形式化陈述：periodicOrbit_eq_nil_iff_not_periodic_pt : periodicOrbit f x = Cycle.nil ↔
 x ∉ periodicPts f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.periodicOrbit.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.periodicOrbit f x = ↑(List.map (fun n => f^[n] x) (List.range (Function.mi
nimalPeriod f x))…
· 使用定理 `Function.minimalPeriod_eq_zero_iff_notMem_periodicPts`：minimalPeriod_eq_
zero_iff_notMem_periodicPts : minimalPeriod f x = 0 ↔ x ∉ periodicPts f
-/
theorem periodicOrbit_eq_nil_iff_not_periodic_pt :
    periodicOrbit f x = Cycle.nil ↔ x ∉ periodicPts f := by
  simp only [periodicOrbit.eq_1, Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil]
  exact minimalPeriod_eq_zero_iff_notMem_periodicPts
/-
**Function.periodicOrbit_eq_nil_of_not_periodic_pt** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction`。
形式化陈述：periodicOrbit_eq_nil_of_not_periodic_pt (h : x ∉ periodicPts f) : periodic
Orbit f x = Cycle.nil
参数：h : x ∉ periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.periodicOrbit_eq_nil_iff_not_periodic_pt`：periodicOrbit_eq_nil_
iff_not_periodic_pt : periodicOrbit f x = Cycle.nil ↔ x ∉ periodicPts f
-/
theorem periodicOrbit_eq_nil_of_not_periodic_pt (h : x ∉ periodicPts f) :
    periodicOrbit f x = Cycle.nil :=
  periodicOrbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]
/-
**Function.mem_periodicOrbit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mem_periodicOrbit_iff (hx : x in periodicPts f) : y in periodicOrbit f x ↔
 exists n, f^[n] x = y
参数：hx : x in periodicPts f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
· 使用定理 `Function.iterate_mod_minimalPeriod_eq`：iterate_mod_minimalPeriod_eq : f^
[n % minimalPeriod f x] x = f^[n] x
-/
theorem mem_periodicOrbit_iff (hx : x ∈ periodicPts f) :
    y ∈ periodicOrbit f x ↔ ∃ n, f^[n] x = y := by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]
  use fun ⟨a, _, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimalPeriod f x, mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx)
  rw [iterate_mod_minimalPeriod_eq]
/-
**Function.iterate_mem_periodicOrbit** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_mem_periodicOrbit (hx : x in periodicPts f) (n : Nat) : f^[n] x in
 periodicOrbit f x
参数：hx : x in periodicPts f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem iterate_mem_periodicOrbit (hx : x ∈ periodicPts f) (n : ℕ) :
    f^[n] x ∈ periodicOrbit f x := by
  simp [hx]

@[simp]
/-
**Function.exists_iterate_apply_eq_of_mem_periodicPts** 是 Mathlib 中的一个定理，位于命名空间 
`Function`。
形式化陈述：exists_iterate_apply_eq_of_mem_periodicPts (hx : x in periodicPts f) : exi
sts n, f^[n] x = x
参数：hx : x in periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.mem_periodicOrbit_iff`：mem_periodicOrbit_iff (hx : x in periodi
cPts f) : y in periodicOrbit f x ↔ exists n, f^[n] x = y
· 使用定理 `Function.iterate_mem_periodicOrbit`：iterate_mem_periodicOrbit (hx : x in
 periodicPts f) (n : Nat) : f^[n] x in periodicOrbit f x
-/
theorem exists_iterate_apply_eq_of_mem_periodicPts (hx : x ∈ periodicPts f) : ∃ n, f^[n] x = x := by
  simpa only [← mem_periodicOrbit_iff hx] using! iterate_mem_periodicOrbit hx 0
/-
**Function.self_mem_periodicOrbit** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：self_mem_periodicOrbit (hx : x in periodicPts f) : x in periodicOrbit f x
参数：hx : x in periodicPts f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem self_mem_periodicOrbit (hx : x ∈ periodicPts f) : x ∈ periodicOrbit f x := by
  simp [hx]
/-
**Function.nodup_periodicOrbit** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：nodup_periodicOrbit : (periodicOrbit f x).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.periodicOrbit.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.periodicOrbit f x = ↑(List.map (fun n => f^[n] x) (List.range (Function.mi
nimalPeriod f x))…
· 使用定理 `Cycle.nodup_coe_iff`：nodup_coe_iff {l : List α} : Nodup (l : Cycle α) ↔ 
l.Nodup
· 使用定理 `List.nodup_map_iff_inj_on`：nodup_map_iff_inj_on {f : α -> β} {l : List α
} (d : Nodup l) : Nodup (map f l) ↔ forall x in l, forall y in l, f x = f y -> x
 = y
· 使用定理 `List.nodup_range`：∀ {n : ℕ}, (List.range n).Nodup
· 使用定理 `Function.iterate_eq_iterate_iff_of_lt_minimalPeriod`：iterate_eq_iterate_
iff_of_lt_minimalPeriod {m n : Nat} (hm : m < minimalPeriod f x) (hn : n < minim
alPeriod f x) : f^[m] x = f^[n] x ↔ m = n
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
-/
theorem nodup_periodicOrbit : (periodicOrbit f x).Nodup := by
  rw [periodicOrbit, Cycle.nodup_coe_iff, List.nodup_map_iff_inj_on List.nodup_range]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn] at hmn
/-
**Function.periodicOrbit_apply_iterate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_apply_iterate_eq (hx : x in periodicPts f) (n : Nat) : perio
dicOrbit f (f^[n] x) = periodicOrbit f x
参数：hx : x in periodicPts f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cycle.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = (l₂ : C
ycle α) ↔ l₁ ~r l₂
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `Function.minimalPeriod_apply_iterate`：minimalPeriod_apply_iterate (hx : 
x in periodicPts f) (n : Nat) : minimalPeriod f (f^[n] x) = minimalPeriod f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `Function.iterate_mod_minimalPeriod_eq`：iterate_mod_minimalPeriod_eq : f^
[n % minimalPeriod f x] x = f^[n] x
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
-/
theorem periodicOrbit_apply_iterate_eq (hx : x ∈ periodicPts f) (n : ℕ) :
    periodicOrbit f (f^[n] x) = periodicOrbit f x :=
  Eq.symm <| Cycle.coe_eq_coe.2 <| .intro n <|
    List.ext_get (by simp [minimalPeriod_apply_iterate hx]) fun m _ _ ↦ by
      simp [List.getElem_rotate, iterate_add_apply]
/-
**Function.periodicOrbit_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_apply_eq (hx : x in periodicPts f) : periodicOrbit f (f x) =
 periodicOrbit f x
参数：hx : x in periodicPts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.periodicOrbit_apply_iterate_eq`：periodicOrbit_apply_iterate_eq 
(hx : x in periodicPts f) (n : Nat) : periodicOrbit f (f^[n] x) = periodicOrbit 
f x
-/
theorem periodicOrbit_apply_eq (hx : x ∈ periodicPts f) :
    periodicOrbit f (f x) = periodicOrbit f x :=
  periodicOrbit_apply_iterate_eq hx 1
/-
**Function.periodicOrbit_chain** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_chain (r : α -> α -> Prop) {f : α -> α} {x : α} : (periodicO
rbit f x).Chain r ↔ forall n < minimalPeriod f x, r (f^[n] x) (f^[n + 1] x)
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.periodicOrbit.eq_1`：∀ {α : Type u_1} (f : α → α) (x : α),   Fun
ction.periodicOrbit f x = ↑(List.map (fun n => f^[n] x) (List.range (Function.mi
nimalPeriod f x))…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cycle.map_coe`：map_coe {β : Type*} (f : α -> β) (l : List α) : map f ↑l 
= List.map f l
· 使用定理 `Cycle.chain_map`：chain_map {β : Type*} {r : α -> α -> Prop} (f : β -> α)
 {s : Cycle β} : Chain r (s.map f) ↔ Chain (fun a b => r (f a) (f b)) s
· 使用定理 `Cycle.chain_range_succ`：chain_range_succ (r : Nat -> Nat -> Prop) (n : N
at) : Chain r (List.range n.succ) ↔ r n 0 ∧ forall m < n, r m m.succ
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Function.iterate_minimalPeriod`：iterate_minimalPeriod : f^[minimalPeriod
 f x] x = x
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Function.periodicOrbit_eq_nil_of_not_periodic_pt`：periodicOrbit_eq_nil_o
f_not_periodic_pt (h : x ∉ periodicPts f) : periodicOrbit f x = Cycle.nil
· 使用定理 `Function.minimalPeriod_eq_zero_of_notMem_periodicPts`：minimalPeriod_eq_z
ero_of_notMem_periodicPts (hx : x ∉ periodicPts f) : minimalPeriod f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem periodicOrbit_chain (r : α → α → Prop) {f : α → α} {x : α} :
    (periodicOrbit f x).Chain r ↔ ∀ n < minimalPeriod f x, r (f^[n] x) (f^[n + 1] x) := by
  by_cases hx : x ∈ periodicPts f
  · have hx' := minimalPeriod_pos_of_mem_periodicPts hx
    have hM := Nat.sub_add_cancel (succ_le_iff.2 hx')
    rw [periodicOrbit, ← Cycle.map_coe, Cycle.chain_map, ← hM, Cycle.chain_range_succ]
    refine ⟨?_, fun H => ⟨?_, fun m hm => H _ (hm.trans (Nat.lt_succ_self _))⟩⟩
    · rintro ⟨hr, H⟩ n hn
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hn) with hM' | hM'
      · rwa [hM', hM, iterate_minimalPeriod]
      · exact H _ hM'
    · rw [iterate_zero_apply]
      nth_rw 3 [← @iterate_minimalPeriod α f x]
      nth_rw 2 [← hM]
      exact H _ (Nat.lt_succ_self _)
  · rw [periodicOrbit_eq_nil_of_not_periodic_pt hx, minimalPeriod_eq_zero_of_notMem_periodicPts hx]
    simp
/-
**Function.periodicOrbit_chain'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodicOrbit_chain' (r : α -> α -> Prop) {f : α -> α} {x : α} (hx : x in 
periodicPts f) : (periodicOrbit f x).Chain r ↔ forall n, r (f^[n] x) (f^[n + 1] 
x)
参数：r : α -> α -> Prop；hx : x in periodicPts f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.periodicOrbit_chain`：periodicOrbit_chain (r : α -> α -> Prop) {
f : α -> α} {x : α} : (periodicOrbit f x).Chain r ↔ forall n < minimalPeriod f x
, r (f^[n] x) (f^[…
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_mod_minimalPeriod_eq`：iterate_mod_minimalPeriod_eq : f^
[n % minimalPeriod f x] x = f^[n] x
· 使用定理 `Function.minimalPeriod_apply`：minimalPeriod_apply (hx : x in periodicPts
 f) : minimalPeriod f (f x) = minimalPeriod f x
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Function.minimalPeriod_pos_of_mem_periodicPts`：minimalPeriod_pos_of_mem_
periodicPts (hx : x in periodicPts f) : 0 < minimalPeriod f x
-/
theorem periodicOrbit_chain' (r : α → α → Prop) {f : α → α} {x : α} (hx : x ∈ periodicPts f) :
    (periodicOrbit f x).Chain r ↔ ∀ n, r (f^[n] x) (f^[n + 1] x) := by
  rw [periodicOrbit_chain r]
  refine ⟨fun H n => ?_, fun H n _ => H n⟩
  rw [iterate_succ_apply, ← iterate_mod_minimalPeriod_eq, ← iterate_mod_minimalPeriod_eq (n := n),
    ← iterate_succ_apply, minimalPeriod_apply hx]
  exact H _ (mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx))

end -- noncomputable

end Function

namespace Function

section Prod

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {a : α} {b : β} {m n : ℕ}

@[simp]
/-
**Function.isFixedPt_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → α} {g : β → β} (x : α × β),   Fun
ction.IsFixedPt (Prod.map f g) x ↔ Function.IsFixedPt f x.1 ∧ Function.IsFixedPt
 g x.2
参数：x : α × β；Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem isFixedPt_prodMap (x : α × β) :
    IsFixedPt (Prod.map f g) x ↔ IsFixedPt f x.1 ∧ IsFixedPt g x.2 :=
  Prod.ext_iff
/-
**Function.IsFixedPt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → α} {g : β → β} {a : α} {b : β},  
 Function.IsFixedPt f a → Function.IsFixedPt g b → Function.IsFixedPt (Prod.map 
f g) (a, b)
参数：Prod.map f g；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.isFixedPt_prodMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → α} 
{g : β → β} (x : α × β),   Function.IsFixedPt (Prod.map f g) x ↔ Function.IsFixe
dPt f x.1 ∧ Func…
-/
theorem IsFixedPt.prodMap (ha : IsFixedPt f a) (hb : IsFixedPt g b) :
    IsFixedPt (Prod.map f g) (a, b) :=
  (isFixedPt_prodMap _).mpr ⟨ha, hb⟩

@[simp]
/-
**Function.isPeriodicPt_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → α} {g : β → β} {n : ℕ} (x : α × β
),   Function.IsPeriodicPt (Prod.map f g) n x ↔ Function.IsPeriodicPt f n x.1 ∧ 
Function.IsPeriodicPt g n x.2
参数：x : α × β；Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.map_iterate`：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Pro
d.map f g)^[n] = Prod.map f^[n] g^[n]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPeriodicPt_prodMap (x : α × β) :
    IsPeriodicPt (Prod.map f g) n x ↔ IsPeriodicPt f n x.1 ∧ IsPeriodicPt g n x.2 := by
  simp [IsPeriodicPt]
/-
**Function.IsPeriodicPt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → α} {g : β → β} {a : α} {b : β} {n
 : ℕ},   Function.IsPeriodicPt f n a → Function.IsPeriodicPt g n b → Function.Is
PeriodicPt (Prod.map f g) n (a, b)
参数：Prod.map f g；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.isPeriodicPt_prodMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
α} {g : β → β} {n : ℕ} (x : α × β),   Function.IsPeriodicPt (Prod.map f g) n x ↔
 Function.IsPeriodi…
-/
theorem IsPeriodicPt.prodMap (ha : IsPeriodicPt f n a) (hb : IsPeriodicPt g n b) :
    IsPeriodicPt (Prod.map f g) n (a, b) :=
  (isPeriodicPt_prodMap _).mpr ⟨ha, hb⟩

end Prod

section Pi

variable {ι : Type*} {α : ι → Type*} {f : ∀ i, α i → α i} {x : ∀ i, α i} {n : ℕ}

@[simp]
/-
**Function.isFixedPt_piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → α i → α i} {x : (i : ι)
 → α i},   Function.IsFixedPt (Pi.map f) x ↔ ∀ (i : ι), Function.IsFixedPt (f i)
 (x i)
参数：i : ι；i : ι；Pi.map f；i : ι；f i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem isFixedPt_piMap : IsFixedPt (Pi.map f) x ↔ ∀ i, IsFixedPt (f i) (x i) :=
  funext_iff
/-
**Function.IsFixedPt.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → α i → α i} {x : (i : ι)
 → α i},   (∀ (i : ι), Function.IsFixedPt (f i) (x i)) → Function.IsFixedPt (Pi.
map f) x
参数：i : ι；i : ι；∀ (i : ι), Function.IsFixedPt (f i) (x i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.isFixedPt_piMap`：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : 
ι) → α i → α i} {x : (i : ι) → α i},   Function.IsFixedPt (Pi.map f) x ↔ ∀ (i : 
ι), Function.I…
-/
theorem IsFixedPt.piMap (h : ∀ i, IsFixedPt (f i) (x i)) : IsFixedPt (Pi.map f) x :=
  isFixedPt_piMap.mpr h

@[simp]
/-
**Function.isPeriodicPt_piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → α i → α i} {x : (i : ι)
 → α i} {n : ℕ},   Function.IsPeriodicPt (Pi.map f) n x ↔ ∀ (i : ι), Function.Is
PeriodicPt (f i) n (x i)
参数：i : ι；i : ι；Pi.map f；i : ι；f i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.map_iterate`：map_iterate {α : ι -> Type*} (f : forall i, α i -> α i) 
(n : Nat) : (Pi.map f)^[n] = Pi.map fun i => (f i)^[n]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPeriodicPt_piMap : IsPeriodicPt (Pi.map f) n x ↔ ∀ i, IsPeriodicPt (f i) n (x i) := by
  simp [IsPeriodicPt]
/-
**Function.IsPeriodicPt.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsPeriodicPt`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i : ι) → α i → α i} {x : (i : ι)
 → α i} {n : ℕ},   (∀ (i : ι), Function.IsPeriodicPt (f i) n (x i)) → Function.I
sPeriodicPt (Pi.map f) n x
参数：i : ι；i : ι；∀ (i : ι), Function.IsPeriodicPt (f i) n (x i)；Pi.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.isPeriodicPt_piMap`：∀ {ι : Type u_1} {α : ι → Type u_2} {f : (i
 : ι) → α i → α i} {x : (i : ι) → α i} {n : ℕ},   Function.IsPeriodicPt (Pi.map 
f) n x ↔ ∀ (i : ι…
-/
theorem IsPeriodicPt.piMap (h : ∀ i, IsPeriodicPt (f i) n (x i)) : IsPeriodicPt (Pi.map f) n x :=
  isPeriodicPt_piMap.mpr h

end Pi

end Function

namespace MulAction

open Function

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/--
The period of a multiplicative action of `g` on `a` is the smallest positive `n` such that
`g ^ n • a = a`, or `0` if such an `n` does not exist.
-/
@[to_additive /-- The period of an additive action of `g` on `a` is the smallest positive `n`
such that `(n • g) +ᵥ a = a`, or `0` if such an `n` does not exist. -/]
/-
**MulAction.period** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：{α : Type v} → {M : Type u} → [inst : Monoid M] → [MulAction M α] → M → α 
→ ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def period (m : M) (a : α) : ℕ := minimalPeriod (fun x => m • x) a

/-- `MulAction.period m a` is definitionally equal to `Function.minimalPeriod (m • ·) a`. -/
@[to_additive /-- `AddAction.period m a` is definitionally equal to
`Function.minimalPeriod (m +ᵥ ·) a` -/]
/-
**MulAction.period_eq_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] {m 
: M} {a : α},   MulAction.period m a = Function.minimalPeriod (fun x => m • x) a
参数：fun x => m • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem period_eq_minimalPeriod {m : M} {a : α} :
    MulAction.period m a = minimalPeriod (fun x => m • x) a := rfl

/-- `m ^ (period m a)` fixes `a`. -/
@[to_additive (attr := simp) /-- `(period m a) • m` fixes `a`. -/]
/-
**MulAction.pow_period_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] (m 
: M) (a : α), m ^ MulAction.period m a • a = a
参数：m : M；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_iterate_apply`：smul_iterate_apply (a : M) (n : Nat) (x : α) : (a • 
·)^[n] x = a ^ n • x
· 使用定理 `Function.iterate_minimalPeriod`：iterate_minimalPeriod : f^[minimalPeriod
 f x] x = x

--- 原说明 ---
`m ^ (period m a)` fixes `a`.
-/
theorem pow_period_smul (m : M) (a : α) : m ^ (period m a) • a = a := by
  rw [period_eq_minimalPeriod, ← smul_iterate_apply, iterate_minimalPeriod]

@[to_additive]
/-
**MulAction.isPeriodicPt_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] {m 
: M} {a : α} {n : ℕ},   Function.IsPeriodicPt (fun x => m • x) n a ↔ m ^ n • a =
 a
参数：fun x => m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_iterate_apply`：smul_iterate_apply (a : M) (n : Nat) (x : α) : (a • 
·)^[n] x = a ^ n • x
· 使用定理 `Function.IsPeriodicPt.eq_1`：∀ {α : Type u_1} (f : α → α) (n : ℕ) (x : α)
, Function.IsPeriodicPt f n x = Function.IsFixedPt f^[n] x
· 使用定理 `Function.IsFixedPt.eq_1`：∀ {α : Type u₁} (f : α → α) (x : α), Function.I
sFixedPt f x = (f x = x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPeriodicPt_smul_iff {m : M} {a : α} {n : ℕ} :
    IsPeriodicPt (m • ·) n a ↔ m ^ n • a = a := by
  rw [← smul_iterate_apply, IsPeriodicPt, IsFixedPt]

/-! ### Multiples of `MulAction.period`

It is easy to convince oneself that if `g ^ n • a = a` (resp. `(n • g) +ᵥ a = a`),
then `n` must be a multiple of `period g a`.

This also holds for negative powers/multiples.
-/

@[to_additive]
/-
**MulAction.pow_smul_eq_iff_period_dvd** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] {n 
: ℕ} {m : M} {a : α},   m ^ n • a = a ↔ MulAction.period m a ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.isPeriodicPt_iff_minimalPeriod_dvd`：isPeriodicPt_iff_minimalPer
iod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n
· 使用定理 `MulAction.isPeriodicPt_smul_iff`：∀ {α : Type v} {M : Type u} [inst : Mon
oid M] [inst_1 : MulAction M α] {m : M} {a : α} {n : ℕ},   Function.IsPeriodicPt
 (fun x => m • x) n a…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Multiples of `MulAction.period`

It is easy to convince oneself that if `g ^ n • a = a` (resp. `(n • g) +ᵥ a = a`
),
then `n` must be a multiple of `period g a`.

This also holds for negative powers/multiples.
-/
theorem pow_smul_eq_iff_period_dvd {n : ℕ} {m : M} {a : α} :
    m ^ n • a = a ↔ period m a ∣ n := by
  rw [period_eq_minimalPeriod, ← isPeriodicPt_iff_minimalPeriod_dvd, isPeriodicPt_smul_iff]

@[to_additive]
/-
**MulAction.zpow_smul_eq_iff_period_dvd** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] {j :
 ℤ} {g : G} {a : α},   g ^ j • a = a ↔ ↑(MulAction.period g a) ∣ j
参数：MulAction.period g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `MulAction.pow_smul_eq_iff_period_dvd`：∀ {α : Type v} {M : Type u} [inst 
: Monoid M] [inst_1 : MulAction M α] {n : ℕ} {m : M} {a : α},   m ^ n • a = a ↔ 
MulAction.period m a ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Int.dvd_neg`：∀ {a b : ℤ}, a ∣ -b ↔ a ∣ b
-/
theorem zpow_smul_eq_iff_period_dvd {j : ℤ} {g : G} {a : α} :
    g ^ j • a = a ↔ (period g a : ℤ) ∣ j := by
  match j with
  | (n : ℕ) => rw [zpow_natCast, Int.natCast_dvd_natCast, pow_smul_eq_iff_period_dvd]
  | -(n + 1 : ℕ) =>
    rw [zpow_neg, zpow_natCast, inv_smul_eq_iff, eq_comm, Int.dvd_neg, Int.natCast_dvd_natCast,
      pow_smul_eq_iff_period_dvd]

@[to_additive (attr := simp)]
/-
**MulAction.pow_mod_period_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] (n 
: ℕ) {m : M} {a : α},   m ^ (n % MulAction.period m a) • a = m ^ n • a
参数：n : ℕ；n % MulAction.period m a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.pow_smul_eq_iff_period_dvd`：∀ {α : Type v} {M : Type u} [inst 
: Monoid M] [inst_1 : MulAction M α] {n : ℕ} {m : M} {a : α},   m ^ n • a = a ↔ 
MulAction.period m a ∣ n
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem pow_mod_period_smul (n : ℕ) {m : M} {a : α} :
    m ^ (n % period m a) • a = m ^ n • a := by
  conv_rhs => rw [← Nat.mod_add_div n (period m a), pow_add, mul_smul,
    pow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
/-
**MulAction.zpow_mod_period_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] (j :
 ℤ) {g : G} {a : α},   g ^ (j % ↑(MulAction.period g a)) • a = g ^ j • a
参数：j : ℤ；j % ↑(MulAction.period g a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.zpow_smul_eq_iff_period_dvd`：∀ {α : Type v} {G : Type u} [inst
 : Group G] [inst_1 : MulAction G α] {j : ℤ} {g : G} {a : α},   g ^ j • a = a ↔ 
↑(MulAction.period g a) ∣ j
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem zpow_mod_period_smul (j : ℤ) {g : G} {a : α} :
    g ^ (j % (period g a : ℤ)) • a = g ^ j • a := by
  conv_rhs => rw [← Int.emod_add_mul_ediv j (period g a), zpow_add, mul_smul,
    zpow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
/-
**MulAction.pow_add_period_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] (n 
: ℕ) (m : M) (a : α),   m ^ (n + MulAction.period m a) • a = m ^ n • a
参数：n : ℕ；m : M；a : α；n + MulAction.period m a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.pow_mod_period_smul`：∀ {α : Type v} {M : Type u} [inst : Monoi
d M] [inst_1 : MulAction M α] (n : ℕ) {m : M} {a : α},   m ^ (n % MulAction.peri
od m a) • a = m ^ n…
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
-/
theorem pow_add_period_smul (n : ℕ) (m : M) (a : α) :
    m ^ (n + period m a) • a = m ^ n • a := by
  rw [← pow_mod_period_smul, Nat.add_mod_right, pow_mod_period_smul]

@[to_additive (attr := simp)]
/-
**MulAction.pow_period_add_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {M : Type u} [inst : Monoid M] [inst_1 : MulAction M α] (n 
: ℕ) (m : M) (a : α),   m ^ (MulAction.period m a + n) • a = m ^ n • a
参数：n : ℕ；m : M；a : α；MulAction.period m a + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.pow_mod_period_smul`：∀ {α : Type v} {M : Type u} [inst : Monoi
d M] [inst_1 : MulAction M α] (n : ℕ) {m : M} {a : α},   m ^ (n % MulAction.peri
od m a) • a = m ^ n…
· 使用定理 `Nat.add_mod_left`：∀ (x z : ℕ), (x + z) % x = z % x
-/
theorem pow_period_add_smul (n : ℕ) (m : M) (a : α) :
    m ^ (period m a + n) • a = m ^ n • a := by
  rw [← pow_mod_period_smul, Nat.add_mod_left, pow_mod_period_smul]

@[to_additive (attr := simp)]
/-
**MulAction.zpow_add_period_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] (i :
 ℤ) (g : G) (a : α),   g ^ (i + ↑(MulAction.period g a)) • a = g ^ i • a
参数：i : ℤ；g : G；a : α；i + ↑(MulAction.period g a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.zpow_mod_period_smul`：∀ {α : Type v} {G : Type u} [inst : Grou
p G] [inst_1 : MulAction G α] (j : ℤ) {g : G} {a : α},   g ^ (j % ↑(MulAction.pe
riod g a)) • a = g ^…
· 使用定理 `Int.add_emod_right`：∀ (a b : ℤ), (a + b) % b = a % b
-/
theorem zpow_add_period_smul (i : ℤ) (g : G) (a : α) :
    g ^ (i + period g a) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul, Int.add_emod_right, zpow_mod_period_smul]

@[to_additive (attr := simp)]
/-
**MulAction.zpow_period_add_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] (i :
 ℤ) (g : G) (a : α),   g ^ (↑(MulAction.period g a) + i) • a = g ^ i • a
参数：i : ℤ；g : G；a : α；↑(MulAction.period g a) + i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.zpow_mod_period_smul`：∀ {α : Type v} {G : Type u} [inst : Grou
p G] [inst_1 : MulAction G α] (j : ℤ) {g : G} {a : α},   g ^ (j % ↑(MulAction.pe
riod g a)) • a = g ^…
· 使用定理 `Int.add_emod_left`：∀ (a b : ℤ), (a + b) % a = b % a
-/
theorem zpow_period_add_smul (i : ℤ) (g : G) (a : α) :
    g ^ (period g a + i) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul, Int.add_emod_left, zpow_mod_period_smul]

variable {a : G} {b : α}

@[to_additive]
/-
**MulAction.pow_smul_eq_iff_minimalPeriod_dvd** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] {a :
 G} {b : α} {n : ℕ},   a ^ n • b = b ↔ Function.minimalPeriod (fun x => a • x) b
 ∣ n
参数：fun x => a • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `MulAction.pow_smul_eq_iff_period_dvd`：∀ {α : Type v} {M : Type u} [inst 
: Monoid M] [inst_1 : MulAction M α] {n : ℕ} {m : M} {a : α},   m ^ n • a = a ↔ 
MulAction.period m a ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_smul_eq_iff_minimalPeriod_dvd {n : ℕ} :
    a ^ n • b = b ↔ minimalPeriod (a • ·) b ∣ n := by
  rw [← period_eq_minimalPeriod, pow_smul_eq_iff_period_dvd]

@[to_additive]
/-
**MulAction.zpow_smul_eq_iff_minimalPeriod_dvd** 是 Mathlib 中的一个定理，位于命名空间 `MulAct
ion`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] {a :
 G} {b : α} {n : ℤ},   a ^ n • b = b ↔ ↑(Function.minimalPeriod (fun x => a • x)
 b) ∣ n
参数：Function.minimalPeriod (fun x => a • x) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `MulAction.zpow_smul_eq_iff_period_dvd`：∀ {α : Type v} {G : Type u} [inst
 : Group G] [inst_1 : MulAction G α] {j : ℤ} {g : G} {a : α},   g ^ j • a = a ↔ 
↑(MulAction.period g a) ∣ j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zpow_smul_eq_iff_minimalPeriod_dvd {n : ℤ} :
    a ^ n • b = b ↔ (minimalPeriod (a • ·) b : ℤ) ∣ n := by
  rw [← period_eq_minimalPeriod, zpow_smul_eq_iff_period_dvd]

variable (a b)

@[to_additive (attr := simp)]
/-
**MulAction.pow_smul_mod_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] (a :
 G) (b : α) (n : ℕ),   a ^ (n % Function.minimalPeriod (fun x => a • x) b) • b =
 a ^ n • b
参数：a : G；b : α；n : ℕ；n % Function.minimalPeriod (fun x => a • x) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `MulAction.pow_mod_period_smul`：∀ {α : Type v} {M : Type u} [inst : Monoi
d M] [inst_1 : MulAction M α] (n : ℕ) {m : M} {a : α},   m ^ (n % MulAction.peri
od m a) • a = m ^ n…
-/
theorem pow_smul_mod_minimalPeriod (n : ℕ) :
    a ^ (n % minimalPeriod (a • ·) b) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod, pow_mod_period_smul]

@[to_additive (attr := simp)]
/-
**MulAction.zpow_smul_mod_minimalPeriod** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type v} {G : Type u} [inst : Group G] [inst_1 : MulAction G α] (a :
 G) (b : α) (n : ℤ),   a ^ (n % ↑(Function.minimalPeriod (fun x => a • x) b)) • 
b = a ^ n • b
参数：a : G；b : α；n : ℤ；n % ↑(Function.minimalPeriod (fun x => a • x) b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.period_eq_minimalPeriod`：∀ {α : Type v} {M : Type u} [inst : M
onoid M] [inst_1 : MulAction M α] {m : M} {a : α},   MulAction.period m a = Func
tion.minimalPeriod (fun…
· 使用定理 `MulAction.zpow_mod_period_smul`：∀ {α : Type v} {G : Type u} [inst : Grou
p G] [inst_1 : MulAction G α] (j : ℤ) {g : G} {a : α},   g ^ (j % ↑(MulAction.pe
riod g a)) • a = g ^…
-/
theorem zpow_smul_mod_minimalPeriod (n : ℤ) :
    a ^ (n % (minimalPeriod (a • ·) b : ℤ)) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod, zpow_mod_period_smul]

end MulAction

