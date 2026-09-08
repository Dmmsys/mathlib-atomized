/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : R[X]` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.natDegree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

@[expose] public section


namespace Polynomial

open Finsupp Finset

open scoped Polynomial

section Semiring

variable {R : Type*} [Semiring R] {f : R[X]}

/-- If `i ≤ N`, then `revAtFun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `revAt`.
-/
/-
**Polynomial.revAtFun** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：revAtFun (N i : Nat) : Nat
参数：N i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i ≤ N`, then `revAtFun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `revAt`.
-/
def revAtFun (N i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i
/-
**Polynomial.revAtFun_invol** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAtFun_invol {N i : Nat} : revAtFun N (revAtFun N i) = i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem revAtFun_invol {N i : ℕ} : revAtFun N (revAtFun N i) = i := by
  unfold revAtFun
  grind
/-
**Polynomial.revAtFun_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAtFun_inj {N : Nat} : Function.Injective (revAtFun N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.revAtFun_invol`：revAtFun_invol {N i : Nat} : revAtFun N (revA
tFun N i) = i
-/
theorem revAtFun_inj {N : ℕ} : Function.Injective (revAtFun N) := by
  intro a b hab
  rw [← @revAtFun_invol N a, hab, revAtFun_invol]

/-- If `i ≤ N`, then `revAt N i` returns `N - i`, otherwise it returns `i`.
Essentially, this embedding is only used for `i ≤ N`.
The advantage of `revAt N i` over `N - i` is that `revAt` is an involution.
-/
/-
**Polynomial.revAt** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：revAt (N : Nat) : Function.Embedding Nat Nat where toFun i
参数：N : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.revAtFun_inj`：revAtFun_inj {N : Nat} : Function.Injective (re
vAtFun N)

--- 原说明 ---
If `i ≤ N`, then `revAt N i` returns `N - i`, otherwise it returns `i`.
Essentially, this embedding is only used for `i ≤ N`.
The advantage of `revAt N i` over `N - i` is that `revAt` is an involution.
-/
def revAt (N : ℕ) : Function.Embedding ℕ ℕ where
  toFun i := ite (i ≤ N) (N - i) i
  inj' := revAtFun_inj

/-- We prefer to use the bundled `revAt` over unbundled `revAtFun`. -/
@[simp]
/-
**Polynomial.revAtFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAtFun_eq (N i : Nat) : revAtFun N i = revAt N i
参数：N i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We prefer to use the bundled `revAt` over unbundled `revAtFun`.
-/
theorem revAtFun_eq (N i : ℕ) : revAtFun N i = revAt N i :=
  rfl

@[simp, grind =]
/-
**Polynomial.revAt_invol** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAt_invol {N i : Nat} : (revAt N) (revAt N i) = i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.revAtFun_invol`：revAtFun_invol {N i : Nat} : revAtFun N (revA
tFun N i) = i
-/
theorem revAt_invol {N i : ℕ} : (revAt N) (revAt N i) = i :=
  revAtFun_invol

@[simp]
/-
**Polynomial.revAt_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N - i
参数：H : i <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem revAt_le {N i : ℕ} (H : i ≤ N) : revAt N i = N - i :=
  if_pos H

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.revAt_eq_self_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：revAt_eq_self_of_lt {N i : Nat} (h : N < i) : revAt N i = i
参数：h : N < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_le`：∀ {a b : ℕ}, ¬a ≤ b ↔ b < a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma revAt_eq_self_of_lt {N i : ℕ} (h : N < i) : revAt N i = i := by simp [revAt, Nat.not_le.mpr h]
/-
**Polynomial.revAt_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAt_add {N O n o : Nat} (hn : n <= N) (ho : o <= O) : revAt (N + O) (n +
 o) = revAt N n + revAt O o
参数：hn : n <= N；ho : o <= O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le.dest`：∀ {n m : ℕ}, n ≤ m → ∃ k, n + k = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem revAt_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
    revAt (N + O) (n + o) = revAt N n + revAt O o := by
  rcases Nat.le.dest hn with ⟨n', rfl⟩
  rcases Nat.le.dest ho with ⟨o', rfl⟩
  repeat' rw [revAt_le (le_add_right rfl.le)]
  rw [add_assoc, add_left_comm n' o, ← add_assoc, revAt_le (le_add_right rfl.le)]
  repeat' rw [add_tsub_cancel_left]
/-
**Polynomial.revAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：revAt_zero (N : Nat) : revAt N 0 = N
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem revAt_zero (N : ℕ) : revAt N 0 = N := by simp

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (revAt N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`. -/
/-
**Polynomial.reflect** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u_1} → [inst : Semiring R] → ℕ → Polynomial R → Polynomial R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (revA
t N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ...
, 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree 
of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.
-/
noncomputable def reflect (N : ℕ) : R[X] → R[X]
  | ⟨f⟩ => ⟨.ofCoeff <| f.coeff.embDomain (revAt N)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.reflect_support** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_support (N : Nat) (f : R[X]) : (reflect N f).support = Finset.imag
e (revAt N) f.support
参数：N : Nat；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.support_ofFinsupp`：support_ofFinsupp (p) : support (⟨p⟩ : R[X
]) = p.coeff.support
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reflect_support (N : ℕ) (f : R[X]) :
    (reflect N f).support = Finset.image (revAt N) f.support := by cases f; ext1; simp [reflect]

@[simp, grind =]
/-
**Polynomial.coeff_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) : coeff (reflect N f) i = f.c
oeff (revAt N i)
参数：N : Nat；f : R[X]；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
-/
theorem coeff_reflect (N : ℕ) (f : R[X]) (i : ℕ) : coeff (reflect N f) i = f.coeff (revAt N i) := by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    f.coeff.embDomain (revAt N) i
      = f.coeff.embDomain (revAt N) (revAt N (revAt N i)) := by rw [revAt_invol]
    _ = f.coeff (revAt N i) := Finsupp.embDomain_apply_self _ _ _
/-
**Polynomial.reflect_reflect** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {N : ℕ} {p : Polynomial R}, Polynomia
l.reflect N (Polynomial.reflect N p) = p
参数：Polynomial.reflect N p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma reflect_reflect {N : ℕ} {p : R[X]} : (p.reflect N).reflect N = p := by ext; simp

@[simp]
/-
**Polynomial.reflect_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_zero {N : Nat} : reflect N (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reflect_zero {N : ℕ} : reflect N (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.reflect_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：reflect_eq_zero_iff {N : Nat} {f : R[X]} : reflect N (f : R[X]) = 0 ↔ f = 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma reflect_eq_zero_iff {N : ℕ} {f : R[X]} : reflect N (f : R[X]) = 0 ↔ f = 0 := by simp [reflect]

@[simp]
/-
**Polynomial.reflect_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_add (f g : R[X]) (N : Nat) : reflect N (f + g) = reflect N f + ref
lect N g
参数：f g : R[X]；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reflect_add (f g : R[X]) (N : ℕ) : reflect N (f + g) = reflect N f + reflect N g := by
  ext
  simp only [coeff_add, coeff_reflect]

@[simp]
/-
**Polynomial.reflect_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_C_mul (f : R[X]) (r : R) (N : Nat) : reflect N (C r * f) = C r * r
eflect N f
参数：f : R[X]；r : R；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reflect_C_mul (f : R[X]) (r : R) (N : ℕ) : reflect N (C r * f) = C r * reflect N f := by
  ext
  simp only [coeff_reflect, coeff_C_mul]
/-
**Polynomial.reflect_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_C_mul_X_pow (N n : Nat) {c : R} : reflect N (C c * X ^ n) = C c * 
X ^ revAt N n
参数：N n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
-/
theorem reflect_C_mul_X_pow (N n : ℕ) {c : R} : reflect N (C c * X ^ n) = C c * X ^ revAt N n := by
  ext
  grind

@[simp]
/-
**Polynomial.reflect_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_C (r : R) (N : Nat) : reflect N (C r) = C r * X ^ N
参数：r : R；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.reflect_C_mul_X_pow`：reflect_C_mul_X_pow (N n : Nat) {c : R} 
: reflect N (C c * X ^ n) = C c * X ^ revAt N n
· 使用定理 `Polynomial.revAt_zero`：revAt_zero (N : Nat) : revAt N 0 = N
-/
theorem reflect_C (r : R) (N : ℕ) : reflect N (C r) = C r * X ^ N := by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]

@[simp]
/-
**Polynomial.reflect_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_monomial (N n : Nat) : reflect N ((X : R[X]) ^ n) = X ^ revAt N n
参数：N n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.reflect_C_mul_X_pow`：reflect_C_mul_X_pow (N n : Nat) {c : R} 
: reflect N (C c * X ^ n) = C c * X ^ revAt N n
-/
theorem reflect_monomial (N n : ℕ) : reflect N ((X : R[X]) ^ n) = X ^ revAt N n := by
  rw [← one_mul (X ^ n), ← one_mul (X ^ revAt N n), ← C_1, reflect_C_mul_X_pow]
/-
**Polynomial.reflect_one_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], Polynomial.reflect 1 Polynomial.X = 
1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.reflect_monomial`：reflect_monomial (N n : Nat) : reflect N ((
X : R[X]) ^ n) = X ^ revAt N n
-/
@[simp] lemma reflect_one_X : reflect 1 (X : R[X]) = 1 := by
  simpa using reflect_monomial 1 1 (R := R)
/-
**Polynomial.reflect_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：reflect_map {S : Type*} [Semiring S] (f : R ->+* S) (p : R[X]) (n : Nat) :
 (p.map f).reflect n = (p.reflect n).map f
参数：f : R ->+* S；p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reflect_map {S : Type*} [Semiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).reflect n = (p.reflect n).map f := by
  ext; simp

@[simp]
/-
**Polynomial.reflect_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：reflect_one (n : Nat) : (1 : R[X]).reflect n = Polynomial.X ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Polynomial.reflect_C`：reflect_C (r : R) (N : Nat) : reflect N (C r) = C 
r * X ^ N
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma reflect_one (n : ℕ) : (1 : R[X]).reflect n = Polynomial.X ^ n := by
  rw [← C.map_one, reflect_C, map_one, one_mul]
/-
**Polynomial.reflect_mul_induction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_mul_induction (cf cg : Nat) (N O : Nat) (f g : R[X]) (Cf : #f.supp
ort <= cf.succ) (Cg : #g.support <= cg.succ) (Nf : f.natDegree <= N) (Og : g.nat
Degree <= O) : reflect (N + O) (f * g) = reflect N f * reflect O g
参数：cf cg : Nat；N O : Nat；f g : R[X]；Cf : #f.support <= cf.succ；Cg : #g.support <
= cg.succ；Nf : f.natDegree <= N；Og : g.natDegree <= O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_self`：C_mul_X_pow_eq_self (h : #p.support <= 1
) : C p.leadingCoeff * X ^ p.natDegree = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.reflect_C_mul`：reflect_C_mul (f : R[X]) (r : R) (N : Nat) : r
eflect N (C r * f) = C r * reflect N f
· 使用定理 `Polynomial.reflect_monomial`：reflect_monomial (N n : Nat) : reflect N ((
X : R[X]) ^ n) = X ^ revAt N n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.revAt_add`：revAt_add {N O n o : Nat} (hn : n <= N) (ho : o <=
 O) : revAt (N + O) (n + o) = revAt N n + revAt O o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.reflect_zero`：reflect_zero {N : Nat} : reflect N (0 : R[X]) =
 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.eraseLead_add_C_mul_X_pow`：eraseLead_add_C_mul_X_pow (f : R[X
]) : f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.reflect_add`：reflect_add (f g : R[X]) (N : Nat) : reflect N (
f + g) = reflect N f + reflect N g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.eraseLead_support_card_lt`：eraseLead_support_card_lt (h : f !
= 0) : #(eraseLead f).support < #f.support
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.eraseLead_natDegree_le_aux`：eraseLead_natDegree_le_aux : (era
seLead f).natDegree <= f.natDegree
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `Polynomial.card_support_C_mul_X_pow_le_one`：card_support_C_mul_X_pow_le_
one {c : R} {n : Nat} : #(support (C c * X ^ n)) <= 1
· 使用定理 `Polynomial.natDegree_C_mul_X_pow_le`：natDegree_C_mul_X_pow_le (a : R) (n
 : Nat) : natDegree (C a * X ^ n) <= n
（共 33 条，此处仅展示前 30 条）
-/
theorem reflect_mul_induction (cf cg : ℕ) (N O : ℕ) (f g : R[X]) (Cf : #f.support ≤ cf.succ)
    (Cg : #g.support ≤ cg.succ) (Nf : f.natDegree ≤ N) (Og : g.natDegree ≤ O) :
    reflect (N + O) (f * g) = reflect N f * reflect O g := by
  induction cf generalizing f with
  | zero =>
    induction cg generalizing g with
    | zero =>
      rw [← C_mul_X_pow_eq_self Cf, ← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), reflect_C_mul,
        reflect_monomial, add_comm, revAt_add Nf Og, mul_assoc, X_pow_mul, mul_assoc, ←
        pow_add (X : R[X]), add_comm]
    | succ cg hcg =>
      by_cases g0 : g = 0
      · rw [g0, reflect_zero, mul_zero, mul_zero, reflect_zero]
      rw [← eraseLead_add_C_mul_X_pow g, mul_add, reflect_add, reflect_add, mul_add, hcg, hcg] <;>
        try assumption
      · exact le_add_left card_support_C_mul_X_pow_le_one
      · exact le_trans (natDegree_C_mul_X_pow_le g.leadingCoeff g.natDegree) Og
      · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt g0) Cg)
      · exact le_trans eraseLead_natDegree_le_aux Og
  | succ cf hcf =>
    by_cases f0 : f = 0
    · rw [f0, reflect_zero, zero_mul, zero_mul, reflect_zero]
    rw [← eraseLead_add_C_mul_X_pow f, add_mul, reflect_add, reflect_add, add_mul, hcf, hcf] <;>
      try assumption
    · exact le_add_left card_support_C_mul_X_pow_le_one
    · exact le_trans (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree) Nf
    · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt f0) Cf)
    · exact le_trans eraseLead_natDegree_le_aux Nf

@[simp]
/-
**Polynomial.reflect_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_mul (f g : R[X]) {F G : Nat} (Ff : f.natDegree <= F) (Gg : g.natDe
gree <= G) : reflect (F + G) (f * g) = reflect F f * reflect G g
参数：f g : R[X]；Ff : f.natDegree <= F；Gg : g.natDegree <= G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.reflect_mul_induction`：reflect_mul_induction (cf cg : Nat) (N
 O : Nat) (f g : R[X]) (Cf : #f.support <= cf.succ) (Cg : #g.support <= cg.succ)
 (Nf : f.natDegree <= …
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem reflect_mul (f g : R[X]) {F G : ℕ} (Ff : f.natDegree ≤ F) (Gg : g.natDegree ≤ G) :
    reflect (F + G) (f * g) = reflect F f * reflect G g :=
  reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.natDegree_reflect_le** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_reflect_le {N : Nat} {p : R[X]} : (p.reflect N).natDegree <= max
 N p.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma natDegree_reflect_le {N : ℕ} {p : R[X]} :
    (p.reflect N).natDegree ≤ max N p.natDegree := by
  simp +contextual [-le_sup_iff, natDegree_le_iff_coeff_eq_zero,
    revAt, not_le_of_gt, coeff_eq_zero_of_natDegree_lt]

section Eval₂

variable {S : Type*} [CommSemiring S]

/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_reflect_mul_pow (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f := by
  refine
    induction_with_natDegree_le (fun f => eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f) _ ?_ ?_
      ?_ f hf
  · simp
  · intro n r _ hnN
    simp only [revAt_le hnN, reflect_C_mul_X_pow, eval₂_X_pow, eval₂_C, eval₂_mul]
    conv in x ^ N => rw [← Nat.sub_add_cancel hnN]
    rw [pow_add, ← mul_assoc, mul_assoc (i r), ← mul_pow, invOf_mul_self, one_pow, mul_one]
  · intros
    simp [*, add_mul]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_reflect_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟x) (reflect N f) = 0 ↔ eval₂ i x f = 0 := by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h, zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟x) _), ← one_pow N, ← mul_invOf_self x, mul_pow, ← mul_assoc, h,
      zero_mul]

end Eval₂

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, `reverse f = f (1/X) * X ^ f.natDegree`. -/
/-
**Polynomial.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：reverse (f : R[X]) : R[X]
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse of a polynomial f is the polynomial obtained by "reading f backwards
".
Even though this is not the actual definition, `reverse f = f (1/X) * X ^ f.natD
egree`.
-/
noncomputable def reverse (f : R[X]) : R[X] :=
  reflect f.natDegree f
/-
**Polynomial.coeff_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_reverse (f : R[X]) (n : Nat) : f.reverse.coeff n = f.coeff (revAt f.
natDegree n)
参数：f : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
-/
theorem coeff_reverse (f : R[X]) (n : ℕ) : f.reverse.coeff n = f.coeff (revAt f.natDegree n) := by
  rw [reverse, coeff_reflect]

@[simp]
/-
**Polynomial.coeff_zero_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_reverse (f : R[X]) : coeff (reverse f) 0 = leadingCoeff f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
-/
theorem coeff_zero_reverse (f : R[X]) : coeff (reverse f) 0 = leadingCoeff f := by
  rw [coeff_reverse, revAt_le zero_le, tsub_zero, leadingCoeff]

@[simp]
/-
**Polynomial.reverse_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_zero : reverse (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverse_zero : reverse (0 : R[X]) = 0 :=
  rfl

@[simp]
/-
**Polynomial.reverse_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_eq_zero : f.reverse = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reverse_eq_zero : f.reverse = 0 ↔ f = 0 := by simp [reverse]

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.reverse_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_natDegree_le (f : R[X]) : f.reverse.natDegree <= f.natDegree
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `Polynomial.revAtFun_inj`：revAtFun_inj {N : Nat} : Function.Injective (re
vAtFun N)
· 使用定理 `Polynomial.revAt.eq_1`：∀ (N : ℕ), Polynomial.revAt N = { toFun := fun i 
=> if i ≤ N then N - i else i, inj' := ⋯ }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
-/
theorem reverse_natDegree_le (f : R[X]) : f.reverse.natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse, revAt, Function.Embedding.coeFn_mk, if_neg (not_le_of_gt hn),
    coeff_eq_zero_of_natDegree_lt hn]
/-
**Polynomial.natDegree_eq_reverse_natDegree_add_natTrailingDegree** 是 Mathlib 中的
一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) : f.natDeg
ree = f.reverse.natDegree + f.natTrailingDegree
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.reverse_zero`：reverse_zero : reverse (0 : R[X]) = 0
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Polynomial.natTrailingDegree_zero`：natTrailingDegree_zero : natTrailingD
egree (0 : R[X]) = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用定理 `Polynomial.coeff_reflect`：coeff_reflect (N : Nat) (f : R[X]) (i : Nat) :
 coeff (reflect N f) i = f.coeff (revAt N i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Polynomial.natTrailingDegree_le_natDegree`：natTrailingDegree_le_natDegre
e (p : R[X]) : p.natTrailingDegree <= p.natDegree
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
· 使用定理 `le_tsub_iff_left`：le_tsub_iff_left (h : a <= c) : b <= c - a ↔ a + b <= 
c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Polynomial.reverse_natDegree_le`：reverse_natDegree_le (f : R[X]) : f.rev
erse.natDegree <= f.natDegree
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.reverse_eq_zero`：reverse_eq_zero : f.reverse = 0 ↔ f = 0
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
-/
theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) :
    f.natDegree = f.reverse.natDegree + f.natTrailingDegree := by
  by_cases hf : f = 0
  · rw [hf, reverse_zero, natDegree_zero, natTrailingDegree_zero]
  apply le_antisymm
  · refine tsub_le_iff_right.mp ?_
    apply le_natDegree_of_ne_zero
    rw [reverse, coeff_reflect, ← revAt_le f.natTrailingDegree_le_natDegree, revAt_invol]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hf
  · rw [← le_tsub_iff_left f.reverse_natDegree_le]
    apply natTrailingDegree_le_of_ne_zero
    have key := mt leadingCoeff_eq_zero.mp (mt reverse_eq_zero.mp hf)
    rwa [leadingCoeff, coeff_reverse, revAt_le f.reverse_natDegree_le] at key
/-
**Polynomial.reverse_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTr
ailingDegree
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_eq_reverse_natDegree_add_natTrailingDegree`：natDegr
ee_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) : f.natDegree = f.rever
se.natDegree + f.natTrailingDegree
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTrailingDegree := by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree, add_tsub_cancel_right]
/-
**Polynomial.reverse_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.reverse_natDegree`：reverse_natDegree (f : R[X]) : f.reverse.n
atDegree = f.natDegree - f.natTrailingDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Polynomial.natTrailingDegree_le_natDegree`：natTrailingDegree_le_natDegre
e (p : R[X]) : p.natTrailingDegree <= p.natDegree
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
-/
theorem reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff := by
  rw [leadingCoeff, reverse_natDegree, ← revAt_le f.natTrailingDegree_le_natDegree,
    coeff_reverse, revAt_invol, trailingCoeff]
/-
**Polynomial.natTrailingDegree_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natTrailingDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R}, p.natTrailingDegree = 0 ↔ p = 0 ∨ p.coeff 0 ≠ 0
· 使用定理 `Polynomial.reverse_eq_zero`：reverse_eq_zero : f.reverse = 0 ↔ f = 0
· 使用定理 `Polynomial.coeff_zero_reverse`：coeff_zero_reverse (f : R[X]) : coeff (re
verse f) 0 = leadingCoeff f
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
-/
theorem natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero, reverse_eq_zero, coeff_zero_reverse, leadingCoeff_ne_zero]
  exact eq_or_ne _ _
/-
**Polynomial.reverse_trailingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoef
f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Polynomial.natTrailingDegree_reverse`：natTrailingDegree_reverse (f : R[X
]) : f.reverse.natTrailingDegree = 0
· 使用定理 `Polynomial.coeff_zero_reverse`：coeff_zero_reverse (f : R[X]) : coeff (re
verse f) 0 = leadingCoeff f
-/
theorem reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoeff := by
  rw [trailingCoeff, natTrailingDegree_reverse, coeff_zero_reverse]
/-
**Polynomial.reverse_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff != 0) : rev
erse (f * g) = reverse f * reverse g
参数：fg : f.leadingCoeff * g.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.reflect_mul`：reflect_mul (f g : R[X]) {F G : Nat} (Ff : f.nat
Degree <= F) (Gg : g.natDegree <= G) : reflect (F + G) (f * g) = reflect F f * r
eflect G g
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff ≠ 0) :
    reverse (f * g) = reverse f * reverse g := by
  unfold reverse
  rw [natDegree_mul' fg, reflect_mul f g rfl.le rfl.le]

@[simp]
/-
**Polynomial.reverse_mul_of_domain** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_mul_of_domain {R : Type*} [Semiring R] [NoZeroDivisors R] (f g : R
[X]) : reverse (f * g) = reverse f * reverse g
参数：f g : R[X]。
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
· 使用定理 `Polynomial.reverse_zero`：reverse_zero : reverse (0 : R[X]) = 0
· 使用定理 `Polynomial.reverse_mul`：reverse_mul {f g : R[X]} (fg : f.leadingCoeff * 
g.leadingCoeff != 0) : reverse (f * g) = reverse f * reverse g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem reverse_mul_of_domain {R : Type*} [Semiring R] [NoZeroDivisors R] (f g : R[X]) :
    reverse (f * g) = reverse f * reverse g := by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]
/-
**Polynomial.trailingCoeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingCoeff_mul {R : Type*} [Semiring R] [NoZeroDivisors R] (p q : R[X])
 : (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.reverse_leadingCoeff`：reverse_leadingCoeff (f : R[X]) : f.rev
erse.leadingCoeff = f.trailingCoeff
· 使用定理 `Polynomial.reverse_mul_of_domain`：reverse_mul_of_domain {R : Type*} [Sem
iring R] [NoZeroDivisors R] (f g : R[X]) : reverse (f * g) = reverse f * reverse
 g
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
-/
theorem trailingCoeff_mul {R : Type*} [Semiring R] [NoZeroDivisors R] (p q : R[X]) :
    (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff := by
  rw [← reverse_leadingCoeff, reverse_mul_of_domain, leadingCoeff_mul, reverse_leadingCoeff,
    reverse_leadingCoeff]

@[simp]
/-
**Polynomial.coeff_one_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_one_reverse (f : R[X]) : coeff (reverse f) 1 = nextCoeff f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_reverse`：coeff_reverse (f : R[X]) (n : Nat) : f.reverse
.coeff n = f.coeff (revAt f.natDegree n)
· 使用定理 `Polynomial.nextCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R),   p.nextCoeff = if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 
1)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.revAtFun_inj`：revAtFun_inj {N : Nat} : Function.Injective (re
vAtFun N)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
-/
theorem coeff_one_reverse (f : R[X]) : coeff (reverse f) 1 = nextCoeff f := by
  rw [coeff_reverse, nextCoeff]
  split_ifs with hf
  · have : coeff f 1 = 0 := coeff_eq_zero_of_natDegree_lt (by simp only [hf, zero_lt_one])
    simp [*, revAt]
  · rw [revAt_le]
    exact Nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf)
/-
**Polynomial.reverse_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (t : R), (Polynomial.C t).reverse = P
olynomial.C t
参数：t : R；Polynomial.C t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Polynomial.reflect_C`：reflect_C (r : R) (N : Nat) : reflect N (C r) = C 
r * X ^ N
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma reverse_C (t : R) :
    reverse (C t) = C t := by
  simp [reverse]
/-
**Polynomial.reverse_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R), (p * Polynomial.X
).reverse = p.reverse
参数：p : Polynomial R；p * Polynomial.X。
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
· 使用定理 `Polynomial.reverse_mul_of_domain`：reverse_mul_of_domain {R : Type*} [Sem
iring R] [NoZeroDivisors R] (f g : R[X]) : reverse (f * g) = reverse f * reverse
 g
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_mul_X`：∀ {R : Type u} [inst : Semiring R] [Nontrivi
al R] {p : Polynomial R},   p ≠ 0 → (p * Polynomial.X).natDegree = p.natDegree +
 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.reflect_mul`：reflect_mul (f g : R[X]) {F G : Nat} (Ff : f.nat
Degree <= F) (Gg : g.natDegree <= G) : reflect (F + G) (f * g) = reflect F f * r
eflect G g
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Polynomial.reflect_one_X`：∀ {R : Type u_1} [inst : Semiring R], Polynomi
al.reflect 1 Polynomial.X = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] lemma reverse_mul_X (p : R[X]) : reverse (p * X) = reverse p := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]
/-
**Polynomial.reverse_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R), (Polynomial.X * p
).reverse = p.reverse
参数：p : Polynomial R；Polynomial.X * p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `Polynomial.reverse_mul_X`：∀ {R : Type u_1} [inst : Semiring R] (p : Poly
nomial R), (p * Polynomial.X).reverse = p.reverse
-/
@[simp] lemma reverse_X_mul (p : R[X]) : reverse (X * p) = reverse p := by
  rw [commute_X p, reverse_mul_X]
/-
**Polynomial.reverse_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R) (n : ℕ), (p * Poly
nomial.X ^ n).reverse = p.reverse
参数：p : Polynomial R；n : ℕ；p * Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.reverse_mul_X`：∀ {R : Type u_1} [inst : Semiring R] (p : Poly
nomial R), (p * Polynomial.X).reverse = p.reverse
-/
@[simp] lemma reverse_mul_X_pow (p : R[X]) (n : ℕ) : reverse (p * X ^ n) = reverse p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]
/-
**Polynomial.reverse_X_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R) (n : ℕ), (Polynomi
al.X ^ n * p).reverse = p.reverse
参数：p : Polynomial R；n : ℕ；Polynomial.X ^ n * p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.commute_X_pow`：commute_X_pow (p : R[X]) (n : Nat) : Commute (
X ^ n) p
· 使用定理 `Polynomial.reverse_mul_X_pow`：∀ {R : Type u_1} [inst : Semiring R] (p : 
Polynomial R) (n : ℕ), (p * Polynomial.X ^ n).reverse = p.reverse
-/
@[simp] lemma reverse_X_pow_mul (p : R[X]) (n : ℕ) : reverse (X ^ n * p) = reverse p := by
  rw [commute_X_pow p, reverse_mul_X_pow]
/-
**Polynomial.reverse_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R) (t : R),   (p + Po
lynomial.C t).reverse = p.reverse + Polynomial.C t * Polynomial.X ^ p.natDegree
参数：p : Polynomial R；t : R；p + Polynomial.C t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.reflect_add`：reflect_add (f g : R[X]) (N : Nat) : reflect N (
f + g) = reflect N f + reflect N g
· 使用定理 `Polynomial.reflect_C`：reflect_C (r : R) (N : Nat) : reflect N (C r) = C 
r * X ^ N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma reverse_add_C (p : R[X]) (t : R) :
    reverse (p + C t) = reverse p + C t * X ^ p.natDegree := by
  simp [reverse]
/-
**Polynomial.reverse_C_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (p : Polynomial R) (t : R),   (Polyno
mial.C t + p).reverse = Polynomial.C t * Polynomial.X ^ p.natDegree + p.reverse
参数：p : Polynomial R；t : R；Polynomial.C t + p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.reverse_add_C`：∀ {R : Type u_1} [inst : Semiring R] (p : Poly
nomial R) (t : R),   (p + Polynomial.C t).reverse = p.reverse + Polynomial.C t *
 Polynomial.X …
-/
@[simp] lemma reverse_C_add (p : R[X]) (t : R) :
    reverse (C t + p) = C t * X ^ p.natDegree + reverse p := by
  rw [add_comm, reverse_add_C, add_comm]

section Eval₂

variable {S : Type*} [CommSemiring S]

/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_reverse_mul_pow (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (reverse f) * x ^ f.natDegree = eval₂ i x f :=
  eval₂_reflect_mul_pow i _ _ f le_rfl

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_reverse_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (reverse f) = 0 ↔ eval₂ i x f = 0 :=
  eval₂_reflect_eq_zero_iff i x _ _ le_rfl

end Eval₂

end Semiring

section Ring

variable {R : Type*} [Ring R]

@[simp]
/-
**Polynomial.reflect_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_neg (f : R[X]) (N : Nat) : reflect N (-f) = -reflect N f
参数：f : R[X]；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.reflect_C_mul`：reflect_C_mul (f : R[X]) (r : R) (N : Nat) : r
eflect N (C r * f) = C r * reflect N f
-/
theorem reflect_neg (f : R[X]) (N : ℕ) : reflect N (-f) = -reflect N f := by
  rw [neg_eq_neg_one_mul, ← C_1, ← C_neg, reflect_C_mul, C_neg, C_1, ← neg_eq_neg_one_mul]

@[simp]
/-
**Polynomial.reflect_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reflect_sub (f g : R[X]) (N : Nat) : reflect N (f - g) = reflect N f - ref
lect N g
参数：f g : R[X]；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.reflect_add`：reflect_add (f g : R[X]) (N : Nat) : reflect N (
f + g) = reflect N f + reflect N g
· 使用定理 `Polynomial.reflect_neg`：reflect_neg (f : R[X]) (N : Nat) : reflect N (-f
) = -reflect N f
-/
theorem reflect_sub (f g : R[X]) (N : ℕ) : reflect N (f - g) = reflect N f - reflect N g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, reflect_add, reflect_neg]

@[simp]
/-
**Polynomial.reverse_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：reverse_neg (f : R[X]) : reverse (-f) = -reverse f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用定理 `Polynomial.reflect_neg`：reflect_neg (f : R[X]) (N : Nat) : reflect N (-f
) = -reflect N f
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
-/
theorem reverse_neg (f : R[X]) : reverse (-f) = -reverse f := by
  rw [reverse, reverse, reflect_neg, natDegree_neg]

end Ring

end Polynomial

