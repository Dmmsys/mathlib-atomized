/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Aesop
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Monotone.Basic

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/

public section

open Function

open Function (Commute)

namespace Monotone

variable {α : Type*} [Preorder α] {f : α → α} {x y : ℕ → α}

/-!
### Comparison of two sequences

If $f$ is a monotone function, then $∀ k, x_{k+1} ≤ f(x_k)$ implies that $x_k$ grows slower than
$f^k(x_0)$, and similarly for the reversed inequalities. If $x_k$ and $y_k$ are two sequences such
that $x_{k+1} ≤ f(x_k)$ and $y_{k+1} ≥ f(y_k)$ for all $k < n$, then $x_0 ≤ y_0$ implies
$x_n ≤ y_n$, see `Monotone.seq_le_seq`.

If some of the inequalities in this lemma are strict, then we have $x_n < y_n$. The rest of the
lemmas in this section formalize this fact for different inequalities made strict.
-/


@[to_dual self (reorder := x y, hx hy)]
/-
**Monotone.seq_le_seq** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：seq_le_seq (hf : Monotone f) (n : Nat) (h₀ : x 0 <= y 0) (hx : forall k < 
n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) <= y (k + 1)) : x n <= y n
参数：hf : Monotone f；n : Nat；h₀ : x 0 <= y 0；hx : forall k < n, x (k + 1) <= f (x 
k)；hy : forall k < n, f (y k) <= y (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
### Comparison of two sequences

If $f$ is a monotone function, then $∀ k, x_{k+1} ≤ f(x_k)$ implies that $x_k$ g
rows slower than
$f^k(x_0)$, and similarly for the reversed inequalities. If $x_k$ and $y_k$ are 
two sequences such
that $x_{k+1} ≤ f(x_k)$ and $y_{k+1} ≥ f(y_k)$ for all $k < n$, then $x_0 ≤ y_0$
 implies
$x_n ≤ y_n$, see `Monotone.seq_le_seq`.

If some of the inequalities in this lemma are strict, then we have $x_n < y_n$. 
The rest of the
lemmas in this section formalize this fact for different inequalities made stric
t.
-/
theorem seq_le_seq (hf : Monotone f) (n : ℕ) (h₀ : x 0 ≤ y 0) (hx : ∀ k < n, x (k + 1) ≤ f (x k))
    (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n ≤ y n := by
  induction n with
  | zero => exact h₀
  | succ n ihn =>
    refine (hx _ n.lt_succ_self).trans ((hf <| ihn ?_ ?_).trans (hy _ n.lt_succ_self))
    · exact fun k hk => hx _ (hk.trans n.lt_succ_self)
    · exact fun k hk => hy _ (hk.trans n.lt_succ_self)
/-
**Monotone.seq_pos_lt_seq_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：seq_pos_lt_seq_of_lt_of_le (hf : Monotone f) {n : Nat} (hn : 0 < n) (h₀ : 
x 0 <= y 0) (hx : forall k < n, x (k + 1) < f (x k)) (hy : forall k < n, f (y k)
 <= y (k + 1)) : x n < y n
参数：hf : Monotone f；hn : 0 < n；h₀ : x 0 <= y 0；hx : forall k < n, x (k + 1) < f (
x k)；hy : forall k < n, f (y k) <= y (k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem seq_pos_lt_seq_of_lt_of_le (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  induction n with
  | zero => exact hn.false.elim
  | succ n ihn =>
  suffices x n ≤ y n from (hx n n.lt_succ_self).trans_le ((hf this).trans <| hy n n.lt_succ_self)
  cases n with
  | zero => exact h₀
  | succ n =>
    refine (ihn n.zero_lt_succ (fun k hk => hx _ ?_) fun k hk => hy _ ?_).le <;>
    exact hk.trans n.succ.lt_succ_self
/-
**Monotone.seq_pos_lt_seq_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：seq_pos_lt_seq_of_le_of_lt (hf : Monotone f) {n : Nat} (hn : 0 < n) (h₀ : 
x 0 <= y 0) (hx : forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k
) < y (k + 1)) : x n < y n
参数：hf : Monotone f；hn : 0 < n；h₀ : x 0 <= y 0；hx : forall k < n, x (k + 1) <= f 
(x k)；hy : forall k < n, f (y k) < y (k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_pos_lt_seq_of_lt_of_le`：seq_pos_lt_seq_of_lt_of_le (hf : Mo
notone f) {n : Nat} (hn : 0 < n) (h₀ : x 0 <= y 0) (hx : forall k < n, x (k + 1)
 < f (x k)) (hy : forall …
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem seq_pos_lt_seq_of_le_of_lt (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_pos_lt_seq_of_lt_of_le hn h₀ hy hx
/-
**Monotone.seq_lt_seq_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：seq_lt_seq_of_lt_of_le (hf : Monotone f) (n : Nat) (h₀ : x 0 < y 0) (hx : 
forall k < n, x (k + 1) < f (x k)) (hy : forall k < n, f (y k) <= y (k + 1)) : x
 n < y n
参数：hf : Monotone f；n : Nat；h₀ : x 0 < y 0；hx : forall k < n, x (k + 1) < f (x k)
；hy : forall k < n, f (y k) <= y (k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.seq_pos_lt_seq_of_lt_of_le`：seq_pos_lt_seq_of_lt_of_le (hf : Mo
notone f) {n : Nat} (hn : 0 < n) (h₀ : x 0 <= y 0) (hx : forall k < n, x (k + 1)
 < f (x k)) (hy : forall …
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem seq_lt_seq_of_lt_of_le (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  cases n
  exacts [h₀, hf.seq_pos_lt_seq_of_lt_of_le (Nat.zero_lt_succ _) h₀.le hx hy]
/-
**Monotone.seq_lt_seq_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：seq_lt_seq_of_le_of_lt (hf : Monotone f) (n : Nat) (h₀ : x 0 < y 0) (hx : 
forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) < y (k + 1)) : x
 n < y n
参数：hf : Monotone f；n : Nat；h₀ : x 0 < y 0；hx : forall k < n, x (k + 1) <= f (x k
)；hy : forall k < n, f (y k) < y (k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_lt_seq_of_lt_of_le`：seq_lt_seq_of_lt_of_le (hf : Monotone f
) (n : Nat) (h₀ : x 0 < y 0) (hx : forall k < n, x (k + 1) < f (x k)) (hy : fora
ll k < n, f (y k) <= …
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem seq_lt_seq_of_le_of_lt (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_lt_seq_of_lt_of_le n h₀ hy hx

/-!
### Iterates of two functions

In this section we compare the iterates of a monotone function `f : α → α` to iterates of any
function `g : β → β`. If `h : β → α` satisfies `h ∘ g ≤ f ∘ h`, then `h (g^[n] x)` grows slower
than `f^[n] (h x)`, and similarly for the reversed inequality.

Then we specialize these two lemmas to the case `β = α`, `h = id`.
-/


variable {β : Type*} {g : β → β} {h : β → α}

open Function

@[to_dual iterate_comp_le_of_le]
/-
**Monotone.le_iterate_comp_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：le_iterate_comp_of_le (hf : Monotone f) (H : h ∘ g <= f ∘ h) (n : Nat) : h
 ∘ g^[n] <= f^[n] ∘ h
参数：hf : Monotone f；H : h ∘ g <= f ∘ h；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_le_seq`：seq_le_seq (hf : Monotone f) (n : Nat) (h₀ : x 0 <=
 y 0) (hx : forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) <= y
 (k + 1))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem le_iterate_comp_of_le (hf : Monotone f) (H : h ∘ g ≤ f ∘ h) (n : ℕ) :
    h ∘ g^[n] ≤ f^[n] ∘ h := fun x => by
  apply hf.seq_le_seq n <;>
    aesop (add simp [iterate_succ']) (erase simp [iterate_succ])

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
@[to_dual le_iterate_of_le /-- If `f ≤ g` and `g` is monotone, then `f^[n] ≤ g^[n]`. -/]
/-
**Monotone.iterate_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：iterate_le_of_le {g : α -> α} (hf : Monotone f) (h : f <= g) (n : Nat) : f
^[n] <= g^[n]
参数：hf : Monotone f；h : f <= g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.iterate_comp_le_of_le`：∀ {α : Type u_1} [inst : Preorder α] {f 
: α → α} {β : Type u_2} {g : β → β} {h : β → α},   Monotone f → f ∘ h ≤ h ∘ g → 
∀ (n : ℕ), f^[n] ∘ h…

--- 原说明 ---
If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`.
-/
theorem iterate_le_of_le {g : α → α} (hf : Monotone f) (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  hf.iterate_comp_le_of_le h n

end Monotone

/-!
### Comparison of iterations and the identity function

If $f(x) ≤ x$ for all $x$ (we express this as `f ≤ id` in the code), then the same is true for
any iterate of $f$, and similarly for the reversed inequality.
-/


namespace Function

section Preorder

variable {α : Type*} [Preorder α] {f : α → α}

/-- If $x ≤ f x$ for all $x$ (we write this as `id ≤ f`), then the same is true for any iterate
`f^[n]` of `f`. -/
@[to_dual iterate_le_id_of_le_id]
/-
**Function.id_le_iterate_of_id_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：id_le_iterate_of_id_le (h : id <= f) (n : Nat) : id <= f^[n]
参数：h : id <= f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
· 使用定理 `Monotone.iterate_le_of_le`：iterate_le_of_le {g : α -> α} (hf : Monotone 
f) (h : f <= g) (n : Nat) : f^[n] <= g^[n]
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)

--- 原说明 ---
If $x ≤ f x$ for all $x$ (we write this as `id ≤ f`), then the same is true for 
any iterate
`f^[n]` of `f`.
-/
theorem id_le_iterate_of_id_le (h : id ≤ f) (n : ℕ) : id ≤ f^[n] := by
  simpa only [iterate_id] using monotone_id.iterate_le_of_le h n
/-
**Function.monotone_iterate_of_id_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：monotone_iterate_of_id_le (h : id <= f) : Monotone fun m => f^[m]
参数：h : id <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem monotone_iterate_of_id_le (h : id ≤ f) : Monotone fun m => f^[m] :=
  monotone_nat_of_le_succ fun n x => by
    rw [iterate_succ_apply']
    exact h _
/-
**Function.antitone_iterate_of_le_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：antitone_iterate_of_le_id (h : f <= id) : Antitone fun m => f^[m]
参数：h : f <= id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.monotone_iterate_of_id_le`：monotone_iterate_of_id_le (h : id <=
 f) : Monotone fun m => f^[m]
-/
theorem antitone_iterate_of_le_id (h : f ≤ id) : Antitone fun m => f^[m] := fun m n hmn =>
  @monotone_iterate_of_id_le αᵒᵈ _ f h m n hmn

end Preorder

/-!
### Iterates of commuting functions

If `f` and `g` are monotone and commute, then `f x ≤ g x` implies `f^[n] x ≤ g^[n] x`, see
`Function.Commute.iterate_le_of_map_le`. We also prove two strict inequality versions of this lemma,
as well as `iff` versions.
-/


namespace Commute

section Preorder

variable {α : Type*} [Preorder α] {f g : α → α}

/-
**Function.Commute.iterate_le_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Function.Comm
ute`。
形式化陈述：iterate_le_of_map_le (h : Commute f g) (hf : Monotone f) (hg : Monotone g)
 {x} (hx : f x <= g x) (n : Nat) : f^[n] x <= g^[n] x
参数：h : Commute f g；hf : Monotone f；hg : Monotone g；hx : f x <= g x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_le_seq`：seq_le_seq (hf : Monotone f) (n : Nat) (h₀ : x 0 <=
 y 0) (hx : forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) <= y
 (k + 1))…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Monotone.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Monoto
ne f → ∀ (n : ℕ), Monotone f^[n]
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iterate_le_of_map_le (h : Commute f g) (hf : Monotone f) (hg : Monotone g) {x}
    (hx : f x ≤ g x) (n : ℕ) : f^[n] x ≤ g^[n] x := by
  apply hf.seq_le_seq n
  · rfl
  · intros; rw [iterate_succ_apply']
  · simp [h.iterate_right _ _, hg.iterate _ hx]
/-
**Function.Commute.iterate_pos_lt_of_map_lt** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Commute`。
形式化陈述：iterate_pos_lt_of_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictM
ono g) {x} (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x
参数：h : Commute f g；hf : Monotone f；hg : StrictMono g；hx : f x < g x；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_pos_lt_seq_of_le_of_lt`：seq_pos_lt_seq_of_le_of_lt (hf : Mo
notone f) {n : Nat} (hn : 0 < n) (h₀ : x 0 <= y 0) (hx : forall k < n, x (k + 1)
 <= f (x k)) (hy : forall…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `StrictMono.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Stri
ctMono f → ∀ (n : ℕ), StrictMono f^[n]
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem iterate_pos_lt_of_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x := by
  apply hf.seq_pos_lt_seq_of_le_of_lt hn
  · rfl
  · intros; rw [iterate_succ_apply']
  · simp [h.iterate_right _ _, hg.iterate _ hx]
/-
**Function.Commute.iterate_pos_lt_of_map_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Commute`。
形式化陈述：iterate_pos_lt_of_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Mono
tone g) {x} (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x
参数：h : Commute f g；hf : StrictMono f；hg : Monotone g；hx : f x < g x；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_pos_lt_of_map_lt`：iterate_pos_lt_of_map_lt (h :
 Commute f g) (hf : Monotone f) (hg : StrictMono g) {x} (hx : f x < g x) {n} (hn
 : 0 < n) : f^[n] x < g^[n] x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem iterate_pos_lt_of_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x :=
  @iterate_pos_lt_of_map_lt αᵒᵈ _ g f h.symm hg.dual hf.dual x hx n hn

end Preorder

variable {α : Type*} [LinearOrder α] {f g : α → α}

/-
**Function.Commute.iterate_pos_lt_iff_map_lt** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Commute`。
形式化陈述：iterate_pos_lt_iff_map_lt (h : Commute f g) (hf : Monotone f) (hg : Strict
Mono g) {x n} (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x
参数：h : Commute f g；hf : Monotone f；hg : StrictMono g；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Commute.iterate_eq_of_map_eq`：iterate_eq_of_map_eq (h : Commute
 f g) (n : Nat) {x} (hx : f x = g x) : f^[n] x = g^[n] x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `Function.Commute.iterate_pos_lt_of_map_lt'`：iterate_pos_lt_of_map_lt' (h
 : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x} (hx : f x < g x) {n} (
hn : 0 < n) : f^[n] x < g^[n] x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
-/
theorem iterate_pos_lt_iff_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x := by
  rcases lt_trichotomy (f x) (g x) with (H | H | H)
  · simp only [*, iterate_pos_lt_of_map_lt]
  · simp only [*, h.iterate_eq_of_map_eq, lt_irrefl]
  · simp only [lt_asymm H, lt_asymm (h.symm.iterate_pos_lt_of_map_lt' hg hf H hn)]
/-
**Function.Commute.iterate_pos_lt_iff_map_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Commute`。
形式化陈述：iterate_pos_lt_iff_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Mon
otone g) {x n} (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x
参数：h : Commute f g；hf : StrictMono f；hg : Monotone g；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_pos_lt_iff_map_lt`：iterate_pos_lt_iff_map_lt (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x < g^[n] x ↔ f x < g x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem iterate_pos_lt_iff_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x :=
  @iterate_pos_lt_iff_map_lt αᵒᵈ _ _ _ h.symm hg.dual hf.dual x n hn
/-
**Function.Commute.iterate_pos_le_iff_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Commute`。
形式化陈述：iterate_pos_le_iff_map_le (h : Commute f g) (hf : Monotone f) (hg : Strict
Mono g) {x n} (hn : 0 < n) : f^[n] x <= g^[n] x ↔ f x <= g x
参数：h : Commute f g；hf : Monotone f；hg : StrictMono g；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.Commute.iterate_pos_lt_iff_map_lt'`：iterate_pos_lt_iff_map_lt' 
(h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n} (hn : 0 < n) : f^[
n] x < g^[n] x ↔ f x < g x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
-/
theorem iterate_pos_le_iff_map_le (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt' hg hf hn)
/-
**Function.Commute.iterate_pos_le_iff_map_le'** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Commute`。
形式化陈述：iterate_pos_le_iff_map_le' (h : Commute f g) (hf : StrictMono f) (hg : Mon
otone g) {x n} (hn : 0 < n) : f^[n] x <= g^[n] x ↔ f x <= g x
参数：h : Commute f g；hf : StrictMono f；hg : Monotone g；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Function.Commute.iterate_pos_lt_iff_map_lt`：iterate_pos_lt_iff_map_lt (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x < g^[n] x ↔ f x < g x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
-/
theorem iterate_pos_le_iff_map_le' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt hg hf hn)
/-
**Function.Commute.iterate_pos_eq_iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Commute`。
形式化陈述：iterate_pos_eq_iff_map_eq (h : Commute f g) (hf : Monotone f) (hg : Strict
Mono g) {x n} (hn : 0 < n) : f^[n] x = g^[n] x ↔ f x = g x
参数：h : Commute f g；hf : Monotone f；hg : StrictMono g；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Commute.iterate_pos_le_iff_map_le`：iterate_pos_le_iff_map_le (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x <= g^[n] x ↔ f x <= g x
· 使用定理 `Function.Commute.iterate_pos_le_iff_map_le'`：iterate_pos_le_iff_map_le' 
(h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n} (hn : 0 < n) : f^[
n] x <= g^[n] x ↔ f x <= g x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iterate_pos_eq_iff_map_eq (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x = g^[n] x ↔ f x = g x := by
  simp only [le_antisymm_iff, h.iterate_pos_le_iff_map_le hf hg hn,
    h.symm.iterate_pos_le_iff_map_le' hg hf hn]

end Commute

end Function

namespace Monotone

variable {α : Type*} [Preorder α] {f : α → α} {x : α}

/-- If `f` is a monotone map and `x ≤ f x` at some point `x`, then the iterates `f^[n] x` form
a monotone sequence. -/
/-
**Monotone.monotone_iterate_of_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：monotone_iterate_of_le_map (hf : Monotone f) (hx : x <= f x) : Monotone fu
n n => f^[n] x
参数：hf : Monotone f；hx : x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Monotone.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Monoto
ne f → ∀ (n : ℕ), Monotone f^[n]

--- 原说明 ---
If `f` is a monotone map and `x ≤ f x` at some point `x`, then the iterates `f^[
n] x` form
a monotone sequence.
-/
theorem monotone_iterate_of_le_map (hf : Monotone f) (hx : x ≤ f x) : Monotone fun n => f^[n] x :=
  monotone_nat_of_le_succ fun n => by
    rw [iterate_succ_apply]
    exact hf.iterate n hx

/-- If `f` is a monotone map and `f x ≤ x` at some point `x`, then the iterates `f^[n] x` form
an antitone sequence. -/
/-
**Monotone.antitone_iterate_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：antitone_iterate_of_map_le (hf : Monotone f) (hx : f x <= x) : Antitone fu
n n => f^[n] x
参数：hf : Monotone f；hx : f x <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.monotone_iterate_of_le_map`：monotone_iterate_of_le_map (hf : Mo
notone f) (hx : x <= f x) : Monotone fun n => f^[n] x
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
If `f` is a monotone map and `f x ≤ x` at some point `x`, then the iterates `f^[
n] x` form
an antitone sequence.
-/
theorem antitone_iterate_of_map_le (hf : Monotone f) (hx : f x ≤ x) : Antitone fun n => f^[n] x :=
  hf.dual.monotone_iterate_of_le_map hx

end Monotone

namespace StrictMono

variable {α : Type*} [Preorder α] {f : α → α} {x : α}

/-- If `f` is a strictly monotone map and `x < f x` at some point `x`, then the iterates `f^[n] x`
form a strictly monotone sequence. -/
/-
**StrictMono.strictMono_iterate_of_lt_map** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`
。
形式化陈述：strictMono_iterate_of_lt_map (hf : StrictMono f) (hx : x < f x) : StrictMo
no fun n => f^[n] x
参数：hf : StrictMono f；hx : x < f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `StrictMono.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Stri
ctMono f → ∀ (n : ℕ), StrictMono f^[n]

--- 原说明 ---
If `f` is a strictly monotone map and `x < f x` at some point `x`, then the iter
ates `f^[n] x`
form a strictly monotone sequence.
-/
theorem strictMono_iterate_of_lt_map (hf : StrictMono f) (hx : x < f x) :
    StrictMono fun n => f^[n] x :=
  strictMono_nat_of_lt_succ fun n => by
    rw [iterate_succ_apply]
    exact hf.iterate n hx

/-- If `f` is a strictly antitone map and `f x < x` at some point `x`, then the iterates `f^[n] x`
form a strictly antitone sequence. -/
/-
**StrictMono.strictAnti_iterate_of_map_lt** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`
。
形式化陈述：strictAnti_iterate_of_map_lt (hf : StrictMono f) (hx : f x < x) : StrictAn
ti fun n => f^[n] x
参数：hf : StrictMono f；hx : f x < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.strictMono_iterate_of_lt_map`：strictMono_iterate_of_lt_map (h
f : StrictMono f) (hx : x < f x) : StrictMono fun n => f^[n] x
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…

--- 原说明 ---
If `f` is a strictly antitone map and `f x < x` at some point `x`, then the iter
ates `f^[n] x`
form a strictly antitone sequence.
-/
theorem strictAnti_iterate_of_map_lt (hf : StrictMono f) (hx : f x < x) :
    StrictAnti fun n => f^[n] x :=
  hf.dual.strictMono_iterate_of_lt_map hx

end StrictMono

