/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Birkhoff sums

In this file we define `birkhoffSum f g n x` to be the sum `∑ k ∈ Finset.range n, g (f^[k] x)`.
This sum (more precisely, the corresponding average `n⁻¹ • birkhoffSum f g n x`)
appears in various ergodic theorems
saying that these averages converge to the "space average" `⨍ x, g x ∂μ` in some sense.

See also `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`.
-/

@[expose] public section

open Finset Function

section AddCommMonoid

variable {α M : Type*} [AddCommMonoid M]

/-- The sum of values of `g` on the first `n` points of the orbit of `x` under `f`. -/
/-
**birkhoffSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：birkhoffSum (f : α -> α) (g : α -> M) (n : Nat) (x : α) : M
参数：f : α -> α；g : α -> M；n : Nat；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of values of `g` on the first `n` points of the orbit of `x` under `f`.
-/
def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)
/-
**birkhoffSum_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_zero (f : α -> α) (g : α -> M) (x : α) : birkhoffSum f g 0 x =
 0
参数：f : α -> α；g : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_zero`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f : ℕ 
→ M), ∑ k ∈ Finset.range 0, f k = 0
-/
theorem birkhoffSum_zero (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 0 x = 0 :=
  sum_range_zero _

@[simp]
/-
**birkhoffSum_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_zero' (f : α -> α) (g : α -> M) : birkhoffSum f g 0 = 0
参数：f : α -> α；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `birkhoffSum_zero`：birkhoffSum_zero (f : α -> α) (g : α -> M) (x : α) : b
irkhoffSum f g 0 x = 0
-/
theorem birkhoffSum_zero' (f : α → α) (g : α → M) : birkhoffSum f g 0 = 0 :=
  funext <| birkhoffSum_zero _ _
/-
**birkhoffSum_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_one (f : α -> α) (g : α -> M) (x : α) : birkhoffSum f g 1 x = 
g x
参数：f : α -> α；g : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
-/
theorem birkhoffSum_one (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 1 x = g x :=
  sum_range_one _

@[simp]
/-
**birkhoffSum_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_one' (f : α -> α) (g : α -> M) : birkhoffSum f g 1 = g
参数：f : α -> α；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `birkhoffSum_one`：birkhoffSum_one (f : α -> α) (g : α -> M) (x : α) : bir
khoffSum f g 1 x = g x
-/
theorem birkhoffSum_one' (f : α → α) (g : α → M) : birkhoffSum f g 1 = g :=
  funext <| birkhoffSum_one f g
/-
**birkhoffSum_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_succ (f : α -> α) (g : α -> M) (n : Nat) (x : α) : birkhoffSum
 f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x)
参数：f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
theorem birkhoffSum_succ (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x) :=
  sum_range_succ _ _
/-
**birkhoffSum_succ'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_succ' (f : α -> α) (g : α -> M) (n : Nat) (x : α) : birkhoffSu
m f g (n + 1) x = g x + birkhoffSum f g n (f x)
参数：f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem birkhoffSum_succ' (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffSum f g (n + 1) x = g x + birkhoffSum f g n (f x) :=
  (sum_range_succ' _ _).trans (add_comm _ _)
/-
**birkhoffSum_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_add (f : α -> α) (g : α -> M) (m n : Nat) (x : α) : birkhoffSu
m f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x)
参数：f : α -> α；g : α -> M；m n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M) (n m : ℕ),   ∑ x ∈ Finset.range (n + m), f x = ∑ x ∈ Finset.range n, f x + ∑
 x ∈ Finse…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem birkhoffSum_add (f : α → α) (g : α → M) (m n : ℕ) (x : α) :
    birkhoffSum f g (m + n) x = birkhoffSum f g m x + birkhoffSum f g n (f^[m] x) := by
  simp_rw [birkhoffSum, sum_range_add, add_comm m, iterate_add_apply]
/-
**birkhoffSum_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_add' (f : α -> α) (g g' : α -> M) (n : Nat) (x : α) : birkhoff
Sum f (g + g') n x = birkhoffSum f g n x + birkhoffSum f g' n x
参数：f : α -> α；g g' : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
-/
theorem birkhoffSum_add' (f : α → α) (g g' : α → M) (n : ℕ) (x : α) :
    birkhoffSum f (g + g') n x = birkhoffSum f g n x + birkhoffSum f g' n x := by
  simpa [birkhoffSum] using sum_add_distrib
/-
**Function.IsFixedPt.birkhoffSum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.IsFixedPt.birkhoffSum_eq {f : α -> α} {x : α} (h : IsFixedPt f x)
 (g : α -> M) (n : Nat) : birkhoffSum f g n x = n • g x
参数：h : IsFixedPt f x；g : α -> M；n : Nat。
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
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Function.IsFixedPt.birkhoffSum_eq {f : α → α} {x : α} (h : IsFixedPt f x) (g : α → M)
    (n : ℕ) : birkhoffSum f g n x = n • g x := by
  simp [birkhoffSum, (h.iterate _).eq]
/-
**map_birkhoffSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoid
HomClass F M N] (g' : F) (f : α -> α) (g : α -> M) (n : Nat) (x : α) : g' (birkh
offSum f g n x) = birkhoffSum f (g' ∘ g) n x
参数：g' : F；f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
-/
theorem map_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffSum f g n x) = birkhoffSum f (g' ∘ g) n x :=
  map_sum g' _ _

/-- If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`), then the Birkhoff sum
of `φ` over `f` for `n` iterations is equal to `n • φ`. -/
/-
**birkhoffSum_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_of_comp_eq {f : α -> α} {φ : α -> M} (h : φ ∘ f = φ) (n : Nat)
 : birkhoffSum f φ n = n • φ
参数：h : φ ∘ f = φ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_invariant`：iterate_invariant {g : α -> β} (h : g ∘ f = 
g) (n : Nat) : g ∘ f^[n] = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a function `φ` is invariant under a function `f` (i.e., `φ ∘ f = φ`), then th
e Birkhoff sum
of `φ` over `f` for `n` iterations is equal to `n • φ`.
-/
theorem birkhoffSum_of_comp_eq {f : α → α} {φ : α → M} (h : φ ∘ f = φ) (n : ℕ) :
    birkhoffSum f φ n = n • φ := by
  funext x
  suffices ∀ k, φ (f^[k] x) = φ x by simp [birkhoffSum, this]
  intro k
  exact congrFun (iterate_invariant h k) x

end AddCommMonoid

section AddCommGroup

variable {α G : Type*} [AddCommGroup G]

/-
**birkhoffSum_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_neg (f : α -> α) (g : α -> G) (n : Nat) (x : α) : birkhoffSum 
f (-g) n x = -birkhoffSum f g n x
参数：f : α -> α；g : α -> G；n : Nat；x : α。
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
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem birkhoffSum_neg (f : α → α) (g : α → G) (n : ℕ) (x : α) :
    birkhoffSum f (-g) n x = -birkhoffSum f g n x := by
  simp [birkhoffSum]
/-
**birkhoffSum_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_sub (f : α -> α) (g g' : α -> G) (n : Nat) (x : α) : birkhoffS
um f (g - g') n x = birkhoffSum f g n x - birkhoffSum f g' n x
参数：f : α -> α；g g' : α -> G；n : Nat；x : α。
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
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem birkhoffSum_sub (f : α → α) (g g' : α → G) (n : ℕ) (x : α) :
    birkhoffSum f (g - g') n x = birkhoffSum f g n x - birkhoffSum f g' n x := by
  simp [birkhoffSum]

/-- Birkhoff sum is "almost invariant" under `f`:
the difference between `birkhoffSum f g n (f x)` and `birkhoffSum f g n x`
is equal to `g (f^[n] x) - g x`. -/
/-
**birkhoffSum_apply_sub_birkhoffSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffSum_apply_sub_birkhoffSum (f : α -> α) (g : α -> G) (n : Nat) (x :
 α) : birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x
参数：f : α -> α；g : α -> G；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `birkhoffSum_succ`：birkhoffSum_succ (f : α -> α) (g : α -> M) (n : Nat) (
x : α) : birkhoffSum f g (n + 1) x = birkhoffSum f g n x + g (f^[n] x)
· 使用定理 `birkhoffSum_succ'`：birkhoffSum_succ' (f : α -> α) (g : α -> M) (n : Nat)
 (x : α) : birkhoffSum f g (n + 1) x = g x + birkhoffSum f g n (f x)
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c :
 α), a - b + c = c - b + a

--- 原说明 ---
Birkhoff sum is "almost invariant" under `f`:
the difference between `birkhoffSum f g n (f x)` and `birkhoffSum f g n x`
is equal to `g (f^[n] x) - g x`.
-/
theorem birkhoffSum_apply_sub_birkhoffSum (f : α → α) (g : α → G) (n : ℕ) (x : α) :
    birkhoffSum f g n (f x) - birkhoffSum f g n x = g (f^[n] x) - g x := by
  rw [← sub_eq_iff_eq_add.2 (birkhoffSum_succ f g n x),
    ← sub_eq_iff_eq_add.2 (birkhoffSum_succ' f g n x),
    ← sub_add, ← sub_add, sub_add_comm]

end AddCommGroup

