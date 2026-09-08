/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcdA x y` and `gcdB x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcdA x y + y * gcdB x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/

@[expose] public section

/-! ### Extended Euclidean algorithm -/


namespace Nat

/-- Helper function for the extended GCD algorithm (`Nat.xgcd`). -/
/-
**Nat.xgcdAux** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：xgcdAux : Nat -> Int -> Int -> Nat -> Int -> Int -> Nat × Int × Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for the extended GCD algorithm (`Nat.xgcd`).
-/
def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ :=
  Nat.strongRec fun n ih s t r' s' t' ↦ match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t

@[simp]
/-
**Nat.xgcd_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.xgcdAux.eq_1`：∀ (t : ℕ),   t.xgcdAux =     Nat.strongRec (motive := 
fun x => ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ)       (fun n ih s t r' s' t' =>         
match …
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
-/
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  rw [xgcdAux, Nat.strongRec_eq]
/-
**Nat.xgcdAux_rec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xgcdAux_rec {r s t r' s' t'} (h : 0 < r) : xgcdAux r s t r' s' t' = xgcdAu
x (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t
参数：h : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.xgcdAux.eq_1`：∀ (t : ℕ),   t.xgcdAux =     Nat.strongRec (motive := 
fun x => ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ)       (fun n ih s t r' s' t' =>         
match …
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem xgcdAux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rw [xgcdAux, Nat.strongRec_eq]
  rfl

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
/-
**Nat.xgcd** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：xgcd (x y : Nat) : Int × Int
参数：x y : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`.
-/
def xgcd (x y : ℕ) : ℤ × ℤ :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
/-
**Nat.gcdA** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：gcdA (x y : Nat) : Int
参数：x y : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `a` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdA (x y : ℕ) : ℤ :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
/-
**Nat.gcdB** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：gcdB (x y : Nat) : Int
参数：x y : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `b` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdB (x y : ℕ) : ℤ :=
  (xgcd x y).2

@[simp]
/-
**Nat.gcdA_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcdA_zero_left {s : Nat} : gcdA 0 s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcdA.eq_1`：∀ (x y : ℕ), x.gcdA y = (x.xgcd y).1
· 使用定理 `Nat.xgcd.eq_1`：∀ (x y : ℕ), x.xgcd y = (x.xgcdAux 1 0 y 0 1).2
· 使用定理 `Nat.xgcdAux.eq_1`：∀ (t : ℕ),   t.xgcdAux =     Nat.strongRec (motive := 
fun x => ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ)       (fun n ih s t r' s' t' =>         
match …
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
-/
theorem gcdA_zero_left {s : ℕ} : gcdA 0 s = 0 := by
  rw [gcdA, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/-
**Nat.gcdB_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcdB_zero_left {s : Nat} : gcdB 0 s = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcdB.eq_1`：∀ (x y : ℕ), x.gcdB y = (x.xgcd y).2
· 使用定理 `Nat.xgcd.eq_1`：∀ (x y : ℕ), x.xgcd y = (x.xgcdAux 1 0 y 0 1).2
· 使用定理 `Nat.xgcdAux.eq_1`：∀ (t : ℕ),   t.xgcdAux =     Nat.strongRec (motive := 
fun x => ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ)       (fun n ih s t r' s' t' =>         
match …
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
-/
theorem gcdB_zero_left {s : ℕ} : gcdB 0 s = 1 := by
  rw [gcdB, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/-
**Nat.gcdA_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcdA_zero_right {s : Nat} (h : s != 0) : gcdA s 0 = 1
参数：h : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.zero_ediv`：∀ (b : ℤ), 0 / b = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem gcdA_zero_right {s : ℕ} (h : s ≠ 0) : gcdA s 0 = 1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdA, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/-
**Nat.gcdB_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcdB_zero_right {s : Nat} (h : s != 0) : gcdB s 0 = 0
参数：h : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.strongRec_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) → 
m < n → motive m) → motive n) (t : ℕ),   Nat.strongRec ind t = ind t fun m x => 
Nat.st…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.zero_ediv`：∀ (b : ℤ), 0 / b = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem gcdB_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  simp [gcdB, xgcd, xgcdAux, Nat.strongRec_eq]

@[simp]
/-
**Nat.xgcdAux_fst** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xgcdAux_fst (x y) : forall s t s' t', (xgcdAux x s t y s' t').1 = gcd x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd.induction`：∀ {P : ℕ → ℕ → Prop} (m n : ℕ), (∀ (n : ℕ), P 0 n) → 
(∀ (m n : ℕ), 0 < m → P (n % m) m → P m n) → P m n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.xgcd_zero_left`：xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' 
t' = (r', s', t')
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.xgcdAux_rec`：xgcdAux_rec {r s t r' s' t'} (h : 0 < r) : xgcdAux r s 
t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
-/
theorem xgcdAux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]
/-
**Nat.xgcdAux_val** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y)
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.xgcd.eq_1`：∀ (x y : ℕ), x.xgcd y = (x.xgcdAux 1 0 y 0 1).2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.xgcdAux_fst`：xgcdAux_fst (x y) : forall s t s' t', (xgcdAux x s t y 
s' t').1 = gcd x y
-/
theorem xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcdAux_fst x y 1 0 0 1]
/-
**Nat.xgcd_val** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcdA gcdB; constructor

section

variable (x y : ℕ)

/-
**Nat.P** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def P : ℕ × ℤ × ℤ → Prop
  | (r, s, t) => (r : ℤ) = x * s + y * t
/-
**Nat.xgcdAux_P** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem xgcdAux_P {r r'} :
    ∀ {s t s' t'}, P x y (r, s, t) → P x y (r', s', t') → P x y (xgcdAux r s t r' s' t') := by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcdAux_rec h]; refine IH ?_ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : ℤ) = k
    rw [p, p', Int.mul_sub, sub_add_eq_add_sub, Int.mul_sub, Int.add_mul, mul_comm k t,
      mul_comm k s, ← mul_assoc, ← mul_assoc, add_comm (x * s * k), ← add_sub_assoc, sub_sub]

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
/-
**Nat.gcd_eq_gcd_ab** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * gcdB x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P`：∀ (x y : ℕ) {r r' : ℕ} {s
 t s' t' : ℤ},   Nat.P✝ x y (r, s, t) → Nat.P✝ x y (r', s', t') → Nat.P✝ x y (r.
xgcdAux s t r' s' t')
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.xgcd_val`：xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y)
· 使用定理 `Nat.xgcdAux_val`：xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgc
d x y)

--- 原说明 ---
**Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a
 x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this

end

/-
**Nat.exists_mul_mod_eq_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_mul_mod_eq_gcd {k n : Nat} (hk : gcd n k < k) : exists m < k, n * m
 % k = gcd n k
参数：hk : gcd n k < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `Int.toNat_lt`：∀ {n : ℕ} {z : ℤ}, 0 ≤ z → (z.toNat < n ↔ z < ↑n)
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Int.emod_lt`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a % b < ↑b.natAbs
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.natCast_mod`：∀ (m n : ℕ), ↑(m % n) = ↑m % ↑n
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.mul_emod`：∀ (a b n : ℤ), a * b % n = a % n * (b % n) % n
· 使用定理 `Int.emod_emod`：∀ (a b : ℤ), a % b % b = a % b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Int.add_mul_emod_self_left`：∀ (a b c : ℤ), (a + b * c) % b = a % b
-/
theorem exists_mul_mod_eq_gcd {k n : ℕ} (hk : gcd n k < k) : ∃ m < k, n * m % k = gcd n k := by
  have hk' := Int.ofNat_ne_zero.2 (Nat.zero_lt_of_lt hk).ne'
  have key := congr(($(gcd_eq_gcd_ab n k) % k).toNat)
  rw [Int.add_mul_emod_self_left, ← Int.natCast_mod, Int.toNat_natCast, mod_eq_of_lt hk] at key
  refine ⟨(n.gcdA k % k).toNat, ?_, (Int.ofNat_inj.1 ?_).trans key.symm⟩
  · rw [Int.toNat_lt (Int.emod_nonneg _ hk')]
    exact Int.emod_lt _ hk'
  rw [Int.natCast_mod, Int.natCast_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'),
    Int.toNat_of_nonneg (Int.emod_nonneg _ hk'), Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
/-
**Nat.exists_mul_mod_eq_one_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_mul_mod_eq_one_of_coprime {k n : Nat} (hkn : Coprime n k) (hk : 1 <
 k) : exists m < k, n * m % k = 1
参数：hkn : Coprime n k；hk : 1 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.exists_mul_mod_eq_gcd`：exists_mul_mod_eq_gcd {k n : Nat} (hk : gcd n
 k < k) : exists m < k, n * m % k = gcd n k
-/
theorem exists_mul_mod_eq_one_of_coprime {k n : ℕ} (hkn : Coprime n k) (hk : 1 < k) :
    ∃ m < k, n * m % k = 1 := by
  simpa [hkn, hk] using exists_mul_mod_eq_gcd (k := k) (n := n)
/-
**Nat.exists_mul_mod_eq_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_mul_mod_eq_of_coprime {k n : Nat} (r : Nat) (hkn : Coprime n k) (hk
 : k != 0) : exists m < k, n * m % k = r % k
参数：r : Nat；hkn : Coprime n k；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mod_one`：∀ (x : ℕ), x % 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_mul_mod_eq_one_of_coprime`：exists_mul_mod_eq_one_of_coprime {
k n : Nat} (hkn : Coprime n k) (hk : 1 < k) : exists m < k, n * m % k = 1
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem exists_mul_mod_eq_of_coprime {k n : ℕ} (r : ℕ) (hkn : Coprime n k) (hk : k ≠ 0) :
    ∃ m < k, n * m % k = r % k := by
  obtain rfl | hk : k = 1 ∨ 1 < k := by lia
  · simp [mod_one]
  obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hkn hk
  use (m * r) % k, mod_lt _ (by lia)
  rw [mul_mod, mod_mod, ← mul_mod, ← mul_assoc, mul_mod, hm, one_mul, mod_mod]

end Nat

/-! ### Divisibility over ℤ -/


namespace Int

/-
**Int.gcd_def** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_def (i j : Int) : gcd i j = Nat.gcd i.natAbs j.natAbs
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_def (i j : ℤ) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
/-
**Int.gcdA** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `a` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdA : ℤ → ℤ → ℤ
  | ofNat m, n => m.gcdA n.natAbs
  | -[m+1], n => -m.succ.gcdA n.natAbs

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
/-
**Int.gcdB** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ℤ → ℤ → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended GCD `b` value in the equation `gcd x y = x * a + y * b`.
-/
def gcdB : ℤ → ℤ → ℤ
  | m, ofNat n => m.natAbs.gcdB n
  | m, -[n+1] => -m.natAbs.gcdB n.succ

/-- **Bézout's lemma** -/
/-
**Int.gcd_eq_gcd_ab** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
参数：x y : ℤ；x.gcd y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.neg_mul_neg`：∀ (a b : ℤ), -a * -b = a * b

--- 原说明 ---
**Bézout's lemma**
-/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y
  | (m : ℕ), (n : ℕ) => Nat.gcd_eq_gcd_ab _ _
  | (m : ℕ), -[n+1] =>
    show (_ : ℤ) = _ + -(n + 1) * -_ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], (n : ℕ) =>
    show (_ : ℤ) = -(m + 1) * -_ + _ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], -[n+1] =>
    show (_ : ℤ) = -(m + 1) * -_ + -(n + 1) * -_ by
      rw [Int.neg_mul_neg, Int.neg_mul_neg]
      apply Nat.gcd_eq_gcd_ab
/-
**Int.lcm_def** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：lcm_def (i j : Int) : lcm i j = Nat.lcm (natAbs i) (natAbs j)
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd

/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
/-
**Int.gcd_eq_one_of_gcd_mul_right_eq_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_eq_one_of_gcd_mul_right_eq_one_left {a : Int} {m n : Nat} (h : a.gcd (
m * n) = 1) : a.gcd m = 1
参数：h : a.gcd (m * n) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Int.gcd_dvd_gcd_mul_right_right`：∀ (a b c : ℤ), a.gcd b ∣ a.gcd (b * c)

--- 原说明 ---
If `gcd a (m * n) = 1`, then `gcd a m = 1`.
-/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_right_right a m n

/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
/-
**Int.gcd_eq_one_of_gcd_mul_right_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_eq_one_of_gcd_mul_right_eq_one_right {a : Int} {m n : Nat} (h : a.gcd 
(m * n) = 1) : a.gcd n = 1
参数：h : a.gcd (m * n) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Int.gcd_dvd_gcd_mul_left_right`：∀ (a b c : ℤ), a.gcd b ∣ a.gcd (c * b)

--- 原说明 ---
If `gcd a (m * n) = 1`, then `gcd a n = 1`.
-/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_left_right a n m
/-
**Int.ne_zero_of_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ne_zero_of_gcd {x y : Int} (hc : gcd x y != 0) : x != 0 ∨ y != 0
参数：hc : gcd x y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Int.gcd_zero_right`：∀ (a : ℤ), a.gcd 0 = a.natAbs
· 使用定理 `Int.natAbs_zero`：Int.natAbs 0 = 0
-/
theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  contrapose! hc
  rw [hc.left, hc.right, gcd_zero_right, natAbs_zero]
/-
**Int.exists_gcd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_gcd_one {m n : Int} (H : 0 < gcd m n) : exists m' n' : Int, gcd m' 
n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n
参数：H : 0 < gcd m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.gcd_div_gcd_div_gcd`：∀ {i j : ℤ}, 0 < i.gcd j → (i / ↑(i.gcd j)).gcd
 (j / ↑(i.gcd j)) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_mul_cancel`：∀ {a b : ℤ}, b ∣ a → a / b * b = a
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
-/
theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
    ∃ m' n' : ℤ, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩
/-
**Int.exists_gcd_one'** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_gcd_one' {m n : Int} (H : 0 < gcd m n) : exists (g : Nat) (m' n' : 
Int), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g
参数：H : 0 < gcd m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.exists_gcd_one`：exists_gcd_one {m n : Int} (H : 0 < gcd m n) : exist
s m' n' : Int, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n
-/
theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩
/-
**Int.gcd_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_dvd_iff {a b : Int} {n : Nat} : gcd a b ∣ n ↔ exists x y : Int, ↑n = a
 * x + b * y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.gcd_eq_gcd_ab`：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
· 使用定理 `Int.add_mul`：∀ (a b c : ℤ), (a + b) * c = a * c + b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Int.dvd_add`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Int.dvd_mul_of_dvd_left`：∀ {a b c : ℤ}, a ∣ b → a ∣ b * c
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
-/
theorem gcd_dvd_iff {a b : ℤ} {n : ℕ} : gcd a b ∣ n ↔ ∃ x y : ℤ, ↑n = a * x + b * y := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h, Int.natCast_mul, gcd_eq_gcd_ab, Int.add_mul, mul_assoc, mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.natCast_dvd_natCast, h]
    exact Int.dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left ..))
      (dvd_mul_of_dvd_left (gcd_dvd_right ..))
/-
**Int.gcd_greatest** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_greatest {a b d : Int} (hd_pos : 0 <= d) (hda : d ∣ a) (hdb : d ∣ b) (
hd : forall e : Int, e ∣ a -> e ∣ b -> e ∣ d) : d = gcd a b
参数：hd_pos : 0 <= d；hda : d ∣ a；hdb : d ∣ b；hd : forall e : Int, e ∣ a -> e ∣ b -
> e ∣ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_antisymm`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → a ∣ b → b ∣ a → a = b
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Int.dvd_coe_gcd`：∀ {a b c : ℤ}, c ∣ a → c ∣ b → c ∣ ↑(a.gcd b)
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
-/
theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (natCast_nonneg (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `IsCoprime.dvd_of_dvd_mul_left` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors` -/
/-
**Int.dvd_of_dvd_mul_left_of_gcd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dvd_of_dvd_mul_left_of_gcd_one {a b c : Int} (habc : a ∣ b * c) (hab : gcd
 a c = 1) : a ∣ b
参数：habc : a ∣ b * c；hab : gcd a c = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.gcd_eq_gcd_ab`：∀ (x y : ℤ), ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.dvd_add`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Int.dvd_mul_of_dvd_left`：∀ {a b c : ℤ}, a ∣ b → a ∣ b * c
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a

--- 原说明 ---
Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `IsCoprime.dvd_of_dvd_mul_left` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`
-/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a c = 1) :
    a ∣ b := by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.natCast_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← Int.mul_add, ← this]
  rw [← this]
  exact Int.dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b)) (dvd_mul_of_dvd_left habc)

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a b = 1` then `a ∣ c`.
Compare with `IsCoprime.dvd_of_dvd_mul_right` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors` -/
/-
**Int.dvd_of_dvd_mul_right_of_gcd_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dvd_of_dvd_mul_right_of_gcd_one {a b c : Int} (habc : a ∣ b * c) (hab : gc
d a b = 1) : a ∣ c
参数：habc : a ∣ b * c；hab : gcd a b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.dvd_of_dvd_mul_left_of_gcd_one`：dvd_of_dvd_mul_left_of_gcd_one {a b 
c : Int} (habc : a ∣ b * c) (hab : gcd a c = 1) : a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Euclid's lemma: if `a ∣ b * c` and `gcd a b = 1` then `a ∣ c`.
Compare with `IsCoprime.dvd_of_dvd_mul_right` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`
-/
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a b = 1) :
    a ∣ c := by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

/-- For nonzero integers `a` and `b`, `gcd a b` is the smallest positive natural number that can be
written in the form `a * x + b * y` for some pair of integers `x` and `y` -/
/-
**Int.gcd_least_linear** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_least_linear {a b : Int} (ha : a != 0) : IsLeast { n : Nat | 0 < n ∧ e
xists x y : Int, ↑n = a * x + b * y } (a.gcd b)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Int.gcd_pos_of_ne_zero_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → 0 < a.gcd b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n

--- 原说明 ---
For nonzero integers `a` and `b`, `gcd a b` is the smallest positive natural num
ber that can be
written in the form `a * x + b * y` for some pair of integers `x` and `y`
-/
theorem gcd_least_linear {a b : ℤ} (ha : a ≠ 0) :
    IsLeast { n : ℕ | 0 < n ∧ ∃ x y : ℤ, ↑n = a * x + b * y } (a.gcd b) := by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true, dvd_refl, Set.mem_ofPred_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_ofPred_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn

end Int

section Monoid
variable {M : Type*} [Monoid M] {a : M} {m n : ℕ}

@[to_additive (attr := simp) gcd_nsmul_eq_zero]
/-
**pow_gcd_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_gcd_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where mp hmn
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用引理 `IsUnit.of_pow_eq_one`：IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n != 0
) : IsUnit a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma pow_gcd_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
  mp hmn := by
    constructor
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_left n), pow_mul, hmn, one_pow]
    · rw [← Nat.mul_div_cancel' (m.gcd_dvd_right n), pow_mul, hmn, one_pow]
  mpr
  | ⟨hm, hn⟩ => by
    obtain _ | m := m
    · simpa
    obtain ⟨y, rfl⟩ := IsUnit.of_pow_eq_one hm m.succ_ne_zero
    rw [← Units.val_pow_eq_pow_val, ← Units.val_one (α := M), ← zpow_natCast, ← Units.ext_iff] at *
    rw [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, hn, hm, one_zpow, one_zpow, one_mul]

@[to_additive]
/-
**pow_eq_one_iff_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_one_iff_of_coprime (hmn : m.Coprime n) : a ^ m = 1 ∧ a ^ n = 1 ↔ a 
= 1
参数：hmn : m.Coprime n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_eq_one_iff_of_coprime (hmn : m.Coprime n) : a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1 := by
  simp [← pow_gcd_eq_one, hmn]

end Monoid

section Group
variable {M : Type*} [Group M] {a : M} {m n : ℤ}

@[to_additive (attr := simp) intGCD_nsmul_eq_zero]
/-
**pow_intGCD_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_intGCD_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Int.gcd_ofNat_negSucc`：∀ (m n : ℕ), (↑m).gcd (Int.negSucc n) = m.gcd (n 
+ 1)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.gcd_negSucc_ofNat`：∀ (m n : ℕ), (Int.negSucc m).gcd ↑n = (m + 1).gcd
 n
· 使用定理 `Int.gcd_negSucc_negSucc`：∀ (m n : ℕ), (Int.negSucc m).gcd (Int.negSucc n
) = (m + 1).gcd (n + 1)
-/
lemma pow_intGCD_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 := by
  obtain m | m := m <;> obtain n | n := n <;> simp

end Group

variable {α : Type*}

section GroupWithZero
variable [GroupWithZero α] {a b : α} {m n : ℕ}

/-
**Commute.pow_eq_pow_iff_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {α : Type u_1} [inst : GroupWithZero α] {a b : α} {m n : ℕ},   Commute a
 b → m.Coprime n → (a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m)
参数：a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Commute.mul_zpow`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, 
Commute a b → ∀ (n : ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用引理 `Commute.zpow_zpow₀`：zpow_zpow₀ (h : Commute a b) (m n : Int) : Commute (
a ^ m) (b ^ n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
protected lemma Commute.pow_eq_pow_iff_of_coprime (hab : Commute a b) (hmn : m.Coprime n) :
    a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m := by
  refine ⟨fun h ↦ ?_, by rintro ⟨c, rfl, rfl⟩; rw [← pow_mul, ← pow_mul']⟩
  by_cases m = 0; · simp_all
  by_cases n = 0; · simp_all
  by_cases hb : b = 0; · exact ⟨0, by simp_all⟩
  by_cases ha : a = 0; · exact ⟨0, by have := h.symm; simp_all⟩
  refine ⟨a ^ Nat.gcdB m n * b ^ Nat.gcdA m n, ?_, ?_⟩ <;>
  · refine (pow_one _).symm.trans ?_
    conv_lhs => rw [← zpow_natCast, ← hmn, Nat.gcd_eq_gcd_ab]
    simp only [zpow_add₀ ha, zpow_add₀ hb, ← zpow_natCast, (hab.zpow_zpow₀ _ _).mul_zpow,
      ← zpow_mul, mul_comm (Nat.gcdB m n), mul_comm (Nat.gcdA m n)]
    simp only [zpow_mul, zpow_natCast, h]
    exact ((Commute.pow_pow (by aesop) _ _).zpow_zpow₀ _ _).symm

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero α] {a b : α} {m n : ℕ}

/-
**pow_eq_pow_iff_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_pow_iff_of_coprime (hmn : m.Coprime n) : a ^ m = b ^ n ↔ exists c, 
a = c ^ n ∧ b = c ^ m
参数：hmn : m.Coprime n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_eq_pow_iff_of_coprime`：∀ {α : Type u_1} [inst : GroupWithZer
o α] {a b : α} {m n : ℕ},   Commute a b → m.Coprime n → (a ^ m = b ^ n ↔ ∃ c, a 
= c ^ n ∧ b = c ^ m)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma pow_eq_pow_iff_of_coprime (hmn : m.Coprime n) : a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m :=
  (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn
/-
**pow_mem_range_pow_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_mem_range_pow_of_coprime (hmn : m.Coprime n) (a : α) : a ^ m in Set.ra
nge (· ^ n : α -> α) ↔ a in Set.range (· ^ n : α -> α)
参数：hmn : m.Coprime n；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_eq_pow_iff_of_coprime`：pow_eq_pow_iff_of_coprime (hmn : m.Coprime n)
 : a ^ m = b ^ n ↔ exists c, a = c ^ n ∧ b = c ^ m
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_mem_range_pow_of_coprime (hmn : m.Coprime n) (a : α) :
    a ^ m ∈ Set.range (· ^ n : α → α) ↔ a ∈ Set.range (· ^ n : α → α) := by
  simp [pow_eq_pow_iff_of_coprime hmn.symm]; aesop

end CommGroupWithZero

