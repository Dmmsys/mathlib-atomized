/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.Tactic.Qify

/-!
# Pell's Equation

*Pell's Equation* is the equation $x^2 - d y^2 = 1$, where $d$ is a positive integer
that is not a square, and one is interested in solutions in integers $x$ and $y$.

In this file, we aim at providing all of the essential theory of Pell's Equation for general $d$
(as opposed to the contents of `NumberTheory.PellMatiyasevic`, which is specific to the case
$d = a^2 - 1$ for some $a > 1$).

We begin by defining a type `Pell.Solution₁ d` for solutions of the equation,
show that it has a natural structure as an abelian group, and prove some basic
properties.

We then prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `Pell.exists_of_not_isSquare` and `Pell.Solution₁.exists_nontrivial_of_not_isSquare`.

We then define the *fundamental solution* to be the solution
with smallest $x$ among all solutions satisfying $x > 1$ and $y > 0$.
We show that every solution is a power (in the sense of the group structure mentioned above)
of the fundamental solution up to a (common) sign,
see `Pell.IsFundamental.eq_zpow_or_neg_zpow`, and that a (positive) solution has this property
if and only if it is fundamental, see `Pell.pos_generator_iff_fundamental`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory* (Section 17.5)]
  [IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Extend to `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

@[expose] public section


namespace Pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `Pell.Solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*x' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `Pell.Solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `Pell.Solution₁ d`.
-/


open CharZero Zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `Pell.isPell_iff_mem_unitary`. -/
/-
**Pell.is_pell_solution_iff_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：is_pell_solution_iff_mem_unitary {d : Int} {a : Int√d} : a.re ^ 2 - d * a.
im ^ 2 = 1 ↔ a in unitary (Int√d)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Zsqrtd.norm_eq_one_iff_mem_unitary`：norm_eq_one_iff_mem_unitary {d : Int
} {a : Int√d} : a.norm = 1 ↔ a in unitary (Int√d)
· 使用定理 `Zsqrtd.norm_def`：norm_def (n : Int√d) : n.norm = n.re * n.re - d * n.im 
* n.im
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `Pell.isPell_iff_mem_unitary`.
-/
theorem is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.
/-- `Pell.Solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
/-
**Pell.Solution** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pell.Solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 
1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
def Solution₁ (d : ℤ) : Type :=
  ↥(unitary (ℤ√d))

namespace Solution₁

variable {d : ℤ}

/-
**Pell.Solution₁.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Pell.Solution₁`。
形式化陈述：instCommGroup : CommGroup (Solution₁ d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup : CommGroup (Solution₁ d) :=
  inferInstanceAs (CommGroup (unitary (ℤ√d)))
/-
**Pell.Solution₁.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 `Pell.Solution₁`。
形式化陈述：instHasDistribNeg : HasDistribNeg (Solution₁ d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasDistribNeg : HasDistribNeg (Solution₁ d) :=
  inferInstanceAs (HasDistribNeg (unitary (ℤ√d)))
/-
**Pell.Solution₁.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Pell.Solution₁`。
形式化陈述：instInhabited : Inhabited (Solution₁ d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (Solution₁ d) :=
  inferInstanceAs (Inhabited (unitary (ℤ√d)))
/-
**Pell.Solution₁.** 是 Mathlib 中的一个实例，位于命名空间 `Pell.Solution₁`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (Solution₁ d) (ℤ√d) where coe := Subtype.val

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
/-
**Pell.Solution₁.x** 是 Mathlib 中的一个定义，位于命名空间 `Pell.Solution₁`。
形式化陈述：{d : ℤ} → Pell.Solution₁ d → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1`
-/
protected def x (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).re

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
/-
**Pell.Solution₁.y** 是 Mathlib 中的一个定义，位于命名空间 `Pell.Solution₁`。
形式化陈述：{d : ℤ} → Pell.Solution₁ d → ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1`
-/
protected def y (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).im

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
/-
**Pell.Solution₁.prop** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pell.is_pell_solution_iff_mem_unitary`：is_pell_solution_iff_mem_unitary 
{d : Int} {a : Int√d} : a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a in unitary (Int√d)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1`
-/
theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
/-
**Pell.Solution₁.prop_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
An alternative form of the equation, suitable for rewriting `x^2`.
-/
theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by rw [← a.prop]; ring

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
/-
**Pell.Solution₁.prop_y** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
An alternative form of the equation, suitable for rewriting `d * y^2`.
-/
theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by rw [← a.prop]; ring

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
/-
**Pell.Solution₁.ext** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b
参数：hx : a.x = b.x；hy : a.y = b.y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y

--- 原说明 ---
Two solutions are equal if their `x` and `y` components are equal.
-/
theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
  Subtype.ext <| Zsqrtd.ext hx hy

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
/-
**Pell.Solution₁.mk** 是 Mathlib 中的一个定义，位于命名空间 `Pell.Solution₁`。
形式化陈述：mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d where val
参数：x y : Int；prop : x ^ 2 - d * y ^ 2 = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a solution from `x`, `y` and a proof that the equation is satisfied.
-/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d where
  val := ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop

@[simp]
/-
**Pell.Solution₁.x_mk** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x
参数：x y : Int；prop : x ^ 2 - d * y ^ 2 = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x :=
  rfl

@[simp]
/-
**Pell.Solution₁.y_mk** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y
参数：x y : Int；prop : x ^ 2 - d * y ^ 2 = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y :=
  rfl

@[simp]
/-
**Pell.Solution₁.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：coe_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : Int√
d) = ⟨x, y⟩
参数：x y : Int；prop : x ^ 2 - d * y ^ 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.ext`：∀ {d : ℤ} {x y : ℤ√d}, x.re = y.re → x.im = y.im → x = y
· 使用定理 `Pell.Solution₁.x_mk`：x_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (
mk x y prop).x = x
· 使用定理 `Pell.Solution₁.y_mk`：y_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (
mk x y prop).y = y
-/
theorem coe_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x, y⟩ :=
  Zsqrtd.ext (x_mk x y prop) (y_mk x y prop)

@[simp]
/-
**Pell.Solution₁.x_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_one : (1 : Solution₁ d).x = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem x_one : (1 : Solution₁ d).x = 1 :=
  rfl

@[simp]
/-
**Pell.Solution₁.y_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_one : (1 : Solution₁ d).y = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_one : (1 : Solution₁ d).y = 0 :=
  rfl

@[simp]
/-
**Pell.Solution₁.x_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y)
参数：a b : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) := by
  rw [← mul_assoc]
  rfl

@[simp]
/-
**Pell.Solution₁.y_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x
参数：a b : Solution₁ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x :=
  rfl

@[simp]
/-
**Pell.Solution₁.x_inv** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_inv (a : Solution₁ d) : a⁻¹.x = a.x
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem x_inv (a : Solution₁ d) : a⁻¹.x = a.x :=
  rfl

@[simp]
/-
**Pell.Solution₁.y_inv** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_inv (a : Solution₁ d) : a⁻¹.y = -a.y
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_inv (a : Solution₁ d) : a⁻¹.y = -a.y :=
  rfl

@[simp]
/-
**Pell.Solution₁.x_neg** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_neg (a : Solution₁ d) : (-a).x = -a.x
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem x_neg (a : Solution₁ d) : (-a).x = -a.x :=
  rfl

@[simp]
/-
**Pell.Solution₁.y_neg** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_neg (a : Solution₁ d) : (-a).y = -a.y
参数：a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem y_neg (a : Solution₁ d) : (-a).y = -a.y :=
  rfl

/-- When `d` is negative, then `x` or `y` must be zero in a solution. -/
/-
**Pell.Solution₁.eq_zero_of_d_neg** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：eq_zero_of_d_neg (h₀ : d < 0) (a : Solution₁ d) : a.x = 0 ∨ a.y = 0
参数：h₀ : d < 0；a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sq_pos_of_ne_zero`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [ExistsAddOfLE R] {a : R},   a ≠ 0 → 0 < a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
When `d` is negative, then `x` or `y` must be zero in a solution.
-/
theorem eq_zero_of_d_neg (h₀ : d < 0) (a : Solution₁ d) : a.x = 0 ∨ a.y = 0 := by
  have h := a.prop
  contrapose! h
  have h1 := sq_pos_of_ne_zero h.1
  have h2 := sq_pos_of_ne_zero h.2
  nlinarith

/-- A solution has `x ≠ 0`. -/
/-
**Pell.Solution₁.x_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_ne_zero (h₀ : 0 <= d) (a : Solution₁ d) : a.x != 0
参数：h₀ : 0 <= d；a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Pell.Solution₁.prop_y`：prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 
- 1

--- 原说明 ---
A solution has `x ≠ 0`.
-/
theorem x_ne_zero (h₀ : 0 ≤ d) (a : Solution₁ d) : a.x ≠ 0 := by
  intro hx
  have h : 0 ≤ d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  rw [a.prop_y, hx, sq, zero_mul, zero_sub] at h
  exact not_le.mpr (neg_one_lt_zero : (-1 : ℤ) < 0) h

/-- A solution with `x > 1` must have `y ≠ 0`. -/
/-
**Pell.Solution₁.y_ne_zero_of_one_lt_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁
`。
形式化陈述：y_ne_zero_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : a.y != 0
参数：ha : 1 < a.x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_lt_sq_iff₀`：one_lt_sq_iff₀ (ha : 0 <= a) : 1 < a ^ 2 ↔ 1 < a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
A solution with `x > 1` must have `y ≠ 0`.
-/
theorem y_ne_zero_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : a.y ≠ 0 := by
  intro hy
  have prop := a.prop
  rw [hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero] at prop
  exact lt_irrefl _ (((one_lt_sq_iff₀ <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)

/-- If a solution has `x > 1`, then `d` is positive. -/
/-
**Pell.Solution₁.d_pos_of_one_lt_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：d_pos_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : 0 < d
参数：ha : 1 < a.x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.prop_y`：prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 
- 1
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α

--- 原说明 ---
If a solution has `x > 1`, then `d` is positive.
-/
theorem d_pos_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : 0 < d := by
  refine pos_of_mul_pos_left ?_ (sq_nonneg a.y)
  rw [a.prop_y, sub_pos]
  exact one_lt_pow₀ ha two_ne_zero

/-- If a solution has `x > 1`, then `d` is not a square. -/
/-
**Pell.Solution₁.d_nonsquare_of_one_lt_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solutio
n₁`。
形式化陈述：d_nonsquare_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : ¬IsSquare d
参数：ha : 1 < a.x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a solution has `x > 1`, then `d` is not a square.
-/
theorem d_nonsquare_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : ¬IsSquare d := by
  have hp := a.prop
  rintro ⟨b, rfl⟩
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  lia

/-- A solution with `x = 1` is trivial. -/
/-
**Pell.Solution₁.eq_one_of_x_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：eq_one_of_x_eq_one (h₀ : d != 0) {a : Solution₁ d} (ha : a.x = 1) : a = 1
参数：h₀ : d != 0；ha : a.x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.prop_y`：prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 
- 1
· 使用定理 `Pell.Solution₁.ext`：ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y =
 b.y) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
A solution with `x = 1` is trivial.
-/
theorem eq_one_of_x_eq_one (h₀ : d ≠ 0) {a : Solution₁ d} (ha : a.x = 1) : a = 1 := by
  have prop := a.prop_y
  rw [ha, one_pow, sub_self, mul_eq_zero, or_iff_right h₀, sq_eq_zero_iff] at prop
  exact ext ha prop

/-- A solution is `1` or `-1` if and only if `y = 0`. -/
/-
**Pell.Solution₁.eq_one_or_neg_one_iff_y_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pell
.Solution₁`。
形式化陈述：eq_one_or_neg_one_iff_y_eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Pell.Solution₁.ext`：ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y =
 b.y) : a = b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
A solution is `1` or `-1` if and only if `y = 0`.
-/
theorem eq_one_or_neg_one_iff_y_eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 := by
  refine ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => ?_⟩
  have prop := a.prop
  rw [H, sq (0 : ℤ), mul_zero, mul_zero, sub_zero, sq_eq_one_iff] at prop
  exact prop.imp (fun h => ext h H) fun h => ext h H

/-- The set of solutions with `x > 0` is closed under multiplication. -/
/-
**Pell.Solution₁.x_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).
x
参数：ha : 0 < a.x；hb : 0 < b.x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.x_mul`：x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x 
+ d * (a.y * b.y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_lt_iff_pos_add'`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] 
[AddLeftStrictMono α] {a b : α}, -a < b ↔ 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_lt_sq`：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Pell.Solution₁.prop_x`：prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y 
^ 2
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
The set of solutions with `x > 0` is closed under multiplication.
-/
theorem x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).x := by
  simp only [x_mul]
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp ?_).1
  rw [← abs_of_pos ha, ← abs_of_pos hb, ← abs_mul, ← sq_lt_sq, mul_pow a.x, a.prop_x, b.prop_x, ←
    sub_pos]
  ring_nf
  rcases le_or_gt 0 d with h | h
  · positivity
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    simp

/-- The set of solutions with `x` and `y` positive is closed under multiplication. -/
/-
**Pell.Solution₁.y_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b
.x) (hby : 0 < b.y) : 0 < (a * b).y
参数：hax : 0 < a.x；hay : 0 < a.y；hbx : 0 < b.x；hby : 0 < b.y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
The set of solutions with `x` and `y` positive is closed under multiplication.
-/
theorem y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
    (hby : 0 < b.y) : 0 < (a * b).y := by
  simp only [y_mul]
  positivity

/-- If `(x, y)` is a solution with `x` positive, then all its powers with natural exponents
have positive `x`. -/
/-
**Pell.Solution₁.x_pow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : Nat) : 0 < (a ^ n).x
参数：hax : 0 < a.x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Pell.Solution₁.x_mul_pos`：x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (
hb : 0 < b.x) : 0 < (a * b).x

--- 原说明 ---
If `(x, y)` is a solution with `x` positive, then all its powers with natural ex
ponents
have positive `x`.
-/
theorem x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℕ) : 0 < (a ^ n).x := by
  induction n with
  | zero => simp only [pow_zero, x_one, zero_lt_one]
  | succ n ih => rw [pow_succ]; exact x_mul_pos ih hax

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
natural exponents have positive `y`. -/
/-
**Pell.Solution₁.y_pow_succ_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_pow_succ_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : Nat)
 : 0 < (a ^ n.succ).y
参数：hax : 0 < a.x；hay : 0 < a.y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Pell.Solution₁.y_mul_pos`：y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) 
(hay : 0 < a.y) (hbx : 0 < b.x) (hby : 0 < b.y) : 0 < (a * b).y
· 使用定理 `Pell.Solution₁.x_pow_pos`：x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n
 : Nat) : 0 < (a ^ n).x

--- 原说明 ---
If `(x, y)` is a solution with `x` and `y` positive, then all its powers with po
sitive
natural exponents have positive `y`.
-/
theorem y_pow_succ_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : ℕ) :
    0 < (a ^ n.succ).y := by
  induction n with
  | zero => simp only [pow_one, hay]
  | succ n ih => rw [pow_succ']; exact y_mul_pos hax hay (x_pow_pos hax _) ih

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
exponents have positive `y`. -/
/-
**Pell.Solution₁.y_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：y_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : Int} (hn
 : 0 < n) : 0 < (a ^ n).y
参数：hax : 0 < a.x；hay : 0 < a.y；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Pell.Solution₁.y_pow_succ_pos`：y_pow_succ_pos {a : Solution₁ d} (hax : 0
 < a.x) (hay : 0 < a.y) (n : Nat) : 0 < (a ^ n.succ).y

--- 原说明 ---
If `(x, y)` is a solution with `x` and `y` positive, then all its powers with po
sitive
exponents have positive `y`.
-/
theorem y_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : ℤ} (hn : 0 < n) :
    0 < (a ^ n).y := by
  lift n to ℕ using hn.le
  norm_cast at hn ⊢
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact y_pow_succ_pos hax hay _

/-- If `(x, y)` is a solution with `x` positive, then all its powers have positive `x`. -/
/-
**Pell.Solution₁.x_zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : Int) : 0 < (a ^ n).x
参数：hax : 0 < a.x；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Pell.Solution₁.x_pow_pos`：x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n
 : Nat) : 0 < (a ^ n).x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹

--- 原说明 ---
If `(x, y)` is a solution with `x` positive, then all its powers have positive `
x`.
-/
theorem x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℤ) : 0 < (a ^ n).x := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)

/-- If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of any power
has the same sign as the exponent. -/
/-
**Pell.Solution₁.sign_y_zpow_eq_sign_of_x_pos_of_y_pos** 是 Mathlib 中的一个定理，位于命名空间
 `Pell.Solution₁`。
形式化陈述：sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : Solution₁ d} (hax : 0 < a.x) (h
ay : 0 < a.y) (n : Int) : (a ^ n).y.sign = n.sign
参数：hax : 0 < a.x；hay : 0 < a.y；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Pell.Solution₁.y_pow_succ_pos`：y_pow_succ_pos {a : Solution₁ d} (hax : 0
 < a.x) (hay : 0 < a.y) (n : Nat) : 0 < (a ^ n.succ).y
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.sign_eq_neg_one_of_neg`：∀ {a : ℤ}, a < 0 → a.sign = -1
· 使用定理 `neg_neg_of_pos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Partial
Order α] [IsOrderedAddMonoid α] {a : α}, 0 < a → -a < 0

--- 原说明 ---
If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of a
ny power
has the same sign as the exponent.
-/
theorem sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
    (n : ℤ) : (a ^ n).y.sign = n.sign := by
  rcases n with ((_ | n) | n)
  · rfl
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
  · rw [zpow_negSucc]
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))

/-- If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`. -/
/-
**Pell.Solution₁.exists_pos_variant** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solution₁`。
形式化陈述：exists_pos_variant (h₀ : 0 < d) (a : Solution₁ d) : exists b : Solution₁ d
, 0 < b.x ∧ 0 <= b.y ∧ a in ({b, b⁻¹, -b, -b⁻¹} : Set (Solution₁ d))
参数：h₀ : 0 < d；a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Pell.Solution₁.x_ne_zero`：x_ne_zero (h₀ : 0 <= d) (a : Solution₁ d) : a.
x != 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`.
-/
theorem exists_pos_variant (h₀ : 0 < d) (a : Solution₁ d) :
    ∃ b : Solution₁ d, 0 < b.x ∧ 0 ≤ b.y ∧ a ∈ ({b, b⁻¹, -b, -b⁻¹} : Set (Solution₁ d)) := by
  refine
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, ?_, ?_, ?_⟩) fun hy hx => ⟨-a, ?_, ?_, ?_⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, ?_⟩) fun hy hx => ⟨a⁻¹, hx, ?_, ?_⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true] <;>
    assumption

end Solution₁

section Existence

/-!
### Existence of nontrivial solutions
-/


variable {d : ℤ}

open Set Real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
/-
**Pell.exists_of_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) : exists x y : Int,
 x ^ 2 - d * y ^ 2 = 1 ∧ y != 0
参数：h₀ : 0 < d；hd : ¬IsSquare d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrational_nrt_of_notint_nrt`：irrational_nrt_of_notint_nrt {x : Real} (n
 : Nat) (m : Int) (hxr : x ^ n = m) (hv : ¬exists y : Int, x = y) (hnpos : 0 < n
) : Irrational x
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Int.cast_nonneg`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1
 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] {n : ℤ},   0 ≤ n → 0 ≤ ↑n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `exists_int_gt`：exists_int_gt (x : R) : exists n : Int, x < n
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 144 条，此处仅展示前 30 条）

--- 原说明 ---
If `d` is a positive integer that is not a square, then there is a nontrivial so
lution
to the Pell equation `x^2 - d*y^2 = 1`.
-/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 := by
  let ξ : ℝ := √d
  have hξ : Irrational ξ := by
    refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg h₀.le) ?_ two_pos
    rintro ⟨x, hx⟩
    refine hd ⟨x, @Int.cast_injective ℝ _ _ d (x * x) ?_⟩
    rw [← sq_sqrt <| Int.cast_nonneg h₀.le, Int.cast_mul, ← hx, sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : {q : ℚ | |q.1 ^ 2 - d * (q.2 : ℤ) ^ 2| < M}.Infinite := by
    refine Infinite.mono (fun q h => ?_) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : ℝ) / (q.den : ℝ) = q := mod_cast q.num_div_den
    rw [mem_ofPred, abs_sub_comm, ← @Int.cast_lt ℝ,
      ← div_lt_div_iff_of_pos_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel_right₀ _ h0.ne', ← div_pow, h1, ←
      sq_sqrt (Int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div]
    refine mul_lt_mul'' (((abs_add_le ξ q).trans ?_).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add']
    rw [mem_ofPred, abs_sub_comm] at h
    refine (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans ?_)
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * (q.den : ℤ) ^ 2 = m}.Infinite := by
    contrapose! hM
    refine (congr_arg _ (ext fun x => ?_)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_ofPred, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_ofPred, sub_eq_zero, mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨d, hq⟩
    rw [ha, mul_pow, mul_right_inj' (pow_pos (Int.natCast_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  have := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  let f : ℚ → ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : ℤ) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : ℤ) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1, hq2, ← sq, ← sq]
    norm_cast
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd, Nat.cast_pow, ← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hq1, hq2]
  replace hm₀ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm₀
  refine ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      ?_, ?_⟩
  · qify [hd₁, hd₂]
    field_simp
    norm_cast
    grind
  · qify [hd₂]
    refine div_ne_zero_iff.mpr ⟨?_, hm₀⟩
    exact mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
/-
**Pell.exists_iff_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：exists_iff_not_isSquare (h₀ : 0 < d) : (exists x y : Int, x ^ 2 - d * y ^ 
2 = 1 ∧ y != 0) ↔ ¬IsSquare d
参数：h₀ : 0 < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `Int.eq_of_mul_eq_one`：eq_of_mul_eq_one (h : u * v = 1) : u = v
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Pell.exists_of_not_isSquare`：exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬
IsSquare d) : exists x y : Int, x ^ 2 - d * y ^ 2 = 1 ∧ y != 0

--- 原说明 ---
If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square.
-/
theorem exists_iff_not_isSquare (h₀ : 0 < d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬IsSquare d := by
  refine ⟨?_, exists_of_not_isSquare h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy

namespace Solution₁

/-- If `d` is a positive integer that is not a square, then there exists a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
/-
**Pell.Solution₁.exists_nontrivial_of_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Pe
ll.Solution₁`。
形式化陈述：exists_nontrivial_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) : exists
 a : Solution₁ d, a != 1 ∧ a != -1
参数：h₀ : 0 < d；hd : ¬IsSquare d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.exists_of_not_isSquare`：exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬
IsSquare d) : exists x y : Int, x ^ 2 - d * y ^ 2 = 1 ∧ y != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0

--- 原说明 ---
If `d` is a positive integer that is not a square, then there exists a nontrivia
l solution
to the Pell equation `x^2 - d*y^2 = 1`.
-/
theorem exists_nontrivial_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, a ≠ 1 ∧ a ≠ -1 := by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk x y prop, fun H => ?_, fun H => ?_⟩ <;> apply_fun Solution₁.y at H <;>
    simp [hy] at H

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
/-
**Pell.Solution₁.exists_pos_of_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Pell.Solu
tion₁`。
形式化陈述：exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) : exists a : So
lution₁ d, 1 < a.x ∧ 0 < a.y
参数：h₀ : 0 < d；hd : ¬IsSquare d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.exists_of_not_isSquare`：exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬
IsSquare d) : exists x y : Int, x ^ 2 - d * y ^ 2 = 1 ∧ y != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Pell.Solution₁.x_mk`：x_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (
mk x y prop).x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_lt_sq_iff_one_lt_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : Lin
earOrder α] [IsStrictOrderedRing α] (a : α), 1 < a ^ 2 ↔ 1 < |a|
· 使用定理 `eq_add_of_sub_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - 
c = b → a = b + c
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sq_pos_of_ne_zero`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [ExistsAddOfLE R] {a : R},   a ≠ 0 → 0 < a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0

--- 原说明 ---
If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`.
-/
theorem exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, 1 < a.x ∧ 0 < a.y := by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), ?_, abs_pos.mpr hy⟩
  rw [x_mk, ← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero hy)

end Solution₁

end Existence

/-! ### Fundamental solutions

We define the notion of a *fundamental solution* of Pell's equation and
show that it exists and is unique (when `d` is positive and non-square)
and generates the group of solutions up to sign.
-/


variable {d : ℤ}

/-- We define a solution to be *fundamental* if it has `x > 1` and `y > 0`
and its `x` is the smallest possible among solutions with `x > 1`. -/
/-
**Pell.IsFundamental** 是 Mathlib 中的一个定义，位于命名空间 `Pell`。
形式化陈述：IsFundamental (a : Solution₁ d) : Prop
参数：a : Solution₁ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define a solution to be *fundamental* if it has `x > 1` and `y > 0`
and its `x` is the smallest possible among solutions with `x > 1`.
-/
def IsFundamental (a : Solution₁ d) : Prop :=
  1 < a.x ∧ 0 < a.y ∧ ∀ {b : Solution₁ d}, 1 < b.x → a.x ≤ b.x

namespace IsFundamental

open Solution₁

/-- A fundamental solution has positive `x`. -/
/-
**Pell.IsFundamental.x_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`。
形式化陈述：x_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < a.x
参数：h : IsFundamental a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A fundamental solution has positive `x`.
-/
theorem x_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < a.x :=
  zero_lt_one.trans h.1

/-- If a fundamental solution exists, then `d` must be positive. -/
/-
**Pell.IsFundamental.d_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`。
形式化陈述：d_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < d
参数：h : IsFundamental a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.d_pos_of_one_lt_x`：d_pos_of_one_lt_x {a : Solution₁ d} (h
a : 1 < a.x) : 0 < d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If a fundamental solution exists, then `d` must be positive.
-/
theorem d_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < d :=
  d_pos_of_one_lt_x h.1

/-- If a fundamental solution exists, then `d` must be a non-square. -/
/-
**Pell.IsFundamental.d_nonsquare** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`。
形式化陈述：d_nonsquare {a : Solution₁ d} (h : IsFundamental a) : ¬IsSquare d
参数：h : IsFundamental a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.d_nonsquare_of_one_lt_x`：d_nonsquare_of_one_lt_x {a : Sol
ution₁ d} (ha : 1 < a.x) : ¬IsSquare d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If a fundamental solution exists, then `d` must be a non-square.
-/
theorem d_nonsquare {a : Solution₁ d} (h : IsFundamental a) : ¬IsSquare d :=
  d_nonsquare_of_one_lt_x h.1

/-- If there is a fundamental solution, it is unique. -/
/-
**Pell.IsFundamental.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`
。
形式化陈述：subsingleton {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamenta
l b) : a = b
参数：ha : IsFundamental a；hb : IsFundamental b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Pell.Solution₁.ext`：ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y =
 b.y) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.prop_y`：prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 
- 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.eq_of_mul_eq_mul_left`：∀ {a b c : ℤ}, a ≠ 0 → a * b = a * c → b = c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Pell.IsFundamental.d_pos`：d_pos {a : Solution₁ d} (h : IsFundamental a) 
: 0 < d

--- 原说明 ---
If there is a fundamental solution, it is unique.
-/
theorem subsingleton {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b) : a = b := by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  refine Solution₁.ext hx ?_
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  exact (sq_eq_sq₀ ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)

/-- If `d` is positive and not a square, then a fundamental solution exists. -/
/-
**Pell.IsFundamental.exists_of_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFu
ndamental`。
形式化陈述：exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) : exists a : Soluti
on₁ d, IsFundamental a
参数：h₀ : 0 < d；hd : ¬IsSquare d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.exists_pos_of_not_isSquare`：exists_pos_of_not_isSquare (h
₀ : 0 < d) (hd : ¬IsSquare d) : exists a : Solution₁ d, 1 < a.x ∧ 0 < a.y
· 使用定理 `Pell.Solution₁.prop`：prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Pell.Solution₁.x_mk`：x_mk (x y : Int) (prop : x ^ 2 - d * y ^ 2 = 1) : (
mk x y prop).x = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `Pell.Solution₁.y_ne_zero_of_one_lt_x`：y_ne_zero_of_one_lt_x {a : Solutio
n₁ d} (ha : 1 < a.x) : a.y != 0
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2

--- 原说明 ---
If `d` is positive and not a square, then a fundamental solution exists.
-/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, IsFundamental a := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
  -- convert to `x : ℕ` to be able to use `Nat.find`
  have P : ∃ x' : ℕ, 1 < x' ∧ ∃ y' : ℤ, 0 < y' ∧ (x' : ℤ) ^ 2 - d * y' ^ 2 = 1 := by
    have hax := a.prop
    lift a.x to ℕ using by positivity with ax
    norm_cast at ha₁
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩
  classical
  -- to avoid having to show that the predicate is decidable
  let x₁ := Nat.find P
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := Nat.find_spec P
  refine ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact mod_cast hx, hy₀, fun {b} hb => ?_⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
  refine Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr <| y_ne_zero_of_one_lt_x hb'', ?_⟩
  rw [← hb', sq_abs]
  exact b.prop

/-- The map sending an integer `n` to the `y`-coordinate of `a^n` for a fundamental
solution `a` is strictly increasing. -/
/-
**Pell.IsFundamental.y_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`
。
形式化陈述：y_strictMono {a : Solution₁ d} (h : IsFundamental a) : StrictMono fun n : 
Int => (a ^ n).y
参数：h : IsFundamental a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Pell.Solution₁.y_mul`：y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y 
+ a.y * b.x
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
The map sending an integer `n` to the `y`-coordinate of `a^n` for a fundamental
solution `a` is strictly increasing.
-/
theorem y_strictMono {a : Solution₁ d} (h : IsFundamental a) :
    StrictMono fun n : ℤ => (a ^ n).y := by
  have H : ∀ n : ℤ, 0 ≤ n → (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos, zpow_add, zpow_one, y_mul, add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg ?_ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one, le_refl]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine strictMono_int_of_lt_succ fun n => ?_
  rcases le_or_gt 0 n with hn | hn
  · exact H n hn
  · let m : ℤ := -n - 1
    have hm : n = -m - 1 := by simp only [m, neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    rw [hm, sub_add_cancel, ← neg_add', zpow_neg, zpow_neg, y_inv, y_inv, neg_lt_neg_iff]
    exact H _ (by lia)

/-- If `a` is a fundamental solution, then `(a^m).y < (a^n).y` if and only if `m < n`. -/
/-
**Pell.IsFundamental.zpow_y_lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamen
tal`。
形式化陈述：zpow_y_lt_iff_lt {a : Solution₁ d} (h : IsFundamental a) (m n : Int) : (a 
^ m).y < (a ^ n).y ↔ m < n
参数：h : IsFundamental a；m n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Pell.IsFundamental.y_strictMono`：y_strictMono {a : Solution₁ d} (h : IsF
undamental a) : StrictMono fun n : Int => (a ^ n).y

--- 原说明 ---
If `a` is a fundamental solution, then `(a^m).y < (a^n).y` if and only if `m < n
`.
-/
theorem zpow_y_lt_iff_lt {a : Solution₁ d} (h : IsFundamental a) (m n : ℤ) :
    (a ^ m).y < (a ^ n).y ↔ m < n := by
  refine ⟨fun H => ?_, fun H => h.y_strictMono H⟩
  contrapose! H
  exact h.y_strictMono.monotone H

/-- The `n`th power of a fundamental solution is trivial if and only if `n = 0`. -/
/-
**Pell.IsFundamental.zpow_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundament
al`。
形式化陈述：zpow_eq_one_iff {a : Solution₁ d} (h : IsFundamental a) (n : Int) : a ^ n 
= 1 ↔ n = 0
参数：h : IsFundamental a；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Pell.IsFundamental.y_strictMono`：y_strictMono {a : Solution₁ d} (h : IsF
undamental a) : StrictMono fun n : Int => (a ^ n).y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The `n`th power of a fundamental solution is trivial if and only if `n = 0`.
-/
theorem zpow_eq_one_iff {a : Solution₁ d} (h : IsFundamental a) (n : ℤ) : a ^ n = 1 ↔ n = 0 := by
  rw [← zpow_zero a]
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩

/-- A power of a fundamental solution is never equal to the negative of a power of this
fundamental solution. -/
/-
**Pell.IsFundamental.zpow_ne_neg_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamen
tal`。
形式化陈述：zpow_ne_neg_zpow {a : Solution₁ d} (h : IsFundamental a) {n n' : Int} : a 
^ n != -a ^ n'
参数：h : IsFundamental a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.x_zpow_pos`：x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) 
(n : Int) : 0 < (a ^ n).x
· 使用定理 `Pell.IsFundamental.x_pos`：x_pos {a : Solution₁ d} (h : IsFundamental a) 
: 0 < a.x
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   a < -b ↔ b < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
· 使用定理 `Pell.Solution₁.x_neg`：x_neg (a : Solution₁ d) : (-a).x = -a.x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A power of a fundamental solution is never equal to the negative of a power of t
his
fundamental solution.
-/
theorem zpow_ne_neg_zpow {a : Solution₁ d} (h : IsFundamental a) {n n' : ℤ} : a ^ n ≠ -a ^ n' := by
  intro hf
  apply_fun Solution₁.x at hf
  have H := x_zpow_pos h.x_pos n
  rw [hf, x_neg, lt_neg, neg_zero] at H
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)

/-- The `x`-coordinate of a fundamental solution is a lower bound for the `x`-coordinate
of any positive solution. -/
/-
**Pell.IsFundamental.x_le_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`。
形式化陈述：x_le_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 
1 < a.x) : a₁.x <= a.x
参数：h : IsFundamental a₁；hax : 1 < a.x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The `x`-coordinate of a fundamental solution is a lower bound for the `x`-coordi
nate
of any positive solution.
-/
theorem x_le_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) :
    a₁.x ≤ a.x :=
  h.2.2 hax

/-- The `y`-coordinate of a fundamental solution is a lower bound for the `y`-coordinate
of any positive solution. -/
/-
**Pell.IsFundamental.y_le_y** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental`。
形式化陈述：y_le_y {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 
1 < a.x) (hay : 0 < a.y) : a₁.y <= a.y
参数：h : IsFundamental a₁；hax : 1 < a.x；hay : 0 < a.y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.prop_x`：prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y 
^ 2
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
The `y`-coordinate of a fundamental solution is a lower bound for the `y`-coordi
nate
of any positive solution.
-/
theorem y_le_y {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : a₁.y ≤ a.y := by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  rw [← abs_of_pos hay, ← abs_of_pos h.2.1, ← sq_le_sq, ← mul_le_mul_iff_right₀ h.d_pos,
    ← sub_nonpos, ← mul_sub, H, sub_nonpos, sq_le_sq, abs_of_pos (zero_lt_one.trans h.1),
    abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax

-- helper lemma for the next three results
/-
**Pell.IsFundamental.x_mul_y_le_y_mul_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundam
ental`。
形式化陈述：x_mul_y_le_y_mul_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution
₁ d} (hax : 1 < a.x) (hay : 0 < a.y) : a.x * a₁.y <= a.y * a₁.x
参数：h : IsFundamental a₁；hax : 1 < a.x；hay : 0 < a.y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Pell.IsFundamental.x_pos`：x_pos {a : Solution₁ d} (h : IsFundamental a) 
: 0 < a.x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Pell.Solution₁.prop_x`：prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y 
^ 2
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 66 条，此处仅展示前 30 条）
-/
theorem x_mul_y_le_y_mul_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
    (hax : 1 < a.x) (hay : 0 < a.y) : a.x * a₁.y ≤ a.y * a₁.x := by
  rw [← abs_of_pos <| zero_lt_one.trans hax, ← abs_of_pos hay, ← abs_of_pos h.x_pos, ←
    abs_of_pos h.2.1, ← abs_mul, ← abs_mul, ← sq_le_sq, mul_pow, mul_pow, a.prop_x, a₁.prop_x, ←
    sub_nonneg]
  ring_nf
  rw [sub_nonneg, sq_le_sq, abs_of_pos hay, abs_of_pos h.2.1]
  exact h.y_le_y hax hay

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `y`-coordinate remains nonnegative. -/
/-
**Pell.IsFundamental.mul_inv_y_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamen
tal`。
形式化陈述：mul_inv_y_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ 
d} (hax : 1 < a.x) (hay : 0 < a.y) : 0 <= (a * a₁⁻¹).y
参数：h : IsFundamental a₁；hax : 1 < a.x；hay : 0 < a.y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Pell.IsFundamental.x_mul_y_le_y_mul_x`：x_mul_y_le_y_mul_x {a₁ : Solution
₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) (hay : 0 < a.y) : 
a.x * a₁.y <= a.y * a₁.x

--- 原说明 ---
If we multiply a positive solution with the inverse of a fundamental solution,
the `y`-coordinate remains nonnegative.
-/
theorem mul_inv_y_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 ≤ (a * a₁⁻¹).y := by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using!
    h.x_mul_y_le_y_mul_x hax hay

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate stays positive. -/
/-
**Pell.IsFundamental.mul_inv_x_pos** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamental
`。
形式化陈述：mul_inv_x_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} 
(hax : 1 < a.x) (hay : 0 < a.y) : 0 < (a * a₁⁻¹).x
参数：h : IsFundamental a₁；hax : 1 < a.x；hay : 0 < a.y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.x_mul`：x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x 
+ d * (a.y * b.y)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate stays positive.
-/
theorem mul_inv_x_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 < (a * a₁⁻¹).x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
  refine lt_of_mul_lt_mul_left ?_ <| zero_le_one.trans hax.le
  calc a.x * (d * (a.y * a₁.y))
    _ = d * a.y * (a.x * a₁.y) := by ring
    _ ≤ d * a.y * (a.y * a₁.x) := by have := x_mul_y_le_y_mul_x h hax hay; have := h.d_pos; gcongr
    _ = (a.x ^ 2 - 1) * a₁.x := by rw [← a.prop_y]; ring
    _ < a.x * (a.x * a₁.x) := by linarith [h.1]

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate decreases. -/
/-
**Pell.IsFundamental.mul_inv_x_lt_x** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamenta
l`。
形式化陈述：mul_inv_x_lt_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
 (hax : 1 < a.x) (hay : 0 < a.y) : (a * a₁⁻¹).x < a.x
参数：h : IsFundamental a₁；hax : 1 < a.x；hay : 0 < a.y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pell.Solution₁.x_mul`：x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x 
+ d * (a.y * b.y)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Pell.IsFundamental.x_mul_y_le_y_mul_x`：x_mul_y_le_y_mul_x {a₁ : Solution
₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) (hay : 0 < a.y) : 
a.x * a₁.y <= a.y * a₁.x
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate decreases.
-/
theorem mul_inv_x_lt_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : (a * a₁⁻¹).x < a.x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  refine lt_of_mul_lt_mul_left ?_ h.2.1.le
  calc a₁.y * (a.x * a₁.x)
    _ = a.x * a₁.y * a₁.x := by ring
    _ ≤ a.y * a₁.x * a₁.x := by have := h.1; have := x_mul_y_le_y_mul_x h hax hay; gcongr
  rw [mul_assoc, ← sq, a₁.prop_x, ← sub_neg]
  suffices a.y - a.x * a₁.y < 0 by convert! this using 1; ring
  rw [sub_neg, ← abs_of_pos hay, ← abs_of_pos h.2.1, ← abs_of_pos <| zero_lt_one.trans hax, ←
    abs_mul, ← sq_lt_sq, mul_pow, a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ ≤ d * a.y ^ 2 := (mul_le_mul_iff_left₀ <| sq_pos_of_pos hay).mpr h.d_pos
    _ < d * a.y ^ 2 + 1 := lt_add_one _
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ ≤ (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_iff_right₀ (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)

/-- Any nonnegative solution is a power with nonnegative exponent of a fundamental solution. -/
/-
**Pell.IsFundamental.eq_pow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFundamen
tal`。
形式化陈述：eq_pow_of_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ 
d} (hax : 0 < a.x) (hay : 0 <= a.y) : exists n : Nat, a = a₁ ^ n
参数：h : IsFundamental a₁；hax : 0 < a.x；hay : 0 <= a.y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pell.Solution₁.eq_one_or_neg_one_iff_y_eq_zero`：eq_one_or_neg_one_iff_y_
eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
Any nonnegative solution is a power with nonnegative exponent of a fundamental s
olution.
-/
theorem eq_pow_of_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
    (hay : 0 ≤ a.y) : ∃ n : ℕ, a = a₁ ^ n := by
  lift a.x to ℕ using hax.le with ax hax'
  induction ax using Nat.strong_induction_on generalizing a with | h x ih =>
  rcases hay.eq_or_lt with hy | hy
  · -- case 1: `a = 1`
    refine ⟨0, ?_⟩
    rcases eq_one_or_neg_one_iff_y_eq_zero.2 hy.symm with rfl | rfl
    · simp
    · simp at hax'
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    lift (a * a₁⁻¹).x to ℕ using hxx₁.le with x' hx'
    obtain ⟨n, hn⟩ := ih x' (mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    exact ⟨n + 1, by rw [pow_succ', ← hn, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- Every solution is, up to a sign, a power of a given fundamental solution. -/
/-
**Pell.IsFundamental.eq_zpow_or_neg_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Pell.IsFunda
mental`。
形式化陈述：eq_zpow_or_neg_zpow {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solutio
n₁ d) : exists n : Int, a = a₁ ^ n ∨ a = -a₁ ^ n
参数：h : IsFundamental a₁；a : Solution₁ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.exists_pos_variant`：exists_pos_variant (h₀ : 0 < d) (a : 
Solution₁ d) : exists b : Solution₁ d, 0 < b.x ∧ 0 <= b.y ∧ a in ({b, b⁻¹, -b, -
b⁻¹} : Set (Solution₁ d…
· 使用定理 `Pell.IsFundamental.d_pos`：d_pos {a : Solution₁ d} (h : IsFundamental a) 
: 0 < d
· 使用定理 `Pell.IsFundamental.eq_pow_of_nonneg`：eq_pow_of_nonneg {a₁ : Solution₁ d}
 (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 <= a.y) : exi
sts n : Nat, a = a₁ ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b

--- 原说明 ---
Every solution is, up to a sign, a power of a given fundamental solution.
-/
theorem eq_zpow_or_neg_zpow {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d) :
    ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (mod_cast hn)⟩
  · exact ⟨-n, Or.inl (by simp [hn])⟩
  · exact ⟨n, Or.inr (by simp [hn])⟩
  · rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ⟨-n, Or.inr (by simp [hn])⟩

end IsFundamental

open Solution₁ IsFundamental

/-- When `d` is positive and not a square, then the group of solutions to the Pell equation
`x^2 - d*y^2 = 1` has a unique positive generator (up to sign). -/
/-
**Pell.existsUnique_pos_generator** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：existsUnique_pos_generator (h₀ : 0 < d) (hd : ¬IsSquare d) : exists! a₁ : 
Solution₁ d, 1 < a₁.x ∧ 0 < a₁.y ∧ forall a : Solution₁ d, exists n : Int, a = a
₁ ^ n ∨ a = -a₁ ^ n
参数：h₀ : 0 < d；hd : ¬IsSquare d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.IsFundamental.exists_of_not_isSquare`：exists_of_not_isSquare (h₀ : 
0 < d) (hd : ¬IsSquare d) : exists a : Solution₁ d, IsFundamental a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pell.IsFundamental.eq_zpow_or_neg_zpow`：eq_zpow_or_neg_zpow {a₁ : Soluti
on₁ d} (h : IsFundamental a₁) (a : Solution₁ d) : exists n : Int, a = a₁ ^ n ∨ a
 = -a₁ ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.isUnit_iff`：isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Pell.IsFundamental.zpow_eq_one_iff`：zpow_eq_one_iff {a : Solution₁ d} (h
 : IsFundamental a) (n : Int) : a ^ n = 1 ↔ n = 0
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   a < -b ↔ b < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
When `d` is positive and not a square, then the group of solutions to the Pell e
quation
`x^2 - d*y^2 = 1` has a unique positive generator (up to sign).
-/
theorem existsUnique_pos_generator (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃! a₁ : Solution₁ d,
      1 < a₁.x ∧ 0 < a₁.y ∧ ∀ a : Solution₁ d, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => ?_⟩
  obtain ⟨Hx, Hy, H⟩ := H
  obtain ⟨n₁, hn₁⟩ := H a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  rcases hn₂ with (rfl | rfl)
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    rcases hn₁ with hn₁ | hn₁
    · rcases Int.isUnit_iff.mp
          (.of_mul_eq_one _ <|
            sub_eq_zero.mp <| (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
  · rw [x_neg, lt_neg] at Hx
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    norm_num at this

/-- A positive solution is a generator (up to sign) of the group of all solutions to the
Pell equation `x^2 - d*y^2 = 1` if and only if it is a fundamental solution. -/
/-
**Pell.pos_generator_iff_fundamental** 是 Mathlib 中的一个定理，位于命名空间 `Pell`。
形式化陈述：pos_generator_iff_fundamental (a : Solution₁ d) : (1 < a.x ∧ 0 < a.y ∧ for
all b : Solution₁ d, exists n : Int, b = a ^ n ∨ b = -a ^ n) ↔ IsFundamental a
参数：a : Solution₁ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pell.Solution₁.d_pos_of_one_lt_x`：d_pos_of_one_lt_x {a : Solution₁ d} (h
a : 1 < a.x) : 0 < d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Pell.Solution₁.d_nonsquare_of_one_lt_x`：d_nonsquare_of_one_lt_x {a : Sol
ution₁ d} (ha : 1 < a.x) : ¬IsSquare d
· 使用定理 `Pell.IsFundamental.exists_of_not_isSquare`：exists_of_not_isSquare (h₀ : 
0 < d) (hd : ¬IsSquare d) : exists a : Solution₁ d, IsFundamental a
· 使用定理 `Pell.existsUnique_pos_generator`：existsUnique_pos_generator (h₀ : 0 < d)
 (hd : ¬IsSquare d) : exists! a₁ : Solution₁ d, 1 < a₁.x ∧ 0 < a₁.y ∧ forall a :
 Solution₁ d, exists …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pell.IsFundamental.eq_zpow_or_neg_zpow`：eq_zpow_or_neg_zpow {a₁ : Soluti
on₁ d} (h : IsFundamental a₁) (a : Solution₁ d) : exists n : Int, a = a₁ ^ n ∨ a
 = -a₁ ^ n

--- 原说明 ---
A positive solution is a generator (up to sign) of the group of all solutions to
 the
Pell equation `x^2 - d*y^2 = 1` if and only if it is a fundamental solution.
-/
theorem pos_generator_iff_fundamental (a : Solution₁ d) :
    (1 < a.x ∧ 0 < a.y ∧ ∀ b : Solution₁ d, ∃ n : ℤ, b = a ^ n ∨ b = -a ^ n) ↔ IsFundamental a := by
  refine ⟨fun h => ?_, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  have h₀ := d_pos_of_one_lt_x h.1
  have hd := d_nonsquare_of_one_lt_x h.1
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]

end Pell

