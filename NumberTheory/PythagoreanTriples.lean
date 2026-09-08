/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
module

public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Field

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1, 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

/-
**sq_ne_two_fin_zmod_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z != 2
参数：z : ZMod 4。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z ≠ 2 := by
  change Fin 4 at z
  fin_cases z <;> decide
/-
**Int.sq_ne_two_mod_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.sq_ne_two_mod_four (z : Int) : z * z % 4 != 2
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.intCast_eq_intCast_iff'`：intCast_eq_intCast_iff' (a b : Int) (c : N
at) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `sq_ne_two_fin_zmod_four`：sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z !=
 2
-/
theorem Int.sq_ne_two_mod_four (z : ℤ) : z * z % 4 ≠ 2 := by
  suffices ¬z * z % (4 : ℕ) = 2 % (4 : ℕ) by exact this
  rw [← ZMod.intCast_eq_intCast_iff']
  simpa using sq_ne_two_fin_zmod_four _

noncomputable section

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
/-
**PythagoreanTriple** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PythagoreanTriple (x y z : Int) : Prop
参数：x y z : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z
 * z`.
-/
def PythagoreanTriple (x y z : ℤ) : Prop :=
  x * x + y * y = z * z

/-- Pythagorean triples are interchangeable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
/-
**pythagoreanTriple_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pythagoreanTriple_comm {x y z : Int} : PythagoreanTriple x y z ↔ Pythagore
anTriple y x z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Pythagorean triples are interchangeable, i.e `x * x + y * y = y * y + x * x = z 
* z`.
This comes from additive commutativity.
-/
theorem pythagoreanTriple_comm {x y z : ℤ} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z := by
  delta PythagoreanTriple
  rw [add_comm]

/-- The zeroth Pythagorean triple is all zeros. -/
/-
**PythagoreanTriple.zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PythagoreanTriple.zero : PythagoreanTriple 0 0 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The zeroth Pythagorean triple is all zeros.
-/
theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 := by
  simp only [PythagoreanTriple, zero_mul, zero_add]

namespace PythagoreanTriple

variable {x y z : ℤ}

/-
**PythagoreanTriple.eq** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：eq (h : PythagoreanTriple x y z) : x * x + y * y = z * z
参数：h : PythagoreanTriple x y z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq (h : PythagoreanTriple x y z) : x * x + y * y = z * z :=
  h

@[symm]
/-
**PythagoreanTriple.symm** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：symm (h : PythagoreanTriple x y z) : PythagoreanTriple y x z
参数：h : PythagoreanTriple x y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pythagoreanTriple_comm`：pythagoreanTriple_comm {x y z : Int} : Pythagore
anTriple x y z ↔ PythagoreanTriple y x z
-/
theorem symm (h : PythagoreanTriple x y z) : PythagoreanTriple y x z := by
  rwa [pythagoreanTriple_comm]

/-- A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`. -/
/-
**PythagoreanTriple.mul** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：mul (h : PythagoreanTriple x y z) (k : Int) : PythagoreanTriple (k * x) (k
 * y) (k * z)
参数：h : PythagoreanTriple x y z；k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z

--- 原说明 ---
A triple is still a triple if you multiply `x`, `y` and `z`
by a constant `k`.
-/
theorem mul (h : PythagoreanTriple x y z) (k : ℤ) : PythagoreanTriple (k * x) (k * y) (k * z) :=
  calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
    _ = k ^ 2 * (z * z) := by rw [h.eq]
    _ = k * z * (k * z) := by ring

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
/-
**PythagoreanTriple.mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：mul_iff (k : Int) (hk : k != 0) : PythagoreanTriple (k * x) (k * y) (k * z
) ↔ PythagoreanTriple x y z
参数：k : Int；hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `PythagoreanTriple.mul`：mul (h : PythagoreanTriple x y z) (k : Int) : Pyt
hagoreanTriple (k * x) (k * y) (k * z)

--- 原说明 ---
`(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple.
-/
theorem mul_iff (k : ℤ) (hk : k ≠ 0) :
    PythagoreanTriple (k * x) (k * y) (k * z) ↔ PythagoreanTriple x y z := by
  refine ⟨?_, fun h => h.mul k⟩
  simp only [PythagoreanTriple]
  intro h
  rw [← mul_left_inj' (mul_ne_zero hk hk)]
  convert! h using 1 <;> ring

/-- A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that
either
* `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
* `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
@[nolint unusedArguments]
/-
**PythagoreanTriple.IsClassified** 是 Mathlib 中的一个定义，位于命名空间 `PythagoreanTriple`。
形式化陈述：IsClassified (_ : PythagoreanTriple x y z)
参数：_ : PythagoreanTriple x y z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Pythagorean triple `x, y, z` is “classified” if there exist integers `k, m, n`
 such that
either
* `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
* `x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`.
-/
def IsClassified (_ : PythagoreanTriple x y z) :=
  ∃ k m n : ℤ,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1

/-- A primitive Pythagorean triple `x, y, z` is a Pythagorean triple with `x` and `y` coprime.
Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
* `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
* `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unusedArguments]
/-
**PythagoreanTriple.IsPrimitiveClassified** 是 Mathlib 中的一个定义，位于命名空间 `Pythagorean
Triple`。
形式化陈述：IsPrimitiveClassified (_ : PythagoreanTriple x y z)
参数：_ : PythagoreanTriple x y z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A primitive Pythagorean triple `x, y, z` is a Pythagorean triple with `x` and `y
` coprime.
Such a triple is “primitively classified” if there exist coprime integers `m, n`
 such that either
* `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
* `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
def IsPrimitiveClassified (_ : PythagoreanTriple x y z) :=
  ∃ m n : ℤ,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

variable (h : PythagoreanTriple x y z)
include h
/-
**PythagoreanTriple.mul_isClassified** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTripl
e`。
形式化陈述：mul_isClassified (k : Int) (hc : h.IsClassified) : (h.mul k).IsClassified
参数：k : Int；hc : h.IsClassified。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.mul`：mul (h : PythagoreanTriple x y z) (k : Int) : Pyt
hagoreanTriple (k * x) (k * y) (k * z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_isClassified (k : ℤ) (hc : h.IsClassified) : (h.mul k).IsClassified := by
  obtain ⟨l, m, n, ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co⟩⟩ := hc <;> use k * l, m, n <;> grind
/-
**PythagoreanTriple.even_odd_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTr
iple`。
形式化陈述：even_odd_of_coprime (hc : Int.gcd x y = 1) : x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2
 = 1 ∧ y % 2 = 0
参数：hc : Int.gcd x y = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.emod_two_eq_zero_or_one`：emod_two_eq_zero_or_one (n : Int) : n % 2 =
 0 ∨ n % 2 = 1
· 使用定理 `Nat.not_coprime_of_dvd_of_dvd`：∀ {d m n : ℕ}, 1 < d → d ∣ m → d ∣ n → ¬m
.Coprime n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
· 使用定理 `Int.dvd_of_emod_eq_zero`：∀ {a b : ℤ}, b % a = 0 → a ∣ b
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `Int.dvd_self_sub_of_emod_eq`：∀ {a b c : ℤ}, a % b = c → b ∣ a - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Int.sq_ne_two_mod_four`：Int.sq_ne_two_mod_four (z : Int) : z * z % 4 != 
2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 41 条，此处仅展示前 30 条）
-/
theorem even_odd_of_coprime (hc : Int.gcd x y = 1) :
    x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  -- x even, y even
  · exfalso
    apply Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) _ _ hc
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hx
    · apply Int.natCast_dvd.1
      apply Int.dvd_of_emod_eq_zero hy
  -- x even, y odd
  · left
    exact ⟨hx, hy⟩
  -- x odd, y even
  · right
    exact ⟨hx, hy⟩
  -- x odd, y odd
  · exfalso
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0 * 2 + 1 ∧ y = y0 * 2 + 1 := by
      obtain ⟨x0, hx2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hx)
      obtain ⟨y0, hy2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hy)
      rw [sub_eq_iff_eq_add] at hx2 hy2
      exact ⟨x0, y0, hx2, hy2⟩
    apply Int.sq_ne_two_mod_four z
    rw [show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2 by
        rw [← h.eq]
        ring]
    simp only [Int.add_emod, Int.mul_emod_right, zero_add]
    decide
/-
**PythagoreanTriple.gcd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：gcd_dvd : (Int.gcd x y : Int) ∣ z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.gcd_eq_zero_iff`：∀ {a b : ℤ}, a.gcd b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Int.exists_gcd_one'`：exists_gcd_one' {m n : Int} (H : 0 < gcd m n) : exi
sts (g : Nat) (m' n' : Int), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Int.gcd_mul_right`：∀ (m n k : ℤ), (m * n).gcd (k * n) = m.gcd k * n.natA
bs
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.pow_dvd_pow_iff`：∀ {a b : ℤ} {n : ℕ}, n ≠ 0 → (a ^ n ∣ b ^ n ↔ a ∣ b
)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
（共 50 条，此处仅展示前 30 条）
-/
theorem gcd_dvd : (Int.gcd x y : ℤ) ∣ z := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simp [h0, hz]
  obtain ⟨k, x0, y0, _, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  rw [Int.gcd_mul_right, h2, Int.natAbs_natCast, one_mul]
  rw [← Int.pow_dvd_pow_iff two_ne_zero, sq z, ← h.eq]
  rw [(by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = (k : ℤ) ^ 2 * (x0 * x0 + y0 * y0))]
  exact dvd_mul_right _ _
/-
**PythagoreanTriple.normalize** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：normalize : PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int
.gcd x y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.gcd_eq_zero_iff`：∀ {a b : ℤ}, a.gcd b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Int.gcd_self`：∀ {a : ℤ}, a.gcd a = a.natAbs
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `PythagoreanTriple.zero`：PythagoreanTriple.zero : PythagoreanTriple 0 0 0
· 使用定理 `PythagoreanTriple.gcd_dvd`：gcd_dvd : (Int.gcd x y : Int) ∣ z
· 使用定理 `Int.exists_gcd_one'`：exists_gcd_one' {m n : Int} (H : 0 < gcd m n) : exi
sts (g : Nat) (m' n' : Int), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Int.gcd_mul_right`：∀ (m n k : ℤ), (m * n).gcd (k * n) = m.gcd k * n.natA
bs
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.mul_ediv_cancel`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a * b / b = a
· 使用定理 `Int.mul_ediv_cancel_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → a * b / a = b
· 使用定理 `PythagoreanTriple.mul_iff`：mul_iff (k : Int) (hk : k != 0) : Pythagorean
Triple (k * x) (k * y) (k * z) ↔ PythagoreanTriple x y z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem normalize : PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int.gcd x y) := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    have hz : z = 0 := by
      simpa only [PythagoreanTriple, hx, hy, add_zero, zero_eq_mul, mul_zero,
        or_self_iff] using h
    simpa [h0, hx, hy, hz] using zero
  rcases h.gcd_dvd with ⟨z0, rfl⟩
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) (x0 y0 : _), 0 < k ∧ Int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
  have hk : (k : ℤ) ≠ 0 := by
    norm_cast
    rwa [pos_iff_ne_zero] at k0
  rw [Int.gcd_mul_right, h2, Int.natAbs_natCast, one_mul] at h ⊢
  rw [mul_comm x0, mul_comm y0, mul_iff k hk] at h
  rwa [Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel _ hk, Int.mul_ediv_cancel_left _ hk]
/-
**PythagoreanTriple.isClassified_of_isPrimitiveClassified** 是 Mathlib 中的一个定理，位于命
名空间 `PythagoreanTriple`。
形式化陈述：isClassified_of_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.I
sClassified
参数：hp : h.IsPrimitiveClassified。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isClassified_of_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.IsClassified := by
  obtain ⟨m, n, H⟩ := hp
  use 1, m, n
  lia
/-
**PythagoreanTriple.isClassified_of_normalize_isPrimitiveClassified** 是 Mathlib 
中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：isClassified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimit
iveClassified) : h.IsClassified
参数：hc : h.normalize.IsPrimitiveClassified。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.normalize`：normalize : PythagoreanTriple (x / Int.gcd 
x y) (y / Int.gcd x y) (z / Int.gcd x y)
· 使用定理 `PythagoreanTriple.mul`：mul (h : PythagoreanTriple x y z) (k : Int) : Pyt
hagoreanTriple (k * x) (k * y) (k * z)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_ediv_cancel'`：∀ {a b : ℤ}, a ∣ b → a * (b / a) = b
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
· 使用定理 `PythagoreanTriple.gcd_dvd`：gcd_dvd : (Int.gcd x y : Int) ∣ z
· 使用定理 `PythagoreanTriple.mul_isClassified`：mul_isClassified (k : Int) (hc : h.I
sClassified) : (h.mul k).IsClassified
· 使用定理 `PythagoreanTriple.isClassified_of_isPrimitiveClassified`：isClassified_of
_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.IsClassified
-/
theorem isClassified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimitiveClassified) :
    h.IsClassified := by
  convert!
    h.normalize.mul_isClassified (Int.gcd x y)
      (isClassified_of_isPrimitiveClassified h.normalize hc) <;>
    rw [Int.mul_ediv_cancel']
  · exact Int.gcd_dvd_left ..
  · exact Int.gcd_dvd_right ..
  · exact h.gcd_dvd
/-
**PythagoreanTriple.ne_zero_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTri
ple`。
形式化陈述：ne_zero_of_coprime (hc : Int.gcd x y = 1) : z != 0
参数：hc : Int.gcd x y = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Int.ne_zero_of_gcd`：ne_zero_of_gcd {x y : Int} (hc : gcd x y != 0) : x !
= 0 ∨ y != 0
· 使用定理 `lt_add_of_pos_of_le`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddRightStrictMono α] {a b c : α},   0 < a → b ≤ c → b < a + c
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
· 使用定理 `sq_pos_of_ne_zero`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [ExistsAddOfLE R] {a : R},   a ≠ 0 → 0 < a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `lt_add_of_le_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → 0 < a → b < c + a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_false`：isNat_lt_false [Semiring α] [Partia
lOrder α] [IsOrderedRing α] {a b : α} {a' b' : Nat} (ha : IsNat a a') (hb : IsNa
t b b') (h : Nat.ble b' a…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
-/
theorem ne_zero_of_coprime (hc : Int.gcd x y = 1) : z ≠ 0 := by
  suffices 0 < z * z by
    rintro rfl
    norm_num at this
  rw [← h.eq, ← sq, ← sq]
  have hc' : Int.gcd x y ≠ 0 := by
    rw [hc]
    exact one_ne_zero
  rcases Int.ne_zero_of_gcd hc' with hxz | hyz
  · apply lt_add_of_pos_of_le (sq_pos_of_ne_zero hxz) (sq_nonneg y)
  · apply lt_add_of_le_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hyz)
/-
**PythagoreanTriple.isPrimitiveClassified_of_coprime_of_zero_left** 是 Mathlib 中的
一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：isPrimitiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx :
 x = 0) : h.IsPrimitiveClassified
参数：hc : Int.gcd x y = 1；hx : x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `Int.gcd_zero_right`：∀ (a : ℤ), a.gcd 0 = a.natAbs
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Int.gcd_zero_left`：∀ (a : ℤ), Int.gcd 0 a = a.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPrimitiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx : x = 0) :
    h.IsPrimitiveClassified := by
  subst x
  change Nat.gcd 0 (Int.natAbs y) = 1 at hc
  rw [Nat.gcd_zero_left (Int.natAbs y)] at hc
  rcases Int.natAbs_eq y with hy | hy
  · use 1, 0
    rw [hy, hc, Int.gcd_zero_right]
    decide
  · use 0, 1
    rw [hy, hc, Int.gcd_zero_left]
    decide
/-
**PythagoreanTriple.coprime_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTri
ple`。
形式化陈述：coprime_of_coprime (hc : Int.gcd x y = 1) : Int.gcd y z = 1
参数：hc : Int.gcd x y = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Int.Prime.dvd_natAbs_of_coe_dvd_sq`：∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℤ), 
↑p ∣ k ^ 2 → p ∣ k.natAbs
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
-/
theorem coprime_of_coprime (hc : Int.gcd x y = 1) : Int.gcd y z = 1 := by
  by_contra H
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  apply hp.not_dvd_one
  rw [← hc]
  apply Nat.dvd_gcd (Int.Prime.dvd_natAbs_of_coe_dvd_sq hp _ _) hpy
  rw [sq, eq_sub_of_add_eq h]
  rw [← Int.natCast_dvd] at hpy hpz
  exact dvd_sub (hpz.mul_right _) (hpy.mul_right _)

end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of Pythagorean triples, we will use a parametrization of the unit circle.
-/


variable {K : Type*} [Field K]

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- A parameterization of the unit circle that is useful for classifying Pythagorean triples.
(To be applied in the case where `K = ℚ`.) -/
/-
**circleEquivGen** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：circleEquivGen (hk : forall x : K, 1 + x ^ 2 != 0) : K ≃ { p : K × K // p.
1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 } where toFun x
参数：hk : forall x : K, 1 + x ^ 2 != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A parameterization of the unit circle that is useful for classifying Pythagorean
 triples.
(To be applied in the case where `K = ℚ`.)
-/
def circleEquivGen (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) :
    K ≃ { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 } where
  toFun x :=
    ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by field [hk x], by
      simp only [Ne, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by
    have h2 : (1 + 1 : K) = 2 := by norm_num
    have h3 : (2 : K) ≠ 0 := by
      convert! hk 1
      rw [one_pow 2, h2]
    simp [field, hk x, h2, add_assoc, add_comm, add_sub_cancel, mul_comm]
  right_inv := fun ⟨⟨x, y⟩, hxy, hy⟩ => by
    change x ^ 2 + y ^ 2 = 1 at hxy
    have h2 : y + 1 ≠ 0 := mt eq_neg_of_add_eq_zero_left hy
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1) := by
      rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm]
      ring
    have h4 : (2 : K) ≠ 0 := by
      convert! hk 1
      rw [one_pow 2]
      ring
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]
    constructor
    · simp [field, h3]
    · grind

@[simp]
/-
**circleEquivGen_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleEquivGen_apply (hk : forall x : K, 1 + x ^ 2 != 0) (x : K) : (circle
EquivGen hk x : K × K) = ⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩
参数：hk : forall x : K, 1 + x ^ 2 != 0；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem circleEquivGen_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) (x : K) :
    (circleEquivGen hk x : K × K) = ⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩ :=
  rfl

@[simp]
/-
**circleEquivGen_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleEquivGen_symm_apply (hk : forall x : K, 1 + x ^ 2 != 0) (v : { p : K
 × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 != -1 }) : (circleEquivGen hk).symm v = (v :
 K × K).1 / ((v : K × K).2 + 1)
参数：hk : forall x : K, 1 + x ^ 2 != 0；v : { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ 
p.2 != -1 }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem circleEquivGen_symm_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0)
    (v : { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 }) :
    (circleEquivGen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) :=
  rfl

end circleEquivGen

/-
**coprime_sq_sub_sq_add_of_even_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_sq_add_of_even_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have h2m : (p : ℤ) ∣ 2 * m ^ 2 := by
    convert! dvd_add hp2 hp1 using 1
    ring
  have h2n : (p : ℤ) ∣ 2 * n ^ 2 := by
    convert! dvd_sub hp2 hp1 using 1
    ring
  have hmc : p = 2 ∨ p ∣ Int.natAbs m := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2m
  have hnc : p = 2 ∨ p ∣ Int.natAbs n := prime_two_or_dvd_of_dvd_two_mul_pow_self_two hp h2n
  by_cases h2 : p = 2
  · have h3 : (m ^ 2 + n ^ 2) % 2 = 1 := by
      simp only [sq, Int.add_emod, Int.mul_emod, hm, hn, dvd_refl, Int.emod_emod_of_dvd]
      decide
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      rwa [h2] at hp2
    rw [h4] at h3
    exact zero_ne_one h3
  · apply hp.not_dvd_one
    rw [← h]
    exact Nat.dvd_gcd (Or.resolve_left hmc h2) (Or.resolve_left hnc h2)
/-
**coprime_sq_sub_sq_add_of_odd_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_sq_add_of_odd_even {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by
  rw [Int.gcd, ← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2), add_comm]
  apply coprime_sq_sub_sq_add_of_even_odd _ hn hm; rwa [Int.gcd_comm]
/-
**coprime_sq_sub_mul_of_even_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_mul_of_even_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  by_contra H
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp H
  rw [← Int.natCast_dvd] at hp1 hp2
  have hnp : ¬(p : ℤ) ∣ Int.gcd m n := by
    rw [h]
    norm_cast
    exact mt Nat.dvd_one.mp (Nat.Prime.ne_one hp)
  rcases Int.Prime.dvd_mul hp hp2 with hp2m | hpn
  · rw [Int.natAbs_mul] at hp2m
    rcases (Nat.Prime.dvd_mul hp).mp hp2m with hp2 | hpm
    · have hp2' : p = 2 := (Nat.le_of_dvd zero_lt_two hp2).antisymm hp.two_le
      revert hp1
      rw [hp2']
      apply mt Int.emod_eq_zero_of_dvd
      simp only [sq, Nat.cast_ofNat, Int.sub_emod, Int.mul_emod, hm, hn,
        mul_zero, EuclideanDomain.zero_mod, mul_one, zero_sub]
      decide
    apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpm)) hnp
    apply or_self_iff.mp
    apply Int.Prime.dvd_mul' hp
    rw [(by ring : n * n = -(m ^ 2 - n ^ 2) + m * m)]
    exact hp1.neg_right.add ((Int.natCast_dvd.2 hpm).mul_right _)
  rw [Int.gcd_comm] at hnp
  apply mt (Int.dvd_coe_gcd (Int.natCast_dvd.mpr hpn)) hnp
  apply or_self_iff.mp
  apply Int.Prime.dvd_mul' hp
  rw [(by ring : m * m = m ^ 2 - n ^ 2 + n * n)]
  apply dvd_add hp1
  exact (Int.natCast_dvd.mpr hpn).mul_right n
/-
**coprime_sq_sub_mul_of_odd_even** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_mul_of_odd_even {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 0) : Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  rw [Int.gcd, ← Int.natAbs_neg (m ^ 2 - n ^ 2)]
  rw [(by ring : 2 * m * n = 2 * n * m), (by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2)]
  apply coprime_sq_sub_mul_of_even_odd _ hn hm; rwa [Int.gcd_comm]
/-
**coprime_sq_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_mul {m n : ℤ} (h : Int.gcd m n = 1)
    (hmn : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  rcases hmn with h1 | h2
  · exact coprime_sq_sub_mul_of_even_odd h h1.left h1.right
  · exact coprime_sq_sub_mul_of_odd_even h h2.left h2.right
/-
**coprime_sq_sub_sq_sum_of_odd_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coprime_sq_sub_sq_sum_of_odd_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 1)
    (hn : n % 2 = 1) :
    2 ∣ m ^ 2 + n ^ 2 ∧
      2 ∣ m ^ 2 - n ^ 2 ∧
        (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 := by
  obtain ⟨m0, hm2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
  obtain ⟨n0, hn2⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
  rw [sub_eq_iff_eq_add] at hm2 hn2
  subst m
  subst n
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1) := by
    ring
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)) := by ring
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0 := by
    rw [h2, Int.mul_ediv_cancel_left, Int.mul_emod_right]
    decide
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, ?_⟩
  have h20 : (2 : ℤ) ≠ 0 := by decide
  rw [h1, h2, Int.mul_ediv_cancel_left _ h20, Int.mul_ediv_cancel_left _ h20]
  by_contra h4
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h4
  apply hp.not_dvd_one
  rw [← h]
  rw [← Int.natCast_dvd] at hp1 hp2
  apply Nat.dvd_gcd
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_add hp1 hp2
    ring
  · apply Int.Prime.dvd_natAbs_of_coe_dvd_sq hp
    convert! dvd_sub hp2 hp1
    ring

namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

/-
**PythagoreanTriple.isPrimitiveClassified_aux** 是 Mathlib 中的一个定理，位于命名空间 `Pythago
reanTriple`。
形式化陈述：isPrimitiveClassified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : Int} (
hm2n2 : 0 < m ^ 2 + n ^ 2) (hv2 : (x : Rat) / z = 2 * m * n / ((m : Rat) ^ 2 + (
n : Rat) ^ 2)) (hw2 : (y : Rat) / z = ((m : Rat) ^ 2 - (n : Rat) ^ 2) / ((m : Ra
t) ^ 2 + (n : Rat) ^ 2)) (H : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) (co :
 Int.gcd m n = 1) (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.IsPri
mitiveClassified
参数：hc : x.gcd y = 1；hzpos : 0 < z；hm2n2 : 0 < m ^ 2 + n ^ 2；hv2 : (x : Rat) / z 
= 2 * m * n / ((m : Rat) ^ 2 + (n : Rat) ^ 2)；hw2 : (y : Rat) / z = ((m : Rat) ^
 2 - (n : Rat) ^ 2) / ((m : Rat) ^ 2 + (n : Rat) ^ 2)；H : Int.gcd (m ^ 2 - n ^ 2
) (m ^ 2 + n ^ 2) = 1；co : Int.gcd m n = 1；pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 
1 ∧ n % 2 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Rat.div_int_inj`：div_int_inj {a b c d : Int} (hb0 : 0 < b) (hd0 : 0 < d)
 (h1 : Nat.Coprime a.natAbs b.natAbs) (h2 : Nat.Coprime c.natAbs d.natAbs) (h : 
(a : …
· 使用定理 `PythagoreanTriple.coprime_of_coprime`：coprime_of_coprime (hc : Int.gcd x
 y = 1) : Int.gcd y z = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.intCast_inj`：∀ {a b : ℤ}, ↑a = ↑b ↔ a = b
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isPrimitiveClassified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : ℤ}
    (hm2n2 : 0 < m ^ 2 + n ^ 2) (hv2 : (x : ℚ) / z = 2 * m * n / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (hw2 : (y : ℚ) / z = ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (H : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) (co : Int.gcd m n = 1)
    (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.IsPrimitiveClassified := by
  have hz : z ≠ 0 := ne_of_gt hzpos
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2 := by
    apply Rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H
    rw [hw2]
    norm_cast
  use m, n
  apply And.intro _ (And.intro co pp)
  right
  refine ⟨?_, h2.left⟩
  rw [← Rat.intCast_inj, ← div_left_inj' (mt Rat.intCast_inj.mp hz), hv2, h2.right]
  norm_cast
/-
**PythagoreanTriple.isPrimitiveClassified_of_coprime_of_odd_of_pos** 是 Mathlib 中
的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：isPrimitiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo
 : y % 2 = 1) (hzpos : 0 < z) : h.IsPrimitiveClassified
参数：hc : Int.gcd x y = 1；hyo : y % 2 = 1；hzpos : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.isPrimitiveClassified_of_coprime_of_zero_left`：isPrimi
tiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx : x = 0) : h.I
sPrimitiveClassified
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
（共 138 条，此处仅展示前 30 条）
-/
theorem isPrimitiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo : y % 2 = 1)
    (hzpos : 0 < z) : h.IsPrimitiveClassified := by
  by_cases h0 : x = 0
  · exact h.isPrimitiveClassified_of_coprime_of_zero_left hc h0
  let v := (x : ℚ) / z
  let w := (y : ℚ) / z
  have hq : v ^ 2 + w ^ 2 = 1 := by
    simp [field, v, w]
    simp only [sq]
    norm_cast
  have hvz : v ≠ 0 := by simp [field, v, -mul_eq_zero, -div_eq_zero_iff, h0]
  have hw1 : w ≠ -1 := by
    contrapose hvz with hw1
    rw [hw1, neg_sq, one_pow, add_eq_right] at hq
    exact eq_zero_of_pow_eq_zero hq
  have hQ : ∀ x : ℚ, 1 + x ^ 2 ≠ 0 := by
    intro q
    apply ne_of_gt
    exact lt_add_of_pos_of_le zero_lt_one (sq_nonneg q)
  have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ { p : ℚ × ℚ | p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 } := ⟨hq, hw1⟩
  let q := (circleEquivGen hQ).symm ⟨⟨v, w⟩, hp⟩
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2) := by
    apply Prod.mk.inj
    exact congr_arg Subtype.val ((circleEquivGen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm
  let m := (q.den : ℤ)
  let n := q.num
  have hm0 : m ≠ 0 := by
    -- Added to adapt to https://github.com/leanprover/lean4/pull/2734.
    -- Without `unfold`, `norm_cast` can't see the coercion.
    -- One might try `zeta := true` in `Tactic.NormCast.derive`,
    -- but that seems to break many other things.
    unfold m
    norm_cast
    apply Rat.den_nz q
  have hq2 : q = n / m := (Rat.num_div_den q).symm
  have hm2n2 : 0 < m ^ 2 + n ^ 2 := by positivity
  have hm2n20 : (m ^ 2 + n ^ 2 : ℚ) ≠ 0 := by positivity
  have hw2 : w = ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
    calc
      w = (1 - q ^ 2) / (1 + q ^ 2) := by apply ht4.2
      _ = (1 - (↑n / ↑m) ^ 2) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hv2 : v = 2 * m * n / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) := by
    calc
      v = 2 * q / (1 + q ^ 2) := by apply ht4.1
      _ = 2 * (n / m) / (1 + (↑n / ↑m) ^ 2) := by rw [hq2]
      _ = _ := by field
  have hnmcp : Int.gcd n m = 1 := q.reduced
  have hmncp : Int.gcd m n = 1 := by
    rw [Int.gcd_comm]
    exact hnmcp
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2 <;>
    rcases Int.emod_two_eq_zero_or_one n with hn2 | hn2
  · -- m even, n even
    exfalso
    have h1 : 2 ∣ (Int.gcd n m : ℤ) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hn2) (Int.dvd_of_emod_eq_zero hm2)
    lia
  · -- m even, n odd
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_left
      exact And.intro hm2 hn2
    · apply coprime_sq_sub_sq_add_of_even_odd hmncp hm2 hn2
  · -- m odd, n even
    apply h.isPrimitiveClassified_aux hc hzpos hm2n2 hv2 hw2 _ hmncp
    · apply Or.intro_right
      exact And.intro hm2 hn2
    apply coprime_sq_sub_sq_add_of_odd_even hmncp hm2 hn2
  · -- m odd, n odd
    exfalso
    have h1 :
      2 ∣ m ^ 2 + n ^ 2 ∧
        2 ∣ m ^ 2 - n ^ 2 ∧
          (m ^ 2 - n ^ 2) / 2 % 2 = 0 ∧ Int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
      coprime_sq_sub_sq_sum_of_odd_odd hmncp hm2 hn2
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2 := by
      apply Rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2
      · change w = _
        rw [← Rat.divInt_eq_div, ← Rat.divInt_mul_right (by simp : (2 : ℤ) ≠ 0)]
        rw [Int.ediv_mul_cancel h1.1, Int.ediv_mul_cancel h1.2.1, hw2, Rat.divInt_eq_div]
        norm_cast
      · lia
    norm_num [h2.1, h1.2.2.1] at hyo
/-
**PythagoreanTriple.isPrimitiveClassified_of_coprime_of_pos** 是 Mathlib 中的一个定理，位
于命名空间 `PythagoreanTriple`。
形式化陈述：isPrimitiveClassified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 
< z) : h.IsPrimitiveClassified
参数：hc : Int.gcd x y = 1；hzpos : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.even_odd_of_coprime`：even_odd_of_coprime (hc : Int.gcd
 x y = 1) : x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0
· 使用定理 `PythagoreanTriple.isPrimitiveClassified_of_coprime_of_odd_of_pos`：isPrim
itiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo : y % 2 = 1
) (hzpos : 0 < z) : h.IsPrimitiveClassified
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PythagoreanTriple.symm`：symm (h : PythagoreanTriple x y z) : Pythagorean
Triple y x z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.gcd_comm`：∀ (a b : ℤ), a.gcd b = b.gcd a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
theorem isPrimitiveClassified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 < z) :
    h.IsPrimitiveClassified := by
  rcases h.even_odd_of_coprime hc with h1 | h2
  · exact h.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h1.right hzpos
  rw [Int.gcd_comm] at hc
  obtain ⟨m, n, H⟩ := h.symm.isPrimitiveClassified_of_coprime_of_odd_of_pos hc h2.left hzpos
  use m, n; tauto
/-
**PythagoreanTriple.isPrimitiveClassified_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `
PythagoreanTriple`。
形式化陈述：isPrimitiveClassified_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveCla
ssified
参数：hc : Int.gcd x y = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.isPrimitiveClassified_of_coprime_of_pos`：isPrimitiveCl
assified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 < z) : h.IsPrimitiv
eClassified
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, a ≤ -b ↔ b ≤ -a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `PythagoreanTriple.ne_zero_of_coprime`：ne_zero_of_coprime (hc : Int.gcd x
 y = 1) : z != 0
-/
theorem isPrimitiveClassified_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified := by
  by_cases! hz : 0 < z
  · exact h.isPrimitiveClassified_of_coprime_of_pos hc hz
  have h' : PythagoreanTriple x y (-z) := by simpa [PythagoreanTriple, neg_mul_neg] using h.eq
  apply h'.isPrimitiveClassified_of_coprime_of_pos hc
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm
  exact le_neg.mp hz
/-
**PythagoreanTriple.classified** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`。
形式化陈述：classified : h.IsClassified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.gcd_eq_zero_iff`：∀ {a b : ℤ}, a.gcd b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Int.gcd_zero`：∀ {a : ℤ}, a.gcd 0 = a.natAbs
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `PythagoreanTriple.isClassified_of_normalize_isPrimitiveClassified`：isCla
ssified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimitiveClassifi
ed) : h.IsClassified
· 使用定理 `PythagoreanTriple.isPrimitiveClassified_of_coprime`：isPrimitiveClassifie
d_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified
· 使用定理 `PythagoreanTriple.normalize`：normalize : PythagoreanTriple (x / Int.gcd 
x y) (y / Int.gcd x y) (z / Int.gcd x y)
· 使用定理 `Int.gcd_div_gcd_div_gcd`：∀ {i j : ℤ}, 0 < i.gcd j → (i / ↑(i.gcd j)).gcd
 (j / ↑(i.gcd j)) = 1
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem classified : h.IsClassified := by
  by_cases h0 : Int.gcd x y = 0
  · obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0
    use 0, 1, 0
    simp [hx, hy]
  apply h.isClassified_of_normalize_isPrimitiveClassified
  apply h.normalize.isPrimitiveClassified_of_coprime
  apply Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero h0)
/-
**PythagoreanTriple.coprime_classification** 是 Mathlib 中的一个定理，位于命名空间 `Pythagorea
nTriple`。
形式化陈述：coprime_classification : PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔ exist
s m n, (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
 (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧ Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n %
 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PythagoreanTriple.isPrimitiveClassified_of_coprime`：isPrimitiveClassifie
d_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 60 条，此处仅展示前 30 条）
-/
theorem coprime_classification :
    PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
      ∃ m n,
        (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
          (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  constructor
  · intro h
    obtain ⟨m, n, H⟩ := h.left.isPrimitiveClassified_of_coprime h.right
    use m, n
    rcases H with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, co, pp⟩
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq, ← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, co, pp⟩
      have : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
        rw [sq, ← h.left.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · delta PythagoreanTriple
    rintro ⟨m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl, co, pp⟩ <;>
      first
      | constructor; ring; exact coprime_sq_sub_mul co pp
      | constructor; ring; rw [Int.gcd_comm]; exact coprime_sq_sub_mul co pp

/-- By assuming `x` is odd and `z` is positive we get a slightly more precise classification of
the Pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`. -/
/-
**PythagoreanTriple.coprime_classification'** 是 Mathlib 中的一个定理，位于命名空间 `Pythagore
anTriple`。
形式化陈述：coprime_classification' {x y z : Int} (h : PythagoreanTriple x y z) (h_cop
rime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) : exists m n, x =
 m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 ∧ Int.gcd m n = 1 ∧ (m % 2 = 
0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 <= m
参数：h : PythagoreanTriple x y z；h_coprime : Int.gcd x y = 1；h_parity : x % 2 = 1；
h_pos : 0 < z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PythagoreanTriple.coprime_classification`：coprime_classification : Pytha
goreanTriple x y z ∧ Int.gcd x y = 1 ↔ exists m n, (x = m ^ 2 - n ^ 2 ∧ y = 2 * 
m * n ∨ x = 2 * m * n ∧ y = m …
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `imp_false`：∀ {a : Prop}, a → False ↔ ¬a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Int.mul_emod_right`：∀ (a b : ℤ), a * b % a = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
By assuming `x` is odd and `z` is positive we get a slightly more precise classi
fication of
the Pythagorean triple `x ^ 2 + y ^ 2 = z ^ 2`.
-/
theorem coprime_classification' {x y z : ℤ} (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
    ∃ m n,
      x = m ^ 2 - n ^ 2 ∧
        y = 2 * m * n ∧
          z = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m := by
  obtain ⟨m, n, ht1, ht2, ht3, ht4⟩ :=
    PythagoreanTriple.coprime_classification.mp (And.intro h h_coprime)
  rcases le_or_gt 0 m with hm | hm
  · use m, n
    rcases ht1 with h_odd | h_even
    · apply And.intro h_odd.1
      apply And.intro h_odd.2
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos (And.intro ht3 (And.intro ht4 hm))
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc, Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity
  · use -m, -n
    rcases ht1 with h_odd | h_even
    · rw [neg_sq m]
      rw [neg_sq n]
      apply And.intro h_odd.1
      constructor
      · rw [h_odd.2]
        ring
      rcases ht2 with h_pos | h_neg
      · apply And.intro h_pos
        constructor
        · delta Int.gcd
          rw [Int.natAbs_neg, Int.natAbs_neg]
          exact ht3
        · rw [Int.neg_emod_two, Int.neg_emod_two]
          apply And.intro ht4
          lia
      · exfalso
        revert h_pos
        rw [h_neg]
        exact imp_false.mpr (not_lt.mpr (neg_nonpos.mpr (by positivity)))
    exfalso
    rcases h_even with ⟨rfl, -⟩
    rw [mul_assoc, Int.mul_emod_right] at h_parity
    exact zero_ne_one h_parity

/-- **Formula for Pythagorean Triples** -/
/-
**PythagoreanTriple.classification** 是 Mathlib 中的一个定理，位于命名空间 `PythagoreanTriple`
。
形式化陈述：classification : PythagoreanTriple x y z ↔ exists k m n, (x = k * (m ^ 2 -
 n ^ 2) ∧ y = k * (2 * m * n) ∨ x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
 (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PythagoreanTriple.classified`：classified : h.IsClassified
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PythagoreanTriple.eq`：eq (h : PythagoreanTriple x y z) : x * x + y * y =
 z * z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
**Formula for Pythagorean Triples**
-/
theorem classification :
    PythagoreanTriple x y z ↔
      ∃ k m n,
        (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
            x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
          (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by
  constructor
  · intro h
    obtain ⟨k, m, n, H⟩ := h.classified
    use k, m, n
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq, ← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
    · refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2 := by
        rw [sq, ← h.eq]
        ring
      simpa using eq_or_eq_neg_of_sq_eq_sq _ _ this
  · rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩ <;> delta PythagoreanTriple <;> ring

end PythagoreanTriple

