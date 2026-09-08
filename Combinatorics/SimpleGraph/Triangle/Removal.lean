/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
public import Mathlib.Data.Finset.CastCard

/-!
# Triangle removal lemma

In this file, we prove the triangle removal lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section

open Finset Fintype Nat SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]
  {s t : Finset α} {P : Finpartition (univ : Finset α)} {ε : ℝ}

namespace SimpleGraph

/-- An explicit form for the constant in the triangle removal lemma.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exponential. This means
`triangleRemovalBound` is in practice absolutely tiny.

This definition is meant to be used for small values of `ε`, and in particular is junk for values
of `ε` greater than or equal to `1`. The junk value is chosen to be positive, so that
`0 < ε → 0 < triangleRemovalBound ε` regardless of whether `ε < 1` or not. -/
/-
**SimpleGraph.triangleRemovalBound** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：triangleRemovalBound (ε : Real) : Real
参数：ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An explicit form for the constant in the triangle removal lemma.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exp
onential. This means
`triangleRemovalBound` is in practice absolutely tiny.

This definition is meant to be used for small values of `ε`, and in particular i
s junk for values
of `ε` greater than or equal to `1`. The junk value is chosen to be positive, so
 that
`0 < ε → 0 < triangleRemovalBound ε` regardless of whether `ε < 1` or not.
-/
noncomputable def triangleRemovalBound (ε : ℝ) : ℝ :=
  min (2 * ⌈4 / ε⌉₊ ^ 3)⁻¹ ((1 - min 1 ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3)
/-
**SimpleGraph.triangleRemovalBound_pos** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：triangleRemovalBound_pos (hε : 0 < ε) : 0 < triangleRemovalBound ε
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 77 条，此处仅展示前 30 条）
-/
lemma triangleRemovalBound_pos (hε : 0 < ε) : 0 < triangleRemovalBound ε := by
  have : 0 < 1 - min 1 ε / 4 := by have := min_le_left 1 ε; linarith
  unfold triangleRemovalBound
  positivity
/-
**SimpleGraph.triangleRemovalBound_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：triangleRemovalBound_nonpos (hε : ε <= 0) : triangleRemovalBound ε <= 0
参数：hε : ε <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.triangleRemovalBound.eq_1`：∀ (ε : ℝ),   SimpleGraph.triangle
RemovalBound ε =     min (2 * ↑⌈4 / ε⌉₊ ^ 3)⁻¹ ((1 - min 1 ε / 4) * (ε / (16 * ↑
(SzemerediRegularity.bound …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ceil_eq_zero`：ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a <= 0
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
-/
lemma triangleRemovalBound_nonpos (hε : ε ≤ 0) : triangleRemovalBound ε ≤ 0 := by
  rw [triangleRemovalBound, ceil_eq_zero.2 (div_nonpos_of_nonneg_of_nonpos _ hε)] <;> simp
/-
**SimpleGraph.triangleRemovalBound_mul_cube_lt** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：triangleRemovalBound_mul_cube_lt (hε : 0 < ε) : triangleRemovalBound ε * ⌈
4 / ε⌉₊ ^ 3 < 1
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.Positivity.nat_ceil_pos`：nat_ceil_pos [Semiring α] [LinearO
rder α] [FloorSemiring α] {a : α} : 0 < a -> 0 < ⌈a⌉₊
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma triangleRemovalBound_mul_cube_lt (hε : 0 < ε) :
    triangleRemovalBound ε * ⌈4 / ε⌉₊ ^ 3 < 1 := by
  calc
    _ ≤ (2 * ⌈4 / ε⌉₊ ^ 3 : ℝ)⁻¹ * ↑⌈4 / ε⌉₊ ^ 3 := by gcongr; exact min_le_left _ _
    _ = 2⁻¹ := by rw [mul_inv, inv_mul_cancel_right₀]; positivity
    _ < 1 := by norm_num
/-
**SimpleGraph.triangleRemovalBound_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：triangleRemovalBound_le (hε₁ : ε <= 1) : triangleRemovalBound ε <= (1 - ε 
/ 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3
参数：hε₁ : ε <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
lemma triangleRemovalBound_le (hε₁ : ε ≤ 1) :
    triangleRemovalBound ε ≤ (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 := by
  simp [triangleRemovalBound, hε₁]
/-
**SimpleGraph.aux** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) := by
  rw [mul_assoc, two_mul, ← add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    mod_add_div n k, add_comm, add_lt_add_iff_right]
  apply (mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)
/-
**SimpleGraph.card_bound** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_bound (hP₁ : P.IsEquipartition) (hP₃ : #P.parts ≤ bound (ε / 8) ⌈4 / ε⌉₊)
    (hX : s ∈ P.parts) : card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊ : ℝ) ≤ #s := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ ≤ card α / (2 * #P.parts : ℝ) := by gcongr
    _ ≤ ↑(card α / #P.parts) :=
      (div_le_iff₀' (by positivity)).2 <| mod_cast (aux ‹_› P.card_parts_le_card).le
    _ ≤ (#s : ℝ) := mod_cast hP₁.average_le_card_part hX
/-
**SimpleGraph.triangle_removal_aux** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma triangle_removal_aux (hε : 0 < ε) (hε₁ : ε ≤ 1) (hP₁ : P.IsEquipartition)
    (hP₃ : #P.parts ≤ bound (ε / 8) ⌈4 / ε⌉₊)
    (ht : t ∈ (G.regularityReduced P (ε / 8) (ε / 4)).cliqueFinset 3) :
    triangleRemovalBound ε * card α ^ 3 ≤ #(G.cliqueFinset 3) := by
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
  obtain ⟨x, y, z, ⟨-, s, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩,
                   ⟨-, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩,
                   ⟨-, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩, rfl⟩ := ht
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩)
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩)
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩)
  have dXY := P.disjoint hX hY nXY
  have dXZ := P.disjoint hX hZ nXZ
  have dYZ := P.disjoint hY hZ nYZ
  have that : 2 * (ε / 8) = ε / 4 := by ring
  have : 0 ≤ 1 - 2 * (ε / 8) := by
    have : ε / 4 ≤ 1 := ‹ε / 4 ≤ _›.trans (by exact mod_cast G.edgeDensity_le_one _ _); linarith
  calc
    _ ≤ (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 * card α ^ 3 := by
      gcongr; exact triangleRemovalBound_le hε₁
    _ = (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) *
          (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) := by
      ring
    _ ≤ (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * #s * #Y * #Z := by
      gcongr <;> exact card_bound hP₁ hP₃ ‹_›
    _ ≤ _ :=
      triangle_counting G (by rwa [that]) uXY dXY (by rwa [that]) uXZ dXZ (by rwa [that]) uYZ dYZ
/-
**SimpleGraph.regularityReduced_edges_card_aux** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：regularityReduced_edges_card_aux [Nonempty α] (hε : 0 < ε) (hP : P.IsEquip
artition) (hPε : P.IsUniform G (ε / 8)) (hP' : 4 / ε <= #P.parts) : 2 * (#G.edge
Finset - #(G.regularityReduced P (ε / 8) (ε / 4)).edgeFinset : Real) < 2 * ε * (
card α ^ 2 : Nat)
参数：hε : 0 < ε；hP : P.IsEquipartition；hPε : P.IsUniform G (ε / 8)；hP' : 4 / ε <= 
#P.parts。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `Finset.filter_and_not`：filter_and_not (s : Finset α) (p q : α -> Prop) [
DecidablePred p] [DecidablePred q] : s.filter (fun a => p a ∧ ¬ q a) = s.filter 
p \ s.filte…
· 使用引理 `Finset.cast_card_sdiff`：cast_card_sdiff (h : s subseteq t) : (#(t \ s) :
 R) = #t - #s
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用引理 `SimpleGraph.regularityReduced_le`：regularityReduced_le : G.regularityRed
uced P ε δ <= G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `SimpleGraph.two_mul_card_edgeFinset`：two_mul_card_edgeFinset : 2 * #G.ed
geFinset = #(univ.filter fun (x, y) => G.Adj x y)
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `SimpleGraph.unreduced_edges_subset`：unreduced_edges_subset : (A ×ˢ A).fi
lter (fun (x, y) => G.Adj x y ∧ ¬ (G.regularityReduced P (ε / 8) (ε / 4)).Adj x 
y) subseteq (P.nonUnifor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
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
（共 73 条，此处仅展示前 30 条）
-/
lemma regularityReduced_edges_card_aux [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
    (hPε : P.IsUniform G (ε / 8)) (hP' : 4 / ε ≤ #P.parts) :
    2 * (#G.edgeFinset - #(G.regularityReduced P (ε / 8) (ε / 4)).edgeFinset : ℝ)
      < 2 * ε * (card α ^ 2 : ℕ) := by
  let A := (P.nonUniforms G (ε / 8)).biUnion fun (U, V) ↦ U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε / 4)).biUnion fun (U, V) ↦ G.interedges U V
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) ↦
          G.Adj x y ∧ ¬(G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) : ℝ) := by
      rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset, two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy ↦ regularityReduced_le hxy
    _ ≤ #(A ∪ B ∪ C) := by gcongr; exact unreduced_edges_subset
    _ ≤ #(A ∪ B) + #C := mod_cast (card_union_le _ _)
    _ ≤ #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * (ε / 8) * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty (by positivity) hPε
    _ ≤ _ + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : ℕ) := by norm_cast; ring

/-- **Triangle Removal Lemma**. If not all triangles can be removed by removing few edges (on the
order of `(card α)^2`), then there were many triangles to start with (on the order of
`(card α)^3`). -/
/-
**SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {G : SimpleGr
aph α} [inst_2 : DecidableRel G.Adj] {ε : ℝ},   G.FarFromTriangleFree ε → Simple
Graph.triangleRemovalBound ε * ↑(Fintype.card α) ^ 3 ≤ ↑(G.cliqueFinset 3).card
参数：Fintype.card α；G.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `SimpleGraph.triangleRemovalBound_nonpos`：triangleRemovalBound_nonpos (hε
 : ε <= 0) : triangleRemovalBound ε <= 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
**Triangle Removal Lemma**. If not all triangles can be removed by removing few 
edges (on the
order of `(card α)^2`), then there were many triangles to start with (on the ord
er of
`(card α)^3`).
-/
lemma FarFromTriangleFree.le_card_cliqueFinset (hG : G.FarFromTriangleFree ε) :
    triangleRemovalBound ε * card α ^ 3 ≤ #(G.cliqueFinset 3) := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  obtain hε | hε := le_or_gt ε 0
  · apply (mul_nonpos_of_nonpos_of_nonneg (triangleRemovalBound_nonpos hε) _).trans <;> positivity
  let l : ℕ := ⌈4 / ε⌉₊
  have hl : 4 / ε ≤ l := le_ceil (4 / ε)
  rcases le_total (card α) l with hl' | hl'
  · calc
      _ ≤ triangleRemovalBound ε * ↑l ^ 3 := by
        gcongr; exact (triangleRemovalBound_pos hε).le
      _ ≤ (1 : ℝ) := (triangleRemovalBound_mul_cube_lt hε).le
      _ ≤ _ := by simpa [one_le_iff_ne_zero] using (hG.cliqueFinset_nonempty hε).card_pos.ne'
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G (by positivity : 0 < ε / 8) hl'
  have : 4 / ε ≤ #P.parts := hl.trans (cast_le.2 hP₂)
  have k := regularityReduced_edges_card_aux hε hP₁ hP₄ this
  rw [mul_assoc] at k
  replace k := lt_of_mul_lt_mul_left k zero_le_two
  obtain ⟨t, ht⟩ := hG.cliqueFinset_nonempty' regularityReduced_le k
  exact triangle_removal_aux hε hG.lt_one.le hP₁ hP₃ ht

/-- **Triangle Removal Lemma**. If there are not too many triangles (on the order of `(card α)^3`)
then they can all be removed by removing a few edges (on the order of `(card α)^2`). -/
/-
**SimpleGraph.triangle_removal** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：triangle_removal (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card
 α ^ 3) : exists G' <= G, exists _ : DecidableRel G'.Adj, (#G.edgeFinset - #G'.e
dgeFinset : Real) < ε * (card α ^ 2 : Nat) ∧ G'.CliqueFree 3
参数：hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`：∀ {α : Type u_1} [
inst : DecidableEq α] [inst_1 : Fintype α] {G : SimpleGraph α} [inst_2 : Decidab
leRel G.Adj] {ε : ℝ},   G.FarFromTriangleF…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.farFromTriangleFree_iff`：farFromTriangleFree_iff : G.FarFrom
TriangleFree ε ↔ forall ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] -> H <= G -> H
.CliqueFree 3 -> ε * (car…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
**Triangle Removal Lemma**. If there are not too many triangles (on the order of
 `(card α)^3`)
then they can all be removed by removing a few edges (on the order of `(card α)^
2`).
-/
lemma triangle_removal (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3) :
    ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
      (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α ^ 2 : ℕ) ∧ G'.CliqueFree 3 := by
  by_contra! h
  refine hG.not_ge (farFromTriangleFree_iff.2 ?_).le_card_cliqueFinset
  intro G' _ hG hG'
  exact le_of_not_gt fun i ↦ h G' hG _ i hG'

end SimpleGraph

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq SimpleGraph

/-- Extension for the `positivity` tactic: `SimpleGraph.triangleRemovalBound ε` is positive
if `ε` is.

This exploits the positivity of the junk value of `triangleRemovalBound ε` for `ε ≥ 1`. -/
@[positivity triangleRemovalBound _]
meta def evalTriangleRemovalBound : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(triangleRemovalBound $ε) =>
    let .positive hε ← core q(inferInstance) (some q(inferInstance)) ε | failure
    assertInstancesCommute
    pure (.positive q(triangleRemovalBound_pos $hε))
  | _, _, _ => throwError "failed to match on Int.ceil application"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (ε : ℝ) (hε : 0 < ε) : 0 < triangleRemovalBound ε := by positivity

end Mathlib.Meta.Positivity

