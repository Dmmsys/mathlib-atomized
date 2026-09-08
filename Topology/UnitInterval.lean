/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The unit interval, as a topological space

Use `open unitInterval` to turn on the notation `I := Set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

@[expose] public section

noncomputable section

open Topology Filter Set Int Set.Icc

/-! ### The unit interval -/


/-- The unit interval `[0,1]` in ℝ. -/
/-
**unitInterval** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：unitInterval : Set Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit interval `[0,1]` in ℝ.
-/
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

namespace unitInterval

/-
**unitInterval.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：zero_mem : (0 : Real) in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem zero_mem : (0 : ℝ) ∈ I :=
  ⟨le_rfl, zero_le_one⟩
/-
**unitInterval.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：one_mem : (1 : Real) in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem one_mem : (1 : ℝ) ∈ I :=
  ⟨zero_le_one, le_rfl⟩
/-
**unitInterval.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：mul_mem {x y : Real} (hx : x in I) (hy : y in I) : x * y in I
参数：hx : x in I；hy : y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
  ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩
/-
**unitInterval.div_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：div_mem {x y : Real} (hx : 0 <= x) (hy : 0 <= y) (hxy : x <= y) : x / y in
 I
参数：hx : 0 <= x；hy : 0 <= y；hxy : x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
  ⟨div_nonneg hx hy, div_le_one_of_le₀ hxy hy⟩
/-
**unitInterval.fract_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：fract_mem (x : Real) : fract x in I
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.fract_nonneg`：fract_nonneg (a : R) : 0 <= fract a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
-/
theorem fract_mem (x : ℝ) : fract x ∈ I :=
  ⟨fract_nonneg _, (fract_lt_one _).le⟩
/-
**unitInterval.univ_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：univ_eq_Icc : (univ : Set I) = Icc (0 : I) (1 : I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_bot_top`：Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α)
 ⊤ = univ
-/
lemma univ_eq_Icc : (univ : Set I) = Icc (0 : I) (1 : I) := Icc_bot_top.symm
/-
**unitInterval.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, ↑x ≠ 0 ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.Icc.coe_eq_zero`：coe_eq_zero {x : Icc (0 : R) 1} : (x : R) = 0 ↔ x =
 0
-/
@[norm_cast] theorem coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not
/-
**unitInterval.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, ↑x ≠ 1 ↔ x ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.Icc.coe_eq_one`：coe_eq_one {x : Icc (0 : R) 1} : (x : R) = 1 ↔ x = 1
-/
@[norm_cast] theorem coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 := coe_eq_one.not
/-
**unitInterval.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, 0 < ↑x ↔ 0 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] theorem coe_pos {x : I} : (0 : ℝ) < x ↔ 0 < x := Iff.rfl
/-
**unitInterval.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, ↑x < 1 ↔ x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] theorem coe_lt_one {x : I} : (x : ℝ) < 1 ↔ x < 1 := Iff.rfl
/-
**unitInterval.mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：mul_le_left {x y : I} : x * y <= x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_le_left {x y : I} : x * y ≤ x :=
  Subtype.coe_le_coe.mp <| mul_le_of_le_one_right x.2.1 y.2.2
/-
**unitInterval.mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：mul_le_right {x y : I} : x * y <= y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_le_right {x y : I} : x * y ≤ y :=
  Subtype.coe_le_coe.mp <| mul_le_of_le_one_left y.2.1 x.2.2
/-
**unitInterval.eq_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：eq_closedBall : I = Metric.closedBall 2⁻¹ 2⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Icc_eq_closedBall`：Real.Icc_eq_closedBall (x y : Real) : Icc x y = 
closedBall ((x + y) / 2) ((y - x) / 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem eq_closedBall : I = Metric.closedBall 2⁻¹ 2⁻¹ := by
  norm_num [unitInterval, Real.Icc_eq_closedBall]

/-- Unit interval central symmetry. -/
/-
**unitInterval.symm** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：symm : I -> I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unit interval central symmetry.
-/
def symm : I → I := fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp, grind =]
/-
**unitInterval.symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_zero : σ 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_zero : σ 0 = 1 :=
  Subtype.ext <| by simp [symm]

@[simp, grind =]
/-
**unitInterval.symm_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_one : σ 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_one : σ 1 = 0 :=
  Subtype.ext <| by simp [symm]

@[simp, grind =]
/-
**unitInterval.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_symm (x : I) : σ (σ x) = x
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_symm (x : I) : σ (σ x) = x :=
  Subtype.ext <| by simp [symm]
/-
**unitInterval.symm_involutive** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_involutive : Function.Involutive (symm : I -> I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
-/
theorem symm_involutive : Function.Involutive (symm : I → I) := symm_symm
/-
**unitInterval.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_bijective : Function.Bijective (symm : I -> I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `unitInterval.symm_involutive`：symm_involutive : Function.Involutive (sym
m : I -> I)
-/
theorem symm_bijective : Function.Bijective (symm : I → I) := symm_involutive.bijective

@[simp, grind =]
/-
**unitInterval.coe_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：coe_symm_eq (x : I) : (σ x : Real) = 1 - x
参数：x : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x :=
  rfl
/-
**unitInterval.image_coe_preimage_symm** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：image_coe_preimage_symm {s : Set I} : Subtype.val '' σ ⁻¹' s = (1 - ·) ⁻¹'
 Subtype.val '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image_coe_preimage_symm {s : Set I} :
    Subtype.val '' σ ⁻¹' s = (1 - ·) ⁻¹' Subtype.val '' s := by
  simp [symm_involutive, ← Function.Involutive.image_eq_preimage_symm, image_image]

@[simp]
/-
**unitInterval.symm_projIcc** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_projIcc (x : Real) : symm (projIcc 0 1 zero_le_one x) = projIcc 0 1 z
ero_le_one (1 - x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIcc_of_le_left`：projIcc_of_le_left (hx : x <= a) : projIcc a b h
 x = ⟨a, left_mem_Icc.2 h⟩
· 使用定理 `unitInterval.symm_zero`：symm_zero : σ 0 = 1
· 使用定理 `Set.projIcc_of_right_le`：projIcc_of_right_le (hx : b <= x) : projIcc a b
 h x = ⟨b, right_mem_Icc.2 h⟩
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `unitInterval.symm_one`：symm_one : σ 1 = 0
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem symm_projIcc (x : ℝ) :
    symm (projIcc 0 1 zero_le_one x) = projIcc 0 1 zero_le_one (1 - x) := by
  ext
  rcases le_total x 0 with h₀ | h₀
  · simp [projIcc_of_le_left, projIcc_of_right_le, h₀]
  · rcases le_total x 1 with h₁ | h₁
    · lift x to I using ⟨h₀, h₁⟩
      simp_rw [← coe_symm_eq, projIcc_val]
    · simp [projIcc_of_le_left, projIcc_of_right_le, h₁]

@[continuity, fun_prop]
/-
**unitInterval.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：continuous_symm : Continuous σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_symm : Continuous σ :=
  Continuous.subtype_mk (by fun_prop) _

/-- `unitInterval.symm` as a `Homeomorph`. -/
@[simps]
/-
**unitInterval.symmHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：symmHomeomorph : I ≃ₜ I where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x

--- 原说明 ---
`unitInterval.symm` as a `Homeomorph`.
-/
def symmHomeomorph : I ≃ₜ I where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm
/-
**unitInterval.strictAnti_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：strictAnti_symm : StrictAnti σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
theorem strictAnti_symm : StrictAnti σ := fun _ _ h ↦ sub_lt_sub_left (α := ℝ) h _


@[simp]
/-
**unitInterval.symm_inj** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_inj {i j : I} : σ i = σ j ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `unitInterval.symm_bijective`：symm_bijective : Function.Bijective (symm :
 I -> I)
-/
theorem symm_inj {i j : I} : σ i = σ j ↔ i = j := symm_bijective.injective.eq_iff
/-
**unitInterval.half_le_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：half_le_symm_iff (t : I) : 1 / 2 <= (σ t : Real) ↔ (t : Real) <= 1 / 2
参数：t : I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unitInterval.coe_symm_eq`：coe_symm_eq (x : I) : (σ x : Real) = 1 - x
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sub_half`：sub_half (a : K) : a - a / 2 = a / 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem half_le_symm_iff (t : I) : 1 / 2 ≤ (σ t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 := by
  rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le, sub_half]

@[simp]
/-
**unitInterval.symm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：symm_eq_one {i : I} : σ i = 1 ↔ i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_zero`：symm_zero : σ 0 = 1
· 使用定理 `unitInterval.symm_inj`：symm_inj {i j : I} : σ i = σ j ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma symm_eq_one {i : I} : σ i = 1 ↔ i = 0 := by
  rw [← symm_zero, symm_inj]

@[simp]
/-
**unitInterval.symm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：symm_eq_zero {i : I} : σ i = 0 ↔ i = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_one`：symm_one : σ 1 = 0
· 使用定理 `unitInterval.symm_inj`：symm_inj {i j : I} : σ i = σ j ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma symm_eq_zero {i : I} : σ i = 0 ↔ i = 1 := by
  rw [← symm_one, symm_inj]

@[simp]
/-
**unitInterval.symm_le_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_le_symm {i j : I} : σ i <= σ j ↔ j <= i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem symm_le_symm {i j : I} : σ i ≤ σ j ↔ j ≤ i := by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff, add_le_add_iff_left, Subtype.coe_le_coe]
/-
**unitInterval.le_symm_comm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：le_symm_comm {i j : I} : i <= σ j ↔ j <= σ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_le_symm`：symm_le_symm {i j : I} : σ i <= σ j ↔ j <= i
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_symm_comm {i j : I} : i ≤ σ j ↔ j ≤ σ i := by
  rw [← symm_le_symm, symm_symm]
/-
**unitInterval.symm_le_comm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_le_comm {i j : I} : σ i <= j ↔ σ j <= i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_le_symm`：symm_le_symm {i j : I} : σ i <= σ j ↔ j <= i
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_le_comm {i j : I} : σ i ≤ j ↔ σ j ≤ i := by
  rw [← symm_le_symm, symm_symm]

@[simp]
/-
**unitInterval.symm_lt_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_lt_symm {i j : I} : σ i < σ j ↔ j < i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem symm_lt_symm {i j : I} : σ i < σ j ↔ j < i := by
  simp only [symm, Subtype.mk_lt_mk, sub_lt_sub_iff_left, Subtype.coe_lt_coe]
/-
**unitInterval.lt_symm_comm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：lt_symm_comm {i j : I} : i < σ j ↔ j < σ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_lt_symm`：symm_lt_symm {i j : I} : σ i < σ j ↔ j < i
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_symm_comm {i j : I} : i < σ j ↔ j < σ i := by
  rw [← symm_lt_symm, symm_symm]
/-
**unitInterval.symm_lt_comm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：symm_lt_comm {i j : I} : σ i < j ↔ σ j < i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unitInterval.symm_lt_symm`：symm_lt_symm {i j : I} : σ i < σ j ↔ j < i
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_lt_comm {i j : I} : σ i < j ↔ σ j < i := by
  rw [← symm_lt_symm, symm_symm]
/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConnectedSpace I :=
  Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

/-- Verify there is an instance for `CompactSpace I`. -/
/-
**unitInterval.** 是 Mathlib 中的一个示例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify there is an instance for `CompactSpace I`.
-/
example : CompactSpace I := by infer_instance
/-
**unitInterval.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：nonneg (x : I) : 0 <= (x : Real)
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem nonneg (x : I) : 0 ≤ (x : ℝ) :=
  x.2.1
/-
**unitInterval.one_minus_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：one_minus_nonneg (x : I) : 0 <= 1 - (x : Real)
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
/-
**unitInterval.le_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：le_one (x : I) : (x : Real) <= 1
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem le_one (x : I) : (x : ℝ) ≤ 1 :=
  x.2.2
/-
**unitInterval.one_minus_le_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：one_minus_le_one (x : I) : 1 - (x : Real) <= 1
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1
/-
**unitInterval.add_pos** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：add_pos {t : I} {x : Real} (hx : 0 < x) : 0 < (x + t : Real)
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `unitInterval.nonneg`：nonneg (x : I) : 0 <= (x : Real)
-/
theorem add_pos {t : I} {x : ℝ} (hx : 0 < x) : 0 < (x + t : ℝ) :=
  add_pos_of_pos_of_nonneg hx <| nonneg _

/-- like `unitInterval.nonneg`, but with the inequality in `I`. -/
/-
**unitInterval.nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：nonneg' {t : I} : 0 <= t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `unitInterval.nonneg`, but with the inequality in `I`.
-/
theorem nonneg' {t : I} : 0 ≤ t :=
  t.2.1

/-- like `unitInterval.le_one`, but with the inequality in `I`. -/
/-
**unitInterval.le_one'** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：le_one' {t : I} : t <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
like `unitInterval.le_one`, but with the inequality in `I`.
-/
theorem le_one' {t : I} : t ≤ 1 :=
  t.2.2
/-
**unitInterval.pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, 0 < x ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
-/
protected lemma pos_iff_ne_zero {x : I} : 0 < x ↔ x ≠ 0 := bot_lt_iff_ne_bot
/-
**unitInterval.lt_one_iff_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {x : ↑unitInterval}, x < 1 ↔ x ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
protected lemma lt_one_iff_ne_one {x : I} : x < 1 ↔ x ≠ 1 := lt_top_iff_ne_top
/-
**unitInterval.eq_one_or_eq_zero_of_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `unitInterv
al`。
形式化陈述：eq_one_or_eq_zero_of_le_mul {i j : I} (h : i <= j * i) : i = 0 ∨ j = 1
参数：h : i <= j * i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `Set.Icc.coe_mul`：coe_mul (x y : Icc (0 : R) 1) : ↑(x * y) = (x * y : R)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `unitInterval.coe_pos`：∀ {x : ↑unitInterval}, 0 < ↑x ↔ 0 < x
· 使用定理 `unitInterval.pos_iff_ne_zero`：∀ {x : ↑unitInterval}, 0 < x ↔ x ≠ 0
· 使用定理 `unitInterval.coe_lt_one`：∀ {x : ↑unitInterval}, ↑x < 1 ↔ x < 1
· 使用定理 `unitInterval.lt_one_iff_ne_one`：∀ {x : ↑unitInterval}, x < 1 ↔ x ≠ 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma eq_one_or_eq_zero_of_le_mul {i j : I} (h : i ≤ j * i) : i = 0 ∨ j = 1 := by
  contrapose! h
  rw [← unitInterval.lt_one_iff_ne_one, ← coe_lt_one, ← unitInterval.pos_iff_ne_zero,
    ← coe_pos] at h
  rw [← Subtype.coe_lt_coe, coe_mul]
  simpa using mul_lt_mul_of_pos_right h.right h.left
/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial I := ⟨⟨1, 0, (one_ne_zero <| congrArg Subtype.val ·)⟩⟩
/-
**unitInterval.mul_pos_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：mul_pos_mem_iff {a t : Real} (ha : 0 < a) : a * t in I ↔ t in Set.Icc (0 :
 Real) (1 / a)
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_of_mul_nonneg_right`：nonneg_of_mul_nonneg_right [PosMulStrictMono
 R] (h : 0 <= a * b) (ha : 0 < a) : 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ Set.Icc (0 : ℝ) (1 / a) := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff₀ ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff₀ ha, mul_comm] at h₂
/-
**unitInterval.two_mul_sub_one_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：two_mul_sub_one_mem_iff {t : Real} : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 
: Real) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 64 条，此处仅展示前 30 条）
-/
theorem two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The unit interval as a submonoid of ℝ. -/
/-
**unitInterval.submonoid** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：submonoid : Submonoid Real where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `unitInterval.mul_mem`：mul_mem {x y : Real} (hx : x in I) (hy : y in I) :
 x * y in I
· 使用定理 `unitInterval.one_mem`：one_mem : (1 : Real) in I

--- 原说明 ---
The unit interval as a submonoid of ℝ.
-/
def submonoid : Submonoid ℝ where
  carrier := unitInterval
  one_mem' := unitInterval.one_mem
  mul_mem' := unitInterval.mul_mem
/-
**unitInterval.coe_unitIntervalSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval
`。
形式化陈述：↑unitInterval.submonoid = unitInterval
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_unitIntervalSubmonoid : submonoid = unitInterval := rfl
/-
**unitInterval.mem_unitIntervalSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval
`。
形式化陈述：∀ {x : ℝ}, x ∈ unitInterval.submonoid ↔ x ∈ unitInterval
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_unitIntervalSubmonoid {x} : x ∈ submonoid ↔ x ∈ unitInterval :=
  Iff.rfl
/-
**unitInterval.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ {ι : Type u_1} {t : Finset ι} {f : ι → ℝ}, (∀ c ∈ t, f c ∈ unitInterval)
 → ∏ c ∈ t, f c ∈ unitInterval
参数：∀ c ∈ t, f c ∈ unitInterval。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → ℝ}
    (h : ∀ c ∈ t, f c ∈ unitInterval) :
    ∏ c ∈ t, f c ∈ unitInterval := _root_.prod_mem (S := unitInterval.submonoid) h
/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedCommMonoidWithZero I where
  isBot_zero x := x.2.1
  mul_lt_mul_of_pos_left i hi j k hjk := by
    simp only [← Subtype.coe_lt_coe, coe_mul]; gcongr
/-
**unitInterval.subtype_Iic_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：subtype_Iic_eq_Icc (x : I) : Subtype.val ⁻¹' (Iic ↑x) = Icc 0 x
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_subtype_val_Iic`：∀ {α : Type u_1} [inst : Preorder α] {p : 
α → Prop} (a : { x // p x }), Subtype.val ⁻¹' Set.Iic ↑a = Set.Iic a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
-/
lemma subtype_Iic_eq_Icc (x : I) : Subtype.val ⁻¹' (Iic ↑x) = Icc 0 x := by
  rw [preimage_subtype_val_Iic]
  exact Icc_bot.symm
/-
**unitInterval.subtype_Iio_eq_Ico** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：subtype_Iio_eq_Ico (x : I) : Subtype.val ⁻¹' (Iio ↑x) = Ico 0 x
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_subtype_val_Iio`：∀ {α : Type u_1} [inst : Preorder α] {p : 
α → Prop} (a : { x // p x }), Subtype.val ⁻¹' Set.Iio ↑a = Set.Iio a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Ico ⊥ a = Set.Iio a
-/
lemma subtype_Iio_eq_Ico (x : I) : Subtype.val ⁻¹' (Iio ↑x) = Ico 0 x := by
  rw [preimage_subtype_val_Iio]
  exact Ico_bot.symm
/-
**unitInterval.subtype_Ici_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：subtype_Ici_eq_Icc (x : I) : Subtype.val ⁻¹' (Ici ↑x) = Icc x 1
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_subtype_val_Ici`：∀ {α : Type u_1} [inst : Preorder α] {p : 
α → Prop} (a : { x // p x }), Subtype.val ⁻¹' Set.Ici ↑a = Set.Ici a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_top`：Icc_top : Icc a ⊤ = Ici a
-/
lemma subtype_Ici_eq_Icc (x : I) : Subtype.val ⁻¹' (Ici ↑x) = Icc x 1 := by
  rw [preimage_subtype_val_Ici]
  exact Icc_top.symm
/-
**unitInterval.subtype_Ioi_eq_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：subtype_Ioi_eq_Ioc (x : I) : Subtype.val ⁻¹' (Ioi ↑x) = Ioc x 1
参数：x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_subtype_val_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {p : 
α → Prop} (a : { x // p x }), Subtype.val ⁻¹' Set.Ioi ↑a = Set.Ioi a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_top`：Ioc_top : Ioc a ⊤ = Ioi a
-/
lemma subtype_Ioi_eq_Ioc (x : I) : Subtype.val ⁻¹' (Ioi ↑x) = Ioc x 1 := by
  rw [preimage_subtype_val_Ioi]
  exact Ioc_top.symm

end unitInterval

section partition

namespace Set.Icc

variable {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {a b c d : α} (h : a ≤ b) {δ : α}

-- TODO: Set.projIci, Set.projIic
/-- `Set.projIcc` is a contraction. -/
/-
**Set.Icc._root_.Set.abs_projIcc_sub_projIcc** 是 Mathlib 中的一个引理，位于命名空间 `Set.Icc`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.projIcc` is a contraction.
-/
lemma _root_.Set.abs_projIcc_sub_projIcc : (|projIcc a b h c - projIcc a b h d| : α) ≤ |c - d| := by
  wlog hdc : d ≤ c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_ge hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc),
    abs_eq_self.2 (sub_nonneg.2 <| mod_cast monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (by rwa [sub_self]) ?_)
  refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rwa [sub_self, abs_zero]
  · exact (abs_eq_self.mpr hdc).le

/-- When `h : a ≤ b` and `δ > 0`, `addNSMul h δ` is a sequence of points in the closed interval
`[a,b]`, which is initially equally spaced but eventually stays at the right endpoint `b`. -/
/-
**Set.Icc.addNSMul** 是 Mathlib 中的一个定义，位于命名空间 `Set.Icc`。
形式化陈述：addNSMul (δ : α) (n : Nat) : Icc a b
参数：δ : α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `h : a ≤ b` and `δ > 0`, `addNSMul h δ` is a sequence of points in the clos
ed interval
`[a,b]`, which is initially equally spaced but eventually stays at the right end
point `b`.
-/
def addNSMul (δ : α) (n : ℕ) : Icc a b := projIcc a b h (a + n • δ)

omit [IsOrderedAddMonoid α] in
/-
**Set.Icc.addNSMul_zero** 是 Mathlib 中的一个引理，位于命名空间 `Set.Icc`。
形式化陈述：addNSMul_zero : addNSMul h δ 0 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc.addNSMul.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 
: LinearOrder α] {a b : α} (h : a ≤ b) (δ : α) (n : ℕ),   Set.Icc.addNSMul h δ n
 = Set.proj…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.projIcc_left`：projIcc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩
-/
lemma addNSMul_zero : addNSMul h δ 0 = a := by
  rw [addNSMul, zero_smul, add_zero, projIcc_left]
/-
**Set.Icc.addNSMul_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `Set.Icc`。
形式化陈述：addNSMul_eq_right [Archimedean α] (hδ : 0 < δ) : exists m, forall n >= m, 
addNSMul h δ n = b
参数：hδ : 0 < δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc.addNSMul.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 
: LinearOrder α] {a b : α} (h : a ≤ b) (δ : α) (n : ℕ),   Set.Icc.addNSMul h δ n
 = Set.proj…
· 使用定理 `Set.coe_projIcc`：coe_projIcc (a b : α) (h : a <= b) (x : α) : (projIcc a
 b h x : α) = max a (min b x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_eq_left_iff`：min_eq_left_iff : min a b = a ↔ a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nsmul_le_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftMono M] {a : M} {n m : ℕ},   0 ≤ a → n ≤ m → n • a ≤ m • a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
-/
lemma addNSMul_eq_right [Archimedean α] (hδ : 0 < δ) :
    ∃ m, ∀ n ≥ m, addNSMul h δ n = b := by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn ↦ ?_⟩
  rw [addNSMul, coe_projIcc, add_comm, min_eq_left_iff.mpr, max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)
/-
**Set.Icc.monotone_addNSMul** 是 Mathlib 中的一个引理，位于命名空间 `Set.Icc`。
形式化陈述：monotone_addNSMul (hδ : 0 <= δ) : Monotone (addNSMul h δ)
参数：hδ : 0 <= δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.monotone_projIcc`：monotone_projIcc : Monotone (projIcc a b h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `nsmul_le_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftMono M] {a : M} {n m : ℕ},   0 ≤ a → n ≤ m → n • a ≤ m • a
-/
lemma monotone_addNSMul (hδ : 0 ≤ δ) : Monotone (addNSMul h δ) :=
  fun _ _ hnm ↦ monotone_projIcc h <| (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)
/-
**Set.Icc.abs_sub_addNSMul_le** 是 Mathlib 中的一个引理，位于命名空间 `Set.Icc`。
形式化陈述：abs_sub_addNSMul_le (hδ : 0 <= δ) {t : Icc a b} (n : Nat) (ht : t in Icc (
addNSMul h δ n) (addNSMul h δ (n + 1))) : (|t - addNSMul h δ n| : α) <= δ
参数：hδ : 0 <= δ；n : Nat；ht : t in Icc (addNSMul h δ n) (addNSMul h δ (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Set.abs_projIcc_sub_projIcc`：∀ {α : Type u_1} [inst : AddCommGroup α] [i
nst_1 : LinearOrder α] [IsOrderedAddMonoid α] {a b c d : α} (h : a ≤ b),   |↑(Se
t.projIcc a b h c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma abs_sub_addNSMul_le (hδ : 0 ≤ δ) {t : Icc a b} (n : ℕ)
    (ht : t ∈ Icc (addNSMul h δ n) (addNSMul h δ (n + 1))) :
    (|t - addNSMul h δ n| : α) ≤ δ :=
  calc
    (|t - addNSMul h δ n| : α) = t - addNSMul h δ n := abs_eq_self.2 <| sub_nonneg.2 ht.1
    _ ≤ projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n := by apply sub_le_sub_right; exact ht.2
    _ ≤ (|projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n| : α) := le_abs_self _
    _ ≤ |a + (n + 1) • δ - (a + n • δ)| := abs_projIcc_sub_projIcc h
    _ ≤ δ := by
          rw [add_sub_add_comm, sub_self, zero_add, succ_nsmul', add_sub_cancel_right]
          exact (abs_eq_self.mpr hδ).le

/--
Form a convex linear combination of two points in a closed interval.

This should be removed once a general theory of convex spaces is available in Mathlib.
-/
/-
**Set.Icc.convexComb** 是 Mathlib 中的一个定义，位于命名空间 `Set.Icc`。
形式化陈述：convexComb {a b : Real} (x y : Icc a b) (t : unitInterval) : Icc a b
参数：x y : Icc a b；t : unitInterval。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Form a convex linear combination of two points in a closed interval.

This should be removed once a general theory of convex spaces is available in Ma
thlib.
-/
def convexComb {a b : ℝ} (x y : Icc a b) (t : unitInterval) : Icc a b :=
  ⟨(1 - t) * x + t * y, by
    constructor
    · nlinarith [x.2.1, y.2.1, t.2.1, t.2.2]
    · nlinarith [x.2.2, y.2.2, t.2.1, t.2.2]⟩

@[simp, grind =]
/-
**Set.Icc.coe_convexComb** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：coe_convexComb {a b : Real} (x y : Icc a b) (t : unitInterval) : (convexCo
mb x y t : Real) = (1 - t) * x + t * y
参数：x y : Icc a b；t : unitInterval。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_convexComb {a b : ℝ} (x y : Icc a b) (t : unitInterval) :
  (convexComb x y t : ℝ) = (1 - t) * x + t * y := rfl

@[simp, grind =]
/-
**Set.Icc.convexComb_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_zero {a b : Real} (x y : Icc a b) : convexComb x y 0 = x
参数：x y : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexComb_zero {a b : ℝ} (x y : Icc a b) : convexComb x y 0 = x := by
  simp [convexComb]

@[simp, grind =]
/-
**Set.Icc.convexComb_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_one {a b : Real} (x y : Icc a b) : convexComb x y 1 = y
参数：x y : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexComb_one {a b : ℝ} (x y : Icc a b) : convexComb x y 1 = y := by
  simp [convexComb]

@[simp, grind =]
/-
**Set.Icc.convexComb_zero_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_zero_one (t : unitInterval) : convexComb 0 1 t = t
参数：t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexComb_zero_one (t : unitInterval) : convexComb 0 1 t = t := by
  simp [convexComb]

@[simp, grind =]
/-
**Set.Icc.convexComb_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_eq {a b : Real} (x : Icc a b) (t : unitInterval) : convexComb x
 x t = x
参数：x : Icc a b；t : unitInterval。
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexComb_eq {a b : ℝ} (x : Icc a b) (t : unitInterval) : convexComb x x t = x := by
  simp [convexComb, sub_mul]

@[simp, grind =]
/-
**Set.Icc.convexComb_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_symm {a b : Real} (x y : Icc a b) (t : unitInterval) : convexCo
mb x y (unitInterval.symm t) = convexComb y x t
参数：x y : Icc a b；t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `_private.Mathlib.Topology.UnitInterval.0.Set.Icc.convexComb_symm._abel_1
_2`：∀ {a b : ℝ} (x y : ↑(Set.Icc a b)) (t : ↑unitInterval), ↑t * ↑x + (1 - ↑t) *
 ↑y = (1 - ↑t) * ↑y + ↑t * ↑x
-/
theorem convexComb_symm {a b : ℝ} (x y : Icc a b) (t : unitInterval) :
    convexComb x y (unitInterval.symm t) = convexComb y x t := by
  simp [convexComb]
  abel

@[grind .]
/-
**Set.Icc.le_convexComb** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：le_convexComb {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval)
 : x <= convexComb x y t
参数：h : x <= y；t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 57 条，此处仅展示前 30 条）
-/
theorem le_convexComb {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    x ≤ convexComb x y t := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[grind .]
/-
**Set.Icc.convexComb_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_le {a b : Real} {x y : Icc a b} (h : x <= y) (t : unitInterval)
 : convexComb x y t <= y
参数：h : x <= y；t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 57 条，此处仅展示前 30 条）
-/
theorem convexComb_le {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    convexComb x y t ≤ y := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[continuity, fun_prop]
/-
**Set.Icc.continuous_convexComb** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：continuous_convexComb {a b : Real} (x y : Icc a b) : Continuous (convexCom
b x y)
参数：x y : Icc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_convexComb {a b : ℝ} (x y : Icc a b) : Continuous (convexComb x y) := by
  unfold Icc.convexComb
  fun_prop

@[continuity, fun_prop]
/-
**Set.Icc.continuous_convexComb_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：continuous_convexComb_prod {a b : Real} : Continuous fun x : Icc a b × Icc
 a b × unitInterval => Icc.convexComb x.1 x.2.1 x.2.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
-/
theorem continuous_convexComb_prod {a b : ℝ} :
    Continuous fun x : Icc a b × Icc a b × unitInterval ↦ Icc.convexComb x.1 x.2.1 x.2.2 := by
  unfold Icc.convexComb
  fun_prop

/--
Helper definition for `convexComb_assoc`, giving one of the coefficients appearing
when we reassociate a convex combination.
-/
/-
**Set.Icc.convexComb_assoc_coeff** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition for `convexComb_assoc`, giving one of the coefficients appeari
ng
when we reassociate a convex combination.
-/
abbrev convexComb_assoc_coeff₁ (s t : unitInterval) : unitInterval :=
  ⟨s * (1 - t) / (1 - s * t),
    by
      apply div_nonneg
      · nlinarith [s.2.1, t.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1],
    by
      apply div_le_one_of_le₀
      · nlinarith [s.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1]⟩

/--
Helper definition for `convexComb_assoc`, giving one of the coefficients appearing
when we reassociate a convex combination.
-/
/-
**Set.Icc.convexComb_assoc_coeff** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition for `convexComb_assoc`, giving one of the coefficients appeari
ng
when we reassociate a convex combination.
-/
abbrev convexComb_assoc_coeff₂ (s t : unitInterval) : unitInterval := s * t
/-
**Set.Icc.convexComb_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_assoc {a b : Real} (x y z : Icc a b) (s t : unitInterval) : con
vexComb x (convexComb y z t) s = convexComb (convexComb x y (convexComb_assoc_co
eff₁ s t)) z (convexComb_assoc_coeff₂ s t)
参数：x y z : Icc a b；s t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 112 条，此处仅展示前 30 条）
-/
theorem convexComb_assoc {a b : ℝ} (x y z : Icc a b) (s t : unitInterval) :
    convexComb x (convexComb y z t) s =
      convexComb (convexComb x y (convexComb_assoc_coeff₁ s t)) z
        (convexComb_assoc_coeff₂ s t) := by
  simp only [convexComb, coe_mul, Subtype.mk.injEq]
  by_cases hs : (s : ℝ) = 1
  · simp only [hs]
    by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · have : (1 - t : ℝ) ≠ 0 := by grind
      field_simp
      simp
  · by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · have : (1 - s * t : ℝ) ≠ 0 := by
        intro h
        have : 1 ≤ (t : ℝ) := by nlinarith [s.2.2, t.2.1]
        grind
      field_simp
      ring_nf

/--
Helper definition for `convexComb_assoc'`, giving one of the coefficients appearing
when we reassociate a convex combination in the reverse direction.
-/
/-
**Set.Icc.convexComb_assoc_coeff** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition for `convexComb_assoc'`, giving one of the coefficients appear
ing
when we reassociate a convex combination in the reverse direction.
-/
abbrev convexComb_assoc_coeff₁' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexComb_assoc_coeff₂ (unitInterval.symm t) (unitInterval.symm s))

/--
Helper definition for `convexComb_assoc'`, giving one of the coefficients appearing
when we reassociate a convex combination in the reverse direction.
-/
/-
**Set.Icc.convexComb_assoc_coeff** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper definition for `convexComb_assoc'`, giving one of the coefficients appear
ing
when we reassociate a convex combination in the reverse direction.
-/
abbrev convexComb_assoc_coeff₂' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexComb_assoc_coeff₁ (unitInterval.symm t) (unitInterval.symm s))
/-
**Set.Icc.convexComb_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：convexComb_assoc' {a b : Real} (x y z : Icc a b) (s t : unitInterval) : co
nvexComb (convexComb x y s) z t = convexComb x (convexComb y z (convexComb_assoc
_coeff₂' s t)) (convexComb_assoc_coeff₁' s t)
参数：x y z : Icc a b；s t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc.convexComb_symm`：convexComb_symm {a b : Real} (x y : Icc a b) (t
 : unitInterval) : convexComb x y (unitInterval.symm t) = convexComb y x t
· 使用定理 `Set.Icc.convexComb_assoc`：convexComb_assoc {a b : Real} (x y z : Icc a b
) (s t : unitInterval) : convexComb x (convexComb y z t) s = convexComb (convexC
omb x y (conve…
· 使用定理 `Set.Icc.convexComb_assoc_coeff₁'.eq_1`：∀ (s t : ↑unitInterval),   Set.Ic
c.convexComb_assoc_coeff₁' s t =     unitInterval.symm (Set.Icc.convexComb_assoc
_coeff₂ (unitInterval.symm …
· 使用定理 `Set.Icc.convexComb_assoc_coeff₂'.eq_1`：∀ (s t : ↑unitInterval),   Set.Ic
c.convexComb_assoc_coeff₂' s t =     unitInterval.symm (Set.Icc.convexComb_assoc
_coeff₁ (unitInterval.symm …
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
-/
theorem convexComb_assoc' {a b : ℝ} (x y z : Icc a b) (s t : unitInterval) :
    convexComb (convexComb x y s) z t =
      convexComb x (convexComb y z (convexComb_assoc_coeff₂' s t))
        (convexComb_assoc_coeff₁' s t) := by
  rw [← convexComb_symm, ← convexComb_symm y x, convexComb_assoc, ← convexComb_symm x,
    ← convexComb_symm z y]
  rw [convexComb_assoc_coeff₁', convexComb_assoc_coeff₂', unitInterval.symm_symm]

set_option backward.privateInPublic true in
/-
**Set.Icc.eq_convexComb.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_convexComb.zero_le {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    0 ≤ ((y - x) / (z - x) : ℝ) := by
  by_cases h : (z - x : ℝ) = 0
  · simp_all
  · replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    apply div_nonneg <;> grind

set_option backward.privateInPublic true in
/-
**Set.Icc.eq_convexComb.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eq_convexComb.le_one {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    ((y - x) / (z - x) : ℝ) ≤ 1 := by
  by_cases h : (z - x : ℝ) = 0
  · simp_all
  · replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    apply div_le_one_of_le₀ <;> grind

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
A point between two points in a closed interval
can be expressed as a convex combination of them.
-/
/-
**Set.Icc.eq_convexComb** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：eq_convexComb {a b : Real} {x y z : Icc a b} (hxy : x <= y) (hyz : y <= z)
 : y = convexComb x z ⟨((y - x) / (z - x)), eq_convexComb.zero_le hxy hyz, eq_co
nvexComb.le_one hxy hyz⟩
参数：hxy : x <= y；hyz : y <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `_private.Mathlib.Topology.UnitInterval.0.Set.Icc.eq_convexComb.zero_le`：
∀ {a b : ℝ} {x y z : ↑(Set.Icc a b)}, x ≤ y → y ≤ z → 0 ≤ (↑y - ↑x) / (↑z - ↑x)
· 使用定理 `_private.Mathlib.Topology.UnitInterval.0.Set.Icc.eq_convexComb.le_one`：∀
 {a b : ℝ} {x y z : ↑(Set.Icc a b)}, x ≤ y → y ≤ z → (↑y - ↑x) / (↑z - ↑x) ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
A point between two points in a closed interval
can be expressed as a convex combination of them.
-/
theorem eq_convexComb {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    y = convexComb x z ⟨((y - x) / (z - x)),
          eq_convexComb.zero_le hxy hyz, eq_convexComb.le_one hxy hyz⟩ := by
  ext
  simp only [coe_convexComb]
  by_cases h : (z - x : ℝ) = 0
  · simp_all only [div_zero, sub_zero, one_mul, zero_mul, add_zero]
    replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    linarith
  · field_simp
    ring_nf

end Set.Icc

open scoped unitInterval

/-- Any open cover `c` of a closed interval `[a, b]` in ℝ
can be refined to a finite partition into subintervals. -/
/-
**exists_monotone_Icc_subset_open_cover_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_monotone_Icc_subset_open_cover_Icc {ι} {a b : Real} (h : a <= b) {c
 : ι -> Set (Icc a b)} (hc₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, 
c i) : exists t : Nat -> Icc a b, t 0 = a ∧ Monotone t ∧ (exists m, forall n >= 
m, t n = b) ∧ forall n, exists i, Icc (t n) (t (n + 1)) subseteq c i
参数：h : a <= b；Icc a b；hc₁ : forall i, IsOpen (c i)；hc₂ : univ subseteq ⋃ i, c i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lebesgue_number_lemma_of_metric`：lebesgue_number_lemma_of_metric {s : Se
t α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s) (hc₁ : forall i, IsOpen (c 
i)) (hc₂ : s subseteq…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Set.Icc.addNSMul_zero`：addNSMul_zero : addNSMul h δ 0 = a
· 使用引理 `Set.Icc.monotone_addNSMul`：monotone_addNSMul (hδ : 0 <= δ) : Monotone (a
ddNSMul h δ)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Set.Icc.addNSMul_eq_right`：addNSMul_eq_right [Archimedean α] (hδ : 0 < δ
) : exists m, forall n >= m, addNSMul h δ n = b
· 使用定理 `trivial`：True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Set.Icc.abs_sub_addNSMul_le`：abs_sub_addNSMul_le (hδ : 0 <= δ) {t : Icc 
a b} (n : Nat) (ht : t in Icc (addNSMul h δ n) (addNSMul h δ (n + 1))) : (|t - a
ddNSMul h δ n| : …
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a

--- 原说明 ---
Any open cover `c` of a closed interval `[a, b]` in ℝ
can be refined to a finite partition into subintervals.
-/
lemma exists_monotone_Icc_subset_open_cover_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → Icc a b, t 0 = a ∧
      Monotone t ∧ (∃ m, ∀ n ≥ m, t n = b) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n) trivial
  exact ⟨i, fun t ht ↦ hsub ((abs_sub_addNSMul_le h hδ.le n ht).trans_lt <| half_lt_self δ_pos)⟩

/-- Any open cover of the unit interval can be refined to a finite partition into subintervals. -/
/-
**exists_monotone_Icc_subset_open_cover_unitInterval** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι -> Set I} (h
c₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, c i) : exists t : Nat -> 
I, t 0 = 0 ∧ Monotone t ∧ (exists n, forall m >= n, t m = 1) ∧ forall n, exists 
i, Icc (t n) (t (n + 1)) subseteq c i
参数：hc₁ : forall i, IsOpen (c i)；hc₂ : univ subseteq ⋃ i, c i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `exists_monotone_Icc_subset_open_cover_Icc`：exists_monotone_Icc_subset_op
en_cover_Icc {ι} {a b : Real} (h : a <= b) {c : ι -> Set (Icc a b)} (hc₁ : foral
l i, IsOpen (c i)) (hc₂ : univ …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
Any open cover of the unit interval can be refined to a finite partition into su
bintervals.
-/
lemma exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧
      Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂
/-
**exists_monotone_Icc_subset_open_cover_unitInterval_prod_self** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：exists_monotone_Icc_subset_open_cover_unitInterval_prod_self {ι} {c : ι ->
 Set (I × I)} (hc₁ : forall i, IsOpen (c i)) (hc₂ : univ subseteq ⋃ i, c i) : ex
ists t : Nat -> I, t 0 = 0 ∧ Monotone t ∧ (exists n, forall m >= n, t m = 1) ∧ f
orall n m, exists i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) subseteq c i
参数：I × I；hc₁ : forall i, IsOpen (c i)；hc₂ : univ subseteq ⋃ i, c i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lebesgue_number_lemma_of_metric`：lebesgue_number_lemma_of_metric {s : Se
t α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s) (hc₁ : forall i, IsOpen (c 
i)) (hc₂ : s subseteq…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `Set.Icc.addNSMul_zero`：addNSMul_zero : addNSMul h δ 0 = a
· 使用引理 `Set.Icc.monotone_addNSMul`：monotone_addNSMul (hδ : 0 <= δ) : Monotone (a
ddNSMul h δ)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Set.Icc.addNSMul_eq_right`：addNSMul_eq_right [Archimedean α] (hδ : 0 < δ
) : exists m, forall n >= m, addNSMul h δ n = b
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `Set.Icc.abs_sub_addNSMul_le`：abs_sub_addNSMul_le (hδ : 0 <= δ) {t : Icc 
a b} (n : Nat) (ht : t in Icc (addNSMul h δ n) (addNSMul h δ (n + 1))) : (|t - a
ddNSMul h δ n| : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 31 条，此处仅展示前 30 条）
-/
lemma exists_monotone_Icc_subset_open_cover_unitInterval_prod_self {ι} {c : ι → Set (I × I)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : ℝ) ≤ 1 := zero_le_one
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h hδ.le, addNSMul_eq_right h hδ, fun n m ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n, addNSMul h (δ / 2) m) trivial
  exact ⟨i, fun t ht ↦ hsub (Metric.mem_ball.mpr <| (max_le (abs_sub_addNSMul_le h hδ.le n ht.1) <|
    abs_sub_addNSMul_le h hδ.le m ht.2).trans_lt <| half_lt_self δ_pos)⟩

end partition

@[simp]
/-
**projIcc_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：projIcc_eq_zero {x : Real} : projIcc (0 : Real) 1 zero_le_one x = 0 ↔ x <=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_eq_left`：projIcc_eq_left (h : a < b) : projIcc a b h.le x = 
⟨a, left_mem_Icc.mpr h.le⟩ ↔ x <= a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem projIcc_eq_zero {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
  projIcc_eq_left zero_lt_one

@[simp]
/-
**projIcc_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：projIcc_eq_one {x : Real} : projIcc (0 : Real) 1 zero_le_one x = 1 ↔ 1 <= 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.projIcc_eq_right`：projIcc_eq_right (h : a < b) : projIcc a b h.le x 
= ⟨b, right_mem_Icc.2 h.le⟩ ↔ b <= x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem projIcc_eq_one {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
  projIcc_eq_right zero_lt_one

namespace Mathlib.Tactic.Interactive

/--
`unit_interval` solves the goals `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for
any expression `x : I`.
-/
macro "unit_interval" : tactic =>
  `(tactic| (first
  | apply unitInterval.nonneg
  | apply unitInterval.one_minus_nonneg
  | apply unitInterval.le_one
  | apply unitInterval.one_minus_le_one))

/-
**Mathlib.Tactic.Interactive.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Tactic.Interact
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : unitInterval) : 0 ≤ (x : ℝ) := by unit_interval

end Mathlib.Tactic.Interactive

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

set_option backward.isDefEq.respectTransparency false in
-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
/-- The image of `[0,1]` under the homeomorphism `fun x ↦ a * x + b` is `[b, a+b]`.
-/
/-
**affineHomeomorph_image_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineHomeomorph_image_I (a b : 𝕜) (h : 0 < a) : affineHomeomorph a b h.ne
.symm '' Set.Icc 0 1 = Set.Icc b (a + b)
参数：a b : 𝕜；h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `affineHomeomorph_apply`：∀ {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : Topo
logicalSpace 𝕜] [inst_2 : IsTopologicalRing 𝕜] (a b : 𝕜) (h : a ≠ 0)   (x : 𝕜), 
(affineHomeo…
· 使用定理 `Set.image_affine_Icc'`：image_affine_Icc' (h : 0 < a) (b c d : K) : (a * 
· + b) '' Icc c d = Icc (a * c + b) (a * d + b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `[0,1]` under the homeomorphism `fun x ↦ a * x + b` is `[b, a+b]`.
-/
theorem affineHomeomorph_image_I (a b : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne.symm '' Set.Icc 0 1 = Set.Icc b (a + b) := by simp [h]

/-- The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
/-
**iccHomeoI** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜)
参数：a b : 𝕜；h : a < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine (e.trans ?_).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp

@[simp]
/-
**iccHomeoI_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iccHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) : ((iccHomeoI 
a b h) x : 𝕜) = (x - a) / (b - a)
参数：a b : 𝕜；h : a < b；x : Set.Icc a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iccHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) :
    ((iccHomeoI a b h) x : 𝕜) = (x - a) / (b - a) :=
  rfl

@[simp]
/-
**iccHomeoI_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iccHomeoI_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜
)) : ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a
参数：a b : 𝕜；h : a < b；x : Set.Icc (0 : 𝕜) (1 : 𝕜)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iccHomeoI_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜)) :
    ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a :=
  rfl

end

namespace unitInterval

open NNReal

/-- The coercion from `I` to `ℝ≥0`. -/
/-
**unitInterval.toNNReal** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：toNNReal : I -> Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `I` to `ℝ≥0`.
-/
def toNNReal : I → ℝ≥0 := fun i ↦ ⟨i.1, i.2.1⟩
/-
**unitInterval.toNNReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：unitInterval.toNNReal 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toNNReal_zero : toNNReal 0 = 0 := rfl
/-
**unitInterval.toNNReal_one** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：unitInterval.toNNReal 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toNNReal_one : toNNReal 1 = 1 := rfl
/-
**unitInterval.toNNReal_continuous** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：Continuous unitInterval.toNNReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
@[fun_prop] lemma toNNReal_continuous : Continuous toNNReal := by delta toNNReal; fun_prop
/-
**unitInterval.coe_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：∀ (x : ↑unitInterval), ↑(unitInterval.toNNReal x) = ↑x
参数：x : ↑unitInterval；unitInterval.toNNReal x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toNNReal (x : I) : ((toNNReal x) : ℝ) = x := rfl
/-
**unitInterval.toNNReal_add_toNNReal_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterva
l`。
形式化陈述：∀ (x : ↑unitInterval), unitInterval.toNNReal x + unitInterval.toNNReal (un
itInterval.symm x) = 1
参数：x : ↑unitInterval；unitInterval.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toNNReal_add_toNNReal_symm (x : I) : toNNReal x + toNNReal (σ x) = 1 := by ext; simp
/-
**unitInterval.toNNReal_symm_add_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `unitInterva
l`。
形式化陈述：∀ (x : ↑unitInterval), unitInterval.toNNReal (unitInterval.symm x) + unitI
nterval.toNNReal x = 1
参数：x : ↑unitInterval；unitInterval.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toNNReal_symm_add_toNNReal (x : I) : toNNReal (σ x) + toNNReal x = 1 := by ext; simp

end unitInterval

