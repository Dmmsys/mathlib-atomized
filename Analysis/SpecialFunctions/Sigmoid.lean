/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Sigmoid function

In this file we define the sigmoid function `x : ℝ ↦ (1 + exp (-x))⁻¹` and prove some of
its analytic properties.

We then show that the sigmoid function can be seen as an order embedding from `ℝ` to `I = [0, 1]`
and that this embedding is both a topological embedding and a measurable embedding. We also prove
that the composition of this embedding with the measurable embedding from a standard Borel space
`α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

### Sigmoid as a function from `ℝ` to `ℝ`
* `Real.sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `Real.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `Real.continuous_sigmoid` : the sigmoid function is continuous.
* `Real.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `Real.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.
* `Real.hasDerivAt_sigmoid` : the derivative of the sigmoid function.
* `Real.analyticAt_sigmoid` : the sigmoid function is analytic at every point.

### Sigmoid as a function from `ℝ` to `I`
* `unitInterval.sigmoid` : the sigmoid function from `ℝ` to `I`.
* `unitInterval.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `unitInterval.continuous_sigmoid` : the sigmoid function is continuous.
* `unitInterval.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `unitInterval.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `OrderEmbedding.sigmoid` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `Topology.isEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a topological
  embedding.
* `measurableEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a
  measurable embedding.
* `measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of the
  sigmoid function from `ℝ` to `I` with the measurable embedding from a standard Borel
  space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/

@[expose] public section

namespace Real

/-- The sigmoid function from `ℝ` to `ℝ`. -/
/-
**Real.sigmoid** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sigmoid (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sigmoid function from `ℝ` to `ℝ`.
-/
noncomputable def sigmoid (x : ℝ) := (1 + exp (-x))⁻¹
/-
**Real.sigmoid_def** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_def (x : Real) : sigmoid x = (1 + exp (-x))⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigmoid_def (x : ℝ) : sigmoid x = (1 + exp (-x))⁻¹ := rfl

@[simp]
/-
**Real.sigmoid_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_zero : sigmoid 0 = 2⁻¹
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma sigmoid_zero : sigmoid 0 = 2⁻¹ := by norm_num [sigmoid]

@[bound]
/-
**Real.sigmoid_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_pos (x : Real) : 0 < sigmoid x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]
/-
**Real.sigmoid_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_nonneg (x : Real) : 0 <= sigmoid x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.sigmoid_pos`：sigmoid_pos (x : Real) : 0 < sigmoid x
-/
lemma sigmoid_nonneg (x : ℝ) : 0 ≤ sigmoid x := (sigmoid_pos x).le

@[bound]
/-
**Real.sigmoid_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_lt_one (x : Real) : sigmoid x < 1
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 :=
  inv_lt_one_of_one_lt₀ <| (lt_add_iff_pos_right 1).mpr <| exp_pos _

@[bound]
/-
**Real.sigmoid_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_le_one (x : Real) : sigmoid x <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.sigmoid_lt_one`：sigmoid_lt_one (x : Real) : sigmoid x < 1
-/
lemma sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 := (sigmoid_lt_one x).le

@[gcongr, mono]
/-
**Real.sigmoid_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_strictMono : StrictMono sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a
-/
lemma sigmoid_strictMono : StrictMono sigmoid := fun a b hab ↦ by
  simp only [sigmoid]
  gcongr
/-
**Real.sigmoid_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Real.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := sigmoid_strictMono.le_iff_le

@[gcongr]
/-
**Real.sigmoid_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_le {a b : Real} : a <= b -> sigmoid a <= sigmoid b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.sigmoid_le_iff`：sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid 
b ↔ a <= b
-/
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr
/-
**Real.sigmoid_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Real.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := sigmoid_strictMono.lt_iff_lt

@[gcongr]
/-
**Real.sigmoid_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_lt {a b : Real} : a < b -> sigmoid a < sigmoid b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.sigmoid_lt_iff`：sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b
 ↔ a < b
-/
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
/-
**Real.sigmoid_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_monotone : Monotone sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Real.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone
/-
**Real.sigmoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_injective : Function.Injective sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Real.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
/-
**Real.sigmoid_inj** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_inj {a b : Real} : sigmoid a = sigmoid b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Real.sigmoid_injective`：sigmoid_injective : Function.Injective sigmoid
-/
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff
/-
**Real.sigmoid_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_neg (x : Real) : sigmoid (-x) = 1 - sigmoid x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
（共 47 条，此处仅展示前 30 条）
-/
lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = 1 - sigmoid x := by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : ℝ)]
/-
**Real.sigmoid_mul_rexp_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sigmoid_mul_rexp_neg (x : Real) : sigmoid x * exp (-x) = sigmoid (-x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.sigmoid_neg`：sigmoid_neg (x : Real) : sigmoid (-x) = 1 - sigmoid x
· 使用引理 `Real.sigmoid_def`：sigmoid_def (x : Real) : sigmoid x = (1 + exp (-x))⁻¹
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 58 条，此处仅展示前 30 条）
-/
lemma sigmoid_mul_rexp_neg (x : ℝ) : sigmoid x * exp (-x) = sigmoid (-x) := by
  rw [sigmoid_neg, sigmoid_def]
  field

open Set in
/-
**Real.range_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：range_sigmoid : range Real.sigmoid = Ioo 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Real.sigmoid_pos`：sigmoid_pos (x : Real) : 0 < sigmoid x
· 使用引理 `Real.sigmoid_lt_one`：sigmoid_lt_one (x : Real) : sigmoid x < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `one_lt_inv_iff₀`：one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where mp h
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_sigmoid : range Real.sigmoid = Ioo 0 1 := by
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro - ⟨x, rfl⟩
    push _ ∈ _
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

open Topology Filter
/-
**Real.tendsto_sigmoid_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.tendsto_exp_comp_nhds_zero`：tendsto_exp_comp_nhds_zero {f : α -> Re
al} : Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto f l atBot
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) := by
  simpa using! Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot |>.const_add 1 |>.inv₀ <|
    by norm_num
/-
**Real.tendsto_sigmoid_atBot** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.add_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : LinearOrder α]   [IsOrderedAdd
Monoid α] [Ord…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.tendsto_exp_comp_atTop`：tendsto_exp_comp_atTop {f : α -> Real} : Te
ndsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
-/
lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
    |>.inv_tendsto_atTop
/-
**Real.hasDerivAt_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_sigmoid (x : Real) : HasDerivAt sigmoid (sigmoid x * (1 - sigmo
id x)) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.sigmoid_neg`：sigmoid_neg (x : Real) : sigmoid (-x) = 1 - sigmoid x
· 使用引理 `Real.sigmoid_mul_rexp_neg`：sigmoid_mul_rexp_neg (x : Real) : sigmoid x *
 exp (-x) = sigmoid (-x)
· 使用引理 `Real.sigmoid_def`：sigmoid_def (x : Real) : sigmoid x = (1 + exp (-x))⁻¹
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 56 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_sigmoid (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  convert! (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg x, sigmoid_def]
  field [sq]
/-
**Real.deriv_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Real.hasDerivAt_sigmoid`：hasDerivAt_sigmoid (x : Real) : HasDerivAt sigm
oid (sigmoid x * (1 - sigmoid x)) x
-/
lemma deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) :=
  funext fun x => (hasDerivAt_sigmoid x).deriv

end Real

open Set Real

variable {x : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E}

@[fun_prop]
/-
**analyticAt_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticAt_sigmoid : AnalyticAt Real sigmoid x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.fun_inv`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {𝕝 :
 Type u_…
· 使用定理 `AnalyticAt.fun_add`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `AnalyticAt.rexp'`：AnalyticAt.rexp' {x : E} (fa : AnalyticAt Real f x) : 
AnalyticAt Real (fun z => exp (f z)) x
· 使用定理 `AnalyticAt.fun_neg`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_3} {F : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 …
· 使用引理 `analyticAt_id`：analyticAt_id : AnalyticAt 𝕜 (id : E -> E) z
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma analyticAt_sigmoid : AnalyticAt ℝ sigmoid x :=
  AnalyticAt.fun_inv (by fun_prop) (by positivity)

@[fun_prop]
/-
**AnalyticAt.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.sigmoid {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (s
igmoid ∘ f) x
参数：fa : AnalyticAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `analyticAt_sigmoid`：analyticAt_sigmoid : AnalyticAt Real sigmoid x
-/
lemma AnalyticAt.sigmoid {x : E} (fa : AnalyticAt ℝ f x) : AnalyticAt ℝ (sigmoid ∘ f) x :=
  analyticAt_sigmoid.comp fa

@[fun_prop]
/-
**AnalyticAt.sigmoid'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.sigmoid' {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (
fun z => Real.sigmoid (f z)) x
参数：fa : AnalyticAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.sigmoid`：AnalyticAt.sigmoid {x : E} (fa : AnalyticAt Real f x
) : AnalyticAt Real (sigmoid ∘ f) x
-/
lemma AnalyticAt.sigmoid' {x : E} (fa : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun z ↦ Real.sigmoid (f z)) x := fa.sigmoid
/-
**analyticOnNhd_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOnNhd_sigmoid : AnalyticOnNhd Real sigmoid Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `analyticAt_sigmoid`：analyticAt_sigmoid : AnalyticAt Real sigmoid x
-/
lemma analyticOnNhd_sigmoid : AnalyticOnNhd ℝ sigmoid Set.univ :=
  fun _ _ ↦ analyticAt_sigmoid
/-
**AnalyticOnNhd.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.sigmoid (fs : AnalyticOnNhd Real f s) : AnalyticOnNhd Real (
sigmoid ∘ f) s
参数：fs : AnalyticOnNhd Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用引理 `analyticAt_sigmoid`：analyticAt_sigmoid : AnalyticAt Real sigmoid x
-/
lemma AnalyticOnNhd.sigmoid (fs : AnalyticOnNhd ℝ f s) : AnalyticOnNhd ℝ (sigmoid ∘ f) s :=
  fun z n ↦ analyticAt_sigmoid.comp (fs z n)
/-
**analyticOn_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticOn_sigmoid : AnalyticOn Real sigmoid Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `analyticOnNhd_sigmoid`：analyticOnNhd_sigmoid : AnalyticOnNhd Real sigmoi
d Set.univ
-/
lemma analyticOn_sigmoid : AnalyticOn ℝ sigmoid Set.univ :=
  analyticOnNhd_sigmoid.analyticOn
/-
**AnalyticOn.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOn.sigmoid (fs : AnalyticOn Real f s) : AnalyticOn Real (sigmoid ∘
 f) s
参数：fs : AnalyticOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用引理 `analyticOnNhd_sigmoid`：analyticOnNhd_sigmoid : AnalyticOnNhd Real sigmoi
d Set.univ
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
lemma AnalyticOn.sigmoid (fs : AnalyticOn ℝ f s) : AnalyticOn ℝ (sigmoid ∘ f) s :=
  analyticOnNhd_sigmoid.comp_analyticOn fs (mapsTo_univ _ _)
/-
**analyticWithinAt_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：analyticWithinAt_sigmoid {s : Set Real} : AnalyticWithinAt Real sigmoid s 
x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticAt.analyticWithinAt`：AnalyticAt.analyticWithinAt (hf : AnalyticA
t 𝕜 f x) : AnalyticWithinAt 𝕜 f s x
· 使用引理 `analyticAt_sigmoid`：analyticAt_sigmoid : AnalyticAt Real sigmoid x
-/
lemma analyticWithinAt_sigmoid {s : Set ℝ} : AnalyticWithinAt ℝ sigmoid s x :=
  analyticAt_sigmoid.analyticWithinAt
/-
**AnalyticWithinAt.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.sigmoid {x : E} (fa : AnalyticWithinAt Real f s x) : Anal
yticWithinAt Real (sigmoid ∘ f) s x
参数：fa : AnalyticWithinAt Real f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.comp_analyticWithinAt`：AnalyticAt.comp_analyticWithinAt {g : 
F -> G} {f : E -> F} {x : E} {s : Set E} (hg : AnalyticAt 𝕜 g (f x)) (hf : Analy
ticWithinAt 𝕜 f s x) :…
· 使用引理 `analyticAt_sigmoid`：analyticAt_sigmoid : AnalyticAt Real sigmoid x
-/
lemma AnalyticWithinAt.sigmoid {x : E} (fa : AnalyticWithinAt ℝ f s x) :
  AnalyticWithinAt ℝ (sigmoid ∘ f) s x := analyticAt_sigmoid.comp_analyticWithinAt fa

open ContDiff in
@[fun_prop]
/-
**contDiff_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiff_sigmoid : ContDiff Real ω sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOn.contDiff`：AnalyticOn.contDiff (hf : AnalyticOn 𝕜 f univ) : Co
ntDiff 𝕜 n f
· 使用引理 `analyticOn_sigmoid`：analyticOn_sigmoid : AnalyticOn Real sigmoid Set.uni
v
-/
lemma contDiff_sigmoid : ContDiff ℝ ω sigmoid := analyticOn_sigmoid.contDiff

open ContDiff in
@[fun_prop]
/-
**ContDiff.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiff.sigmoid (hf : ContDiff Real ω f) : ContDiff Real ω (sigmoid ∘ f)
参数：hf : ContDiff Real ω f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用引理 `contDiff_sigmoid`：contDiff_sigmoid : ContDiff Real ω sigmoid
-/
lemma ContDiff.sigmoid (hf : ContDiff ℝ ω f) : ContDiff ℝ ω (sigmoid ∘ f) :=
  contDiff_sigmoid.comp hf

@[fun_prop]
/-
**differentiable_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiable_sigmoid : Differentiable Real sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.differentiable_one`：ContDiff.differentiable_one (h : ContDiff 𝕜
 1 f) : Differentiable 𝕜 f
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用引理 `contDiff_sigmoid`：contDiff_sigmoid : ContDiff Real ω sigmoid
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma differentiable_sigmoid : Differentiable ℝ sigmoid :=
  contDiff_sigmoid.of_le le_top |>.differentiable_one

@[fun_prop]
/-
**Differentiable.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.sigmoid (hf : Differentiable Real f) : Differentiable Real 
(sigmoid ∘ f)
参数：hf : Differentiable Real f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用引理 `differentiable_sigmoid`：differentiable_sigmoid : Differentiable Real sig
moid
-/
lemma Differentiable.sigmoid (hf : Differentiable ℝ f) : Differentiable ℝ (sigmoid ∘ f) :=
  differentiable_sigmoid.comp hf

@[fun_prop]
/-
**differentiableAt_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_sigmoid : DifferentiableAt Real sigmoid x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `differentiable_sigmoid`：differentiable_sigmoid : Differentiable Real sig
moid
-/
lemma differentiableAt_sigmoid : DifferentiableAt ℝ sigmoid x :=
  differentiable_sigmoid x

@[fun_prop]
/-
**DifferentiableAt.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sigmoid {x : E} (hf : DifferentiableAt Real f x) : Differ
entiableAt Real (sigmoid ∘ f) x
参数：hf : DifferentiableAt Real f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用引理 `differentiableAt_sigmoid`：differentiableAt_sigmoid : DifferentiableAt Re
al sigmoid x
-/
lemma DifferentiableAt.sigmoid {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (sigmoid ∘ f) x := differentiableAt_sigmoid.comp x hf

@[fun_prop]
/-
**continuous_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_sigmoid : Continuous sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `Differentiable.sigmoid`：Differentiable.sigmoid (hf : Differentiable Real
 f) : Differentiable Real (sigmoid ∘ f)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
lemma continuous_sigmoid : Continuous sigmoid := by
  apply Differentiable.continuous (𝕜 := ℝ)  -- fun_prop can't choose `𝕜`
  fun_prop

omit [NormedSpace ℝ E] in
@[fun_prop]
/-
**Continuous.sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.sigmoid (hf : Continuous f) : Continuous (sigmoid ∘ f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `continuous_sigmoid`：continuous_sigmoid : Continuous sigmoid
-/
lemma Continuous.sigmoid (hf : Continuous f) : Continuous (sigmoid ∘ f) :=
  continuous_sigmoid.comp hf

namespace unitInterval

/-- The sigmoid function from `ℝ` to `I`. -/
/-
**unitInterval.sigmoid** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：sigmoid : Real -> I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sigmoid function from `ℝ` to `I`.
-/
noncomputable def sigmoid : ℝ → I := Subtype.coind Real.sigmoid (fun _ ↦ ⟨by bound, by bound⟩)

@[bound]
/-
**unitInterval.sigmoid_pos** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_pos (x : Real) : 0 < sigmoid x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sigmoid_pos`：sigmoid_pos (x : Real) : 0 < sigmoid x
-/
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := Real.sigmoid_pos x

@[bound]
/-
**unitInterval.sigmoid_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_lt_one (x : Real) : sigmoid x < 1
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sigmoid_lt_one`：sigmoid_lt_one (x : Real) : sigmoid x < 1
-/
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := Real.sigmoid_lt_one x

@[gcongr, mono]
/-
**unitInterval.sigmoid_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_strictMono : StrictMono sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_strictMono : StrictMono sigmoid := Real.sigmoid_strictMono
/-
**unitInterval.sigmoid_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sigmoid_le_iff`：sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid 
b ↔ a <= b
-/
lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := Real.sigmoid_le_iff

@[gcongr]
/-
**unitInterval.sigmoid_le** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_le {a b : Real} : a <= b -> sigmoid a <= sigmoid b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `unitInterval.sigmoid_le_iff`：sigmoid_le_iff {a b : Real} : sigmoid a <= 
sigmoid b ↔ a <= b
-/
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr
/-
**unitInterval.sigmoid_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sigmoid_lt_iff`：sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b
 ↔ a < b
-/
lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := Real.sigmoid_lt_iff

@[gcongr]
/-
**unitInterval.sigmoid_lt** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_lt {a b : Real} : a < b -> sigmoid a < sigmoid b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `unitInterval.sigmoid_lt_iff`：sigmoid_lt_iff {a b : Real} : sigmoid a < s
igmoid b ↔ a < b
-/
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
/-
**unitInterval.sigmoid_monotone** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_monotone : Monotone sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `unitInterval.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone
/-
**unitInterval.sigmoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_injective : Function.Injective sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `unitInterval.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid
-/
lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
/-
**unitInterval.sigmoid_inj** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_inj {a b : Real} : sigmoid a = sigmoid b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `unitInterval.sigmoid_injective`：sigmoid_injective : Function.Injective s
igmoid
-/
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[fun_prop]
/-
**unitInterval.continuous_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：continuous_sigmoid : Continuous sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用引理 `continuous_sigmoid`：continuous_sigmoid : Continuous sigmoid
-/
lemma continuous_sigmoid : Continuous sigmoid := _root_.continuous_sigmoid.subtype_mk _
/-
**unitInterval.sigmoid_neg** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：sigmoid_neg (x : Real) : sigmoid (-x) = σ (sigmoid x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `Real.sigmoid_neg`：sigmoid_neg (x : Real) : sigmoid (-x) = 1 - sigmoid x
-/
lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = σ (sigmoid x) := by
  ext
  exact Real.sigmoid_neg x

set_option backward.isDefEq.respectTransparency false in
open Set in
/-
**unitInterval.range_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：range_sigmoid : range unitInterval.sigmoid = Ioo 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unitInterval.sigmoid.eq_1`：unitInterval.sigmoid = Subtype.coind Real.sig
moid unitInterval.sigmoid._proof_1
· 使用定理 `Set.Subtype.range_coind`：∀ {α : Type u} {β : Type v} (f : α → β) {p : β 
→ Prop} (h : ∀ (a : α), p (f a)),   Set.range (Subtype.coind f h) = Subtype.val 
⁻¹' Set.range…
· 使用引理 `Real.range_sigmoid`：range_sigmoid : range Real.sigmoid = Ioo 0 1
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_sigmoid : range unitInterval.sigmoid = Ioo 0 1 := by
  rw [sigmoid, Subtype.range_coind, Real.range_sigmoid]
  ext
  simp

open Topology Filter
/-
**unitInterval.tendsto_sigmoid_atTop** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用引理 `Real.tendsto_sigmoid_atTop`：tendsto_sigmoid_atTop : Tendsto sigmoid atTo
p (𝓝 1)
-/
lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop
/-
**unitInterval.tendsto_sigmoid_atBot** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
· 使用引理 `Real.tendsto_sigmoid_atBot`：tendsto_sigmoid_atBot : Tendsto sigmoid atBo
t (𝓝 0)
-/
lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

end unitInterval

section Embedding

open unitInterval Function Set

/-- The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`. -/
/-
**OrderEmbedding.sigmoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderEmbedding.sigmoid : Real ↪o I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `unitInterval.sigmoid_strictMono`：sigmoid_strictMono : StrictMono sigmoid

--- 原说明 ---
The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
-/
noncomputable def OrderEmbedding.sigmoid : ℝ ↪o I :=
  OrderEmbedding.ofStrictMono unitInterval.sigmoid unitInterval.sigmoid_strictMono
/-
**Topology.isEmbedding_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.isEmbedding_sigmoid : IsEmbedding unitInterval.sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderEmbedding.isEmbedding_of_ordConnected`：OrderEmbedding.isEmbedding_o
f_ordConnected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α
] [OrderTopology α] [Topological…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.ordConnected_of_Ioo`：ordConnected_of_Ioo {α : Type*} [PartialOrder α
] {s : Set α} (hs : forall x in s, forall y in s, x < y -> Ioo x y subseteq s) :
 OrdConnected…
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `unitInterval.range_sigmoid`：range_sigmoid : range unitInterval.sigmoid =
 Ioo 0 1
-/
lemma Topology.isEmbedding_sigmoid : IsEmbedding unitInterval.sigmoid :=
  OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => unitInterval.range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)
/-
**measurableEmbedding_sigmoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableEmbedding_sigmoid : MeasurableEmbedding unitInterval.sigmoid
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2
} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ : To
pologicalSpace β] [inst_2 : Me…
· 使用引理 `Topology.isEmbedding_sigmoid`：Topology.isEmbedding_sigmoid : IsEmbedding
 unitInterval.sigmoid
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Subtype.instOrderClosedTopology`：∀ {α : Type u} [inst : TopologicalSpace
 α] [inst_1 : Preorder α] [t : OrderClosedTopology α] {p : α → Prop},   OrderClo
sedTopology (Subtype …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `unitInterval.range_sigmoid`：range_sigmoid : range unitInterval.sigmoid =
 Ioo 0 1
-/
lemma measurableEmbedding_sigmoid : MeasurableEmbedding unitInterval.sigmoid :=
  Topology.isEmbedding_sigmoid.measurableEmbedding <| unitInterval.range_sigmoid ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]
/-
**measurableEmbedding_sigmoid_comp_embeddingReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableEmbedding_sigmoid_comp_embeddingReal : MeasurableEmbedding (unit
Interval.sigmoid ∘ MeasureTheory.embeddingReal α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.comp`：comp (hg : MeasurableEmbedding g) (hf : Measur
ableEmbedding f) : MeasurableEmbedding (g ∘ f)
· 使用引理 `measurableEmbedding_sigmoid`：measurableEmbedding_sigmoid : MeasurableEmb
edding unitInterval.sigmoid
· 使用引理 `MeasureTheory.measurableEmbedding_embeddingReal`：measurableEmbedding_emb
eddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : MeasurableEm
bedding (embeddingReal Ω)
-/
lemma measurableEmbedding_sigmoid_comp_embeddingReal :
    MeasurableEmbedding (unitInterval.sigmoid ∘ MeasureTheory.embeddingReal α) :=
  measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end Embedding

