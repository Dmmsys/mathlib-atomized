/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `Real.arsinh`: The inverse function of `Real.sinh`.

- `Real.sinhEquiv`, `Real.sinhOrderIso`, `Real.sinhHomeomorph`: `Real.sinh` as an `Equiv`,
  `OrderIso`, and `Homeomorph`, respectively.

## Main Results

- `Real.sinh_surjective`, `Real.sinh_bijective`: `Real.sinh` is surjective and bijective;

- `Real.arsinh_injective`, `Real.arsinh_surjective`, `Real.arsinh_bijective`: `Real.arsinh` is
  injective, surjective, and bijective;

- `Real.continuous_arsinh`, `Real.differentiable_arsinh`, `Real.contDiff_arsinh`: `Real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `Filter.Tendsto.arsinh` and `ContDiffAt.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/

@[expose] public section

noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + √(1 + x^2))`. -/
@[pp_nodot]
/-
**Real.arsinh** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：arsinh (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`arsinh` is defined using a logarithm, `arsinh x = log (x + √(1 + x^2))`.
-/
def arsinh (x : ℝ) :=
  log (x + √(1 + x ^ 2))
/-
**Real.exp_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_arsinh (x : Real) : exp (arsinh x) = x + √(1 + x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_lt_iff_pos_add'`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] 
[AddLeftStrictMono α] {a b : α}, -a < b ↔ 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.lt_sqrt_of_sq_lt`：lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem exp_arsinh (x : ℝ) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

@[simp]
/-
**Real.arsinh_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_zero : arsinh 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

@[simp]
/-
**Real.arsinh_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_neg (x : Real) : arsinh (-x) = -arsinh x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y
· 使用定理 `Real.exp_arsinh`：exp_arsinh (x : Real) : exp (arsinh x) = x + √(1 + x ^ 
2)
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x := by
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq, neg_add_eq_sub, add_comm x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp]
/-
**Real.sinh_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_arsinh (x : Real) : sinh (arsinh x) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_eq`：∀ (x : ℝ), Real.sinh x = (Real.exp x - Real.exp (-x)) / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.arsinh_neg`：arsinh_neg (x : Real) : arsinh (-x) = -arsinh x
· 使用定理 `Real.exp_arsinh`：exp_arsinh (x : Real) : exp (arsinh x) = x + √(1 + x ^ 
2)
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`arsinh` is the right inverse of `sinh`.
-/
theorem sinh_arsinh (x : ℝ) : sinh (arsinh x) = x := by
  rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq]; simp

@[simp]
/-
**Real.cosh_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_arsinh (x : Real) : cosh (arsinh x) = √(1 + x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x
· 使用定理 `Real.cosh_sq'`：cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
-/
theorem cosh_arsinh (x : ℝ) : cosh (arsinh x) = √(1 + x ^ 2) := by
  rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

@[simp]
/-
**Real.tanh_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_arsinh (x : Real) : tanh (arsinh x) = x / √(1 + x ^ 2)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.tanh_eq_sinh_div_cosh`：∀ (x : ℝ), Real.tanh x = Real.sinh x / Real.
cosh x
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
· 使用定理 `Real.cosh_arsinh`：cosh_arsinh (x : Real) : cosh (arsinh x) = √(1 + x ^ 2
)
-/
theorem tanh_arsinh (x : ℝ) : tanh (arsinh x) = x / √(1 + x ^ 2) := by
  rw [tanh_eq_sinh_div_cosh, sinh_arsinh, cosh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
/-
**Real.sinh_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_surjective : Surjective sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x

--- 原说明 ---
`sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b
`.
-/
theorem sinh_surjective : Surjective sinh :=
  LeftInverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
/-
**Real.sinh_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_bijective : Bijective sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sinh_injective`：sinh_injective : Function.Injective sinh
· 使用定理 `Real.sinh_surjective`：sinh_surjective : Surjective sinh

--- 原说明 ---
`sinh` is bijective, both injective and surjective.
-/
theorem sinh_bijective : Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp]
/-
**Real.arsinh_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_sinh (x : Real) : arsinh (sinh x) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.rightInverse_of_injective_of_leftInverse`：∀ {α : Sort u_1} {β :
 Sort u_2} {f : α → β} {g : β → α},   Function.Injective f → Function.LeftInvers
e f g → Function.RightInverse f g
· 使用定理 `Real.sinh_injective`：sinh_injective : Function.Injective sinh
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x

--- 原说明 ---
`arsinh` is the left inverse of `sinh`.
-/
theorem arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
  rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

/-- `Real.sinh` as an `Equiv`. -/
@[simps]
/-
**Real.sinhEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinhEquiv : Real ≃ Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arsinh_sinh`：arsinh_sinh (x : Real) : arsinh (sinh x) = x
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x

--- 原说明 ---
`Real.sinh` as an `Equiv`.
-/
def sinhEquiv : ℝ ≃ ℝ where
  toFun := sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

/-- `Real.sinh` as an `OrderIso`. -/
@[simps! -fullyApplied]
/-
**Real.sinhOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinhOrderIso : Real ≃o Real where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y

--- 原说明 ---
`Real.sinh` as an `OrderIso`.
-/
def sinhOrderIso : ℝ ≃o ℝ where
  toEquiv := sinhEquiv
  map_rel_iff' := @sinh_le_sinh

/-- `Real.sinh` as a `Homeomorph`. -/
@[simps! -fullyApplied]
/-
**Real.sinhHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinhHomeomorph : Real ≃ₜ Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ

--- 原说明 ---
`Real.sinh` as a `Homeomorph`.
-/
def sinhHomeomorph : ℝ ≃ₜ ℝ :=
  sinhOrderIso.toHomeomorph
/-
**Real.arsinh_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_bijective : Bijective arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem arsinh_bijective : Bijective arsinh :=
  sinhEquiv.symm.bijective
/-
**Real.arsinh_injective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_injective : Injective arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem arsinh_injective : Injective arsinh :=
  sinhEquiv.symm.injective
/-
**Real.arsinh_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_surjective : Surjective arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem arsinh_surjective : Surjective arsinh :=
  sinhEquiv.symm.surjective
/-
**Real.arsinh_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_strictMono : StrictMono arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
theorem arsinh_strictMono : StrictMono arsinh :=
  sinhOrderIso.symm.strictMono

@[simp]
/-
**Real.arsinh_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_inj : arsinh x = arsinh y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Real.arsinh_injective`：arsinh_injective : Injective arsinh
-/
theorem arsinh_inj : arsinh x = arsinh y ↔ x = y :=
  arsinh_injective.eq_iff

@[simp, gcongr]
/-
**Real.arsinh_le_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_le_arsinh : arsinh x <= arsinh y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
theorem arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y :=
  sinhOrderIso.symm.le_iff_le

@[simp]
/-
**Real.arsinh_lt_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
-/
theorem arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y :=
  sinhOrderIso.symm.lt_iff_lt

@[simp]
/-
**Real.arsinh_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Real.arsinh_injective`：arsinh_injective : Injective arsinh
· 使用定理 `Real.arsinh_zero`：arsinh_zero : arsinh 0 = 0
-/
theorem arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
  arsinh_injective.eq_iff' arsinh_zero

@[simp]
/-
**Real.arsinh_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_nonneg_iff : 0 <= arsinh x ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arsinh_nonneg_iff : 0 ≤ arsinh x ↔ 0 ≤ x := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
/-
**Real.arsinh_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_nonpos_iff : arsinh x <= 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arsinh_nonpos_iff : arsinh x ≤ 0 ↔ x ≤ 0 := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
/-
**Real.arsinh_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_pos_iff : 0 < arsinh x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.arsinh_nonpos_iff`：arsinh_nonpos_iff : arsinh x <= 0 ↔ x <= 0
-/
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]
/-
**Real.arsinh_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arsinh_neg_iff : arsinh x < 0 ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.arsinh_nonneg_iff`：arsinh_nonneg_iff : 0 <= arsinh x ↔ 0 <= x
-/
theorem arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arsinh_nonneg_iff
/-
**Real.hasStrictDerivAt_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_arsinh (x : Real) : HasStrictDerivAt arsinh (√(1 + x ^ 2)
)⁻¹ x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Real.cosh_arsinh`：cosh_arsinh (x : Real) : cosh (arsinh x) = √(1 + x ^ 2
)
· 使用定理 `OpenPartialHomeomorph.hasStrictDerivAt_symm`：OpenPartialHomeomorph.hasSt
rictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a in f.target)
 (hf' : f' != 0) (htff' : HasStri…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x
· 使用定理 `Real.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Real) : HasStrict
DerivAt sinh (cosh x) x
-/
theorem hasStrictDerivAt_arsinh (x : ℝ) : HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x := by
  convert!
    sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
      (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm
/-
**Real.hasDerivAt_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_arsinh`：hasStrictDerivAt_arsinh (x : Real) : HasSt
rictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
-/
theorem hasDerivAt_arsinh (x : ℝ) : HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x :=
  (hasStrictDerivAt_arsinh x).hasDerivAt

@[fun_prop]
/-
**Real.differentiable_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_arsinh : Differentiable Real arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_arsinh`：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh
 (√(1 + x ^ 2))⁻¹ x
-/
theorem differentiable_arsinh : Differentiable ℝ arsinh := fun x =>
  (hasDerivAt_arsinh x).differentiableAt

@[fun_prop]
/-
**Real.contDiff_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real n arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.contDiff_symm_deriv`：Homeomorph.contDiff_symm_deriv [Complete
Space 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 -> 𝕜} (h₀ : forall x, f' x != 0) (hf' : forall x, 
HasDerivAt f (f' x) …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem contDiff_arsinh {n : WithTop ℕ∞} : ContDiff ℝ n arsinh :=
  sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

@[continuity]
/-
**Real.continuous_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_arsinh : Continuous arsinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem continuous_arsinh : Continuous arsinh :=
  sinhHomeomorph.symm.continuous

/-- The function `Real.arsinh` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_arsinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_arsinh : AnalyticAt Real arsinh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh

--- 原说明 ---
The function `Real.arsinh` is real analytic.
-/
lemma analyticAt_arsinh : AnalyticAt ℝ arsinh x :=
  contDiff_arsinh.contDiffAt.analyticAt

/-- The function `Real.arsinh` is real analytic. -/
/-
**Real.analyticWithinAt_arsinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_arsinh {s : Set Real} : AnalyticWithinAt Real arsinh s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh

--- 原说明 ---
The function `Real.arsinh` is real analytic.
-/
lemma analyticWithinAt_arsinh {s : Set ℝ} : AnalyticWithinAt ℝ arsinh s x :=
  contDiff_arsinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.arsinh` is real analytic. -/
/-
**Real.analyticOnNhd_arsinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_arsinh {s : Set Real} : AnalyticOnNhd Real arsinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_arsinh`：analyticAt_arsinh : AnalyticAt Real arsinh x

--- 原说明 ---
The function `Real.arsinh` is real analytic.
-/
theorem analyticOnNhd_arsinh {s : Set ℝ} : AnalyticOnNhd ℝ arsinh s :=
  fun _ _ ↦ analyticAt_arsinh

/-- The function `Real.arsinh` is real analytic. -/
/-
**Real.analyticOn_arsinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_arsinh {s : Set Real} : AnalyticOn Real arsinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh

--- 原说明 ---
The function `Real.arsinh` is real analytic.
-/
lemma analyticOn_arsinh {s : Set ℝ} : AnalyticOn ℝ arsinh s :=
  contDiff_arsinh.contDiffOn.analyticOn

end Real

open Real

/-
**Filter.Tendsto.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.arsinh {α : Type*} {l : Filter α} {f : α -> Real} {a : Real
} (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a))
参数：h : Tendsto f l (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_arsinh`：continuous_arsinh : Continuous arsinh
-/
theorem Filter.Tendsto.arsinh {α : Type*} {l : Filter α} {f : α → ℝ} {a : ℝ}
    (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a)) :=
  (continuous_arsinh.tendsto _).comp h

section Continuous

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {a : X}

nonrec theorem ContinuousAt.arsinh (h : ContinuousAt f a) :
    ContinuousAt (fun x => arsinh (f x)) a :=
  h.arsinh

nonrec theorem ContinuousWithinAt.arsinh (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => arsinh (f x)) s a :=
  h.arsinh

/-
**ContinuousOn.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh
 (f x)) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.arsinh`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
{f : X → ℝ} {s : Set X} {a : X},   ContinuousWithinAt f s a → ContinuousWithinAt
 (fun x => Real…
-/
theorem ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh
/-
**Continuous.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x)
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Real.continuous_arsinh`：continuous_arsinh : Continuous arsinh
-/
theorem Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x) :=
  continuous_arsinh.comp h

end Continuous

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {s : Set E} {a : E}
  {f' : StrongDual ℝ E} {n : ℕ∞}

/-
**HasStrictFDerivAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.arsinh (hf : HasStrictFDerivAt f f' a) : HasStrictFDeriv
At (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a
参数：hf : HasStrictFDerivAt f f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_arsinh`：hasStrictDerivAt_arsinh (x : Real) : HasSt
rictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
-/
theorem HasStrictFDerivAt.arsinh (hf : HasStrictFDerivAt f f' a) :
    HasStrictFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf
/-
**HasFDerivAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.arsinh (hf : HasFDerivAt f f' a) : HasFDerivAt (fun x => arsin
h (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a
参数：hf : HasFDerivAt f f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_arsinh`：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh
 (√(1 + x ^ 2))⁻¹ x
-/
theorem HasFDerivAt.arsinh (hf : HasFDerivAt f f' a) :
    HasFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp_hasFDerivAt a hf
/-
**HasFDerivWithinAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.arsinh (hf : HasFDerivWithinAt f f' s a) : HasFDerivWith
inAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a
参数：hf : HasFDerivWithinAt f f' s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_arsinh`：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh
 (√(1 + x ^ 2))⁻¹ x
-/
theorem HasFDerivWithinAt.arsinh (hf : HasFDerivWithinAt f f' s a) :
    HasFDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

@[fun_prop]
/-
**DifferentiableAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.arsinh (h : DifferentiableAt Real f a) : DifferentiableAt
 Real (fun x => arsinh (f x)) a
参数：h : DifferentiableAt Real f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Real.differentiable_arsinh`：differentiable_arsinh : Differentiable Real 
arsinh
-/
theorem DifferentiableAt.arsinh (h : DifferentiableAt ℝ f a) :
    DifferentiableAt ℝ (fun x => arsinh (f x)) a :=
  (differentiable_arsinh _).comp a h

@[fun_prop]
/-
**DifferentiableWithinAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt Real f s a) : Di
fferentiableWithinAt Real (fun x => arsinh (f x)) s a
参数：h : DifferentiableWithinAt Real f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `Real.differentiable_arsinh`：differentiable_arsinh : Differentiable Real 
arsinh
-/
theorem DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt ℝ f s a) :
    DifferentiableWithinAt ℝ (fun x => arsinh (f x)) s a :=
  (differentiable_arsinh _).comp_differentiableWithinAt a h

@[fun_prop]
/-
**DifferentiableOn.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.arsinh (h : DifferentiableOn Real f s) : DifferentiableOn
 Real (fun x => arsinh (f x)) s
参数：h : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.arsinh`：DifferentiableWithinAt.arsinh (h : Differ
entiableWithinAt Real f s a) : DifferentiableWithinAt Real (fun x => arsinh (f x
)) s a
-/
theorem DifferentiableOn.arsinh (h : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => arsinh (f x)) s := fun x hx => (h x hx).arsinh

@[fun_prop]
/-
**Differentiable.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.arsinh (h : Differentiable Real f) : Differentiable Real fu
n x => arsinh (f x)
参数：h : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `Real.differentiable_arsinh`：differentiable_arsinh : Differentiable Real 
arsinh
-/
theorem Differentiable.arsinh (h : Differentiable ℝ f) : Differentiable ℝ fun x => arsinh (f x) :=
  differentiable_arsinh.comp h

@[fun_prop]
/-
**ContDiffAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.arsinh (h : ContDiffAt Real n f a) : ContDiffAt Real n (fun x =
> arsinh (f x)) a
参数：h : ContDiffAt Real n f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh
-/
theorem ContDiffAt.arsinh (h : ContDiffAt ℝ n f a) : ContDiffAt ℝ n (fun x => arsinh (f x)) a :=
  contDiff_arsinh.contDiffAt.comp a h

@[fun_prop]
/-
**ContDiffWithinAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.arsinh (h : ContDiffWithinAt Real n f s a) : ContDiffWith
inAt Real n (fun x => arsinh (f x)) s a
参数：h : ContDiffWithinAt Real n f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh
-/
theorem ContDiffWithinAt.arsinh (h : ContDiffWithinAt ℝ n f s a) :
    ContDiffWithinAt ℝ n (fun x => arsinh (f x)) s a :=
  contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

@[fun_prop]
/-
**ContDiff.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.arsinh (h : ContDiff Real n f) : ContDiff Real n fun x => arsinh 
(f x)
参数：h : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_arsinh`：contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real
 n arsinh
-/
theorem ContDiff.arsinh (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => arsinh (f x) :=
  contDiff_arsinh.comp h

@[fun_prop]
/-
**ContDiffOn.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.arsinh (h : ContDiffOn Real n f s) : ContDiffOn Real n (fun x =
> arsinh (f x)) s
参数：h : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.arsinh`：ContDiffWithinAt.arsinh (h : ContDiffWithinAt R
eal n f s a) : ContDiffWithinAt Real n (fun x => arsinh (f x)) s a
-/
theorem ContDiffOn.arsinh (h : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

end fderiv

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {a f' : ℝ}

/-
**HasStrictDerivAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) : HasStrictDerivAt 
(fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a
参数：hf : HasStrictDerivAt f f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Real.hasStrictDerivAt_arsinh`：hasStrictDerivAt_arsinh (x : Real) : HasSt
rictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
-/
theorem HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) :
    HasStrictDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp a hf
/-
**HasDerivAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.arsinh (hf : HasDerivAt f f' a) : HasDerivAt (fun x => arsinh (
f x)) ((√(1 + f a ^ 2))⁻¹ • f') a
参数：hf : HasDerivAt f f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_arsinh`：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh
 (√(1 + x ^ 2))⁻¹ x
-/
theorem HasDerivAt.arsinh (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp a hf
/-
**HasDerivWithinAt.arsinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) : HasDerivWithinA
t (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a
参数：hf : HasDerivWithinAt f f' s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_arsinh`：hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh
 (√(1 + x ^ 2))⁻¹ x
-/
theorem HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) :
    HasDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

end deriv

