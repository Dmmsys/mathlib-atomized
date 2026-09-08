/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
  # Norm on the complex numbers
-/

@[expose] public section

noncomputable section

open ComplexConjugate Topology Filter Set

namespace Complex
variable {z : ℂ}

@[no_expose]
/-
**Complex.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instNorm : Norm Complex where norm z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNorm : Norm ℂ where
  norm z := √(normSq z)
/-
**Complex.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_def (z : Complex) : ‖z‖ = √(normSq z)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (z : ℂ) : ‖z‖ = √(normSq z) := (rfl)
/-
**Complex.norm_mul_self_eq_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_mul_self_eq_normSq (z : Complex) : ‖z‖ * ‖z‖ = normSq z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
-/
theorem norm_mul_self_eq_normSq (z : ℂ) : ‖z‖ * ‖z‖ = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)
/-
**Complex.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), 0 ≤ ‖z‖
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
-/
protected theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
  Real.sqrt_nonneg _

@[bound]
/-
**Complex.abs_re_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Complex.norm_nonneg`：∀ (z : ℂ), 0 ≤ ‖z‖
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Complex.norm_mul_self_eq_normSq`：norm_mul_self_eq_normSq (z : Complex) :
 ‖z‖ * ‖z‖ = normSq z
· 使用定理 `Complex.re_sq_le_normSq`：re_sq_le_normSq (z : Complex) : z.re * z.re <= 
normSq z
-/
theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (Complex.norm_nonneg _), abs_mul_abs_self,
    norm_mul_self_eq_normSq]
  apply re_sq_le_normSq
/-
**Complex.re_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：re_le_norm (z : Complex) : z.re <= ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
-/
theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm _)).2
/-
**Complex.norm_add_le'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), ‖z + w‖ ≤ ‖z‖ + ‖w‖
参数：z w : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Complex.norm_nonneg`：∀ (z : ℂ), 0 ≤ ‖z‖
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_mul_self_eq_normSq`：norm_mul_self_eq_normSq (z : Complex) :
 ‖z‖ * ‖z‖ = normSq z
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_mul_self_eq`：add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a +
 2 * a * b + b * b
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Complex.normSq_add`：normSq_add (z w : Complex) : normSq (z + w) = normSq
 z + normSq w + 2 * (z * conj w).re
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `Complex.normSq_conj`：normSq_conj (z : Complex) : normSq (conj z) = normS
q z
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Complex.re_le_norm`：re_le_norm (z : Complex) : z.re <= ‖z‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 33 条，此处仅展示前 30 条）
-/
protected theorem norm_add_le' (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ :=
  (mul_self_le_mul_self_iff (Complex.norm_nonneg (z + w)) (add_nonneg (Complex.norm_nonneg z)
    (Complex.norm_nonneg w))).2 <| by
    rw [norm_mul_self_eq_normSq, add_mul_self_eq, norm_mul_self_eq_normSq, norm_mul_self_eq_normSq,
      add_right_comm, normSq_add, mul_assoc, norm_def, norm_def, ← Real.sqrt_mul <| normSq_nonneg z,
      ← normSq_conj w, ← map_mul]
    gcongr
    exact re_le_norm (z * conj w)
/-
**Complex.norm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {z : ℂ}, ‖z‖ = 0 ↔ z = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.sqrt_eq_zero`：sqrt_eq_zero (h : 0 <= x) : √x = 0 ↔ x = 0
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `Complex.normSq_eq_zero`：normSq_eq_zero {z : Complex} : normSq z = 0 ↔ z 
= 0
-/
protected theorem norm_eq_zero_iff {z : ℂ} : ‖z‖ = 0 ↔ z = 0 :=
  (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero
/-
**Complex.norm_map_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：‖0‖ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.norm_eq_zero_iff`：∀ {z : ℂ}, ‖z‖ = 0 ↔ z = 0
-/
protected theorem norm_map_zero' : ‖(0 : ℂ)‖ = 0 :=
  Complex.norm_eq_zero_iff.mpr rfl
/-
**Complex.norm_neg'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ‖-z‖ = ‖z‖
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_neg`：normSq_neg (z : Complex) : normSq (-z) = normSq z
-/
protected theorem norm_neg' (z : ℂ) : ‖-z‖ = ‖z‖ := by
  rw [Complex.norm_def, norm_def, normSq_neg]
/-
**Complex.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_map_zero'`：‖0‖ = 0
· 使用定理 `Complex.norm_add_le'`：∀ (z w : ℂ), ‖z + w‖ ≤ ‖z‖ + ‖w‖
· 使用定理 `Complex.norm_neg'`：∀ (z : ℂ), ‖-z‖ = ‖z‖
-/
instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
  { toFun := norm
    map_zero' := Complex.norm_map_zero'
    add_le' := Complex.norm_add_le'
    neg' := Complex.norm_neg'
    eq_zero_of_map_eq_zero' := fun _ ↦ Complex.norm_eq_zero_iff.mp }

@[simp 1100]
/-
**Complex.norm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
参数：z w : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_mul`：normSq_mul (z w : Complex) : normSq (z * w) = normSq
 z * normSq w
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
-/
protected theorem norm_mul (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

@[simp 1100]
/-
**Complex.norm_div** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z w : ℂ), ‖z / w‖ = ‖z‖ / ‖w‖
参数：z w : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_div`：normSq_div (z w : Complex) : normSq (z / w) = normSq
 z / normSq w
· 使用定理 `Real.sqrt_div`：sqrt_div {x : Real} (hx : 0 <= x) (y : Real) : √(x / y) =
 √x / √y
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
-/
protected theorem norm_div (z w : ℂ) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
  rw [norm_def, norm_def, norm_def, normSq_div, Real.sqrt_div (normSq_nonneg _)]
/-
**Complex.isAbsoluteValueNorm** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : Complex -> Real) where abv_no
nneg'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Complex.norm_eq_zero_iff`：∀ {z : ℂ}, ‖z‖ = 0 ↔ z = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
-/
instance isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : ℂ → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := Complex.norm_eq_zero_iff
  abv_add' := norm_add_le
  abv_mul' := Complex.norm_mul
/-
**Complex.norm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℕ), ‖z ^ n‖ = ‖z‖ ^ n
参数：z : ℂ；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
protected theorem norm_pow (z : ℂ) (n : ℕ) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_pow isAbsoluteValueNorm.abvHom _ _
/-
**Complex.norm_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ) (n : ℤ), ‖z ^ n‖ = ‖z‖ ^ n
参数：z : ℂ；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
protected theorem norm_zpow (z : ℂ) (n : ℤ) : ‖z ^ n‖ = ‖z‖ ^ n :=
  map_zpow₀ isAbsoluteValueNorm.abvHom _ _
/-
**Complex.norm_prod** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_1} (s : Finset ι) (f : ι → ℂ), ‖s.prod f‖ = ∏ i ∈ s, ‖f i‖
参数：s : Finset ι；f : ι → ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
protected theorem norm_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖s.prod f‖ = s.prod fun i ↦ ‖f i‖ :=
  map_prod isAbsoluteValueNorm.abvHom _ _
/-
**Complex.norm_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_conj`：normSq_conj (z : Complex) : normSq (conj z) = normS
q z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_conj (z : ℂ) : ‖conj z‖ = ‖z‖ := by simp [norm_def]
/-
**Complex.norm_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：‖Complex.I‖ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.normSq_I`：normSq_I : normSq I = 1
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma norm_I : ‖I‖ = 1 := by simp [norm]
/-
**Complex.nnnorm_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：‖Complex.I‖₊ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

@[simp 1100, norm_cast]
/-
**Complex.norm_real** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
· 使用定理 `Real.sqrt_mul_self_eq_abs`：sqrt_mul_self_eq_abs (x : Real) : √(x * x) = 
|x|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  simp [norm_def, Real.sqrt_mul_self_eq_abs]
/-
**Complex.norm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
  (norm_real _).trans (abs_of_nonneg h)

@[simp, norm_cast]
/-
**Complex.nnnorm_real** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：nnnorm_real (r : Real) : ‖(r : Complex)‖₊ = ‖r‖₊
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ := by ext; exact norm_real _

@[norm_cast]
/-
**Complex.norm_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_natCast (n : Nat) : ‖(n : Complex)‖ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := Complex.norm_of_nonneg n.cast_nonneg

@[simp 1100]
/-
**Complex.norm_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : Complex)‖ = OfNat.ofNat
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Complex)‖ = n
-/
lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖ = OfNat.ofNat n := norm_natCast n
/-
**Complex.norm_two** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：‖2‖ = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.norm_ofNat`：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : C
omplex)‖ = OfNat.ofNat n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
protected lemma norm_two : ‖(2 : ℂ)‖ = 2 := norm_ofNat 2

@[simp 1100, norm_cast]
/-
**Complex.nnnorm_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：nnnorm_natCast (n : Nat) : ‖(n : Complex)‖₊ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Complex)‖ = n
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = n := Subtype.ext <| by simp [norm_natCast]

@[simp 1100]
/-
**Complex.nnnorm_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：nnnorm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : Complex)‖₊ = OfNat.of
Nat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.nnnorm_natCast`：nnnorm_natCast (n : Nat) : ‖(n : Complex)‖₊ = n
-/
lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[simp 1100, norm_cast]
/-
**Complex.norm_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : Real)|
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_intCast`：∀ (n : ℤ), ↑↑n = ↑n
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
-/
lemma norm_intCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by
  rw [← ofReal_intCast, norm_real, Real.norm_eq_abs]
/-
**Complex.norm_int_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_int_of_nonneg {n : Int} (hn : 0 <= n) : ‖(n : Complex)‖ = n
参数：hn : 0 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [norm_intCast, ← Int.cast_abs, abs_of_nonneg hn]

@[simp 1100, norm_cast]
/-
**Complex.norm_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_ratCast (q : Rat) : ‖(q : Complex)‖ = |(q : Real)|
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := norm_real _

@[simp 1100, norm_cast]
/-
**Complex.norm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_nnratCast (q : Rat>=0) : ‖(q : Complex)‖ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
/-
**Complex.nnnorm_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：nnnorm_ratCast (q : Rat) : ‖(q : Complex)‖₊ = ‖(q : Real)‖₊
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.nnnorm_real`：nnnorm_real (r : Real) : ‖(r : Complex)‖₊ = ‖r‖₊
-/
lemma nnnorm_ratCast (q : ℚ) : ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊ := nnnorm_real q

@[simp 1100, norm_cast]
/-
**Complex.nnnorm_nnratCast** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：nnnorm_nnratCast (q : Rat>=0) : ‖(q : Complex)‖₊ = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Complex.norm_nnratCast`：norm_nnratCast (q : Rat>=0) : ‖(q : Complex)‖ = 
q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
-/
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖₊ = q := by simp [nnnorm]; rfl
/-
**Complex.normSq_eq_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：normSq_eq_norm_sq (z : Complex) : normSq z = ‖z‖ ^ 2
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  simp [norm_def, sq, Real.mul_self_sqrt (normSq_nonneg _)]
/-
**Complex.sq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (z : ℂ), ‖z‖ ^ 2 = Complex.normSq z
参数：z : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
-/
protected theorem sq_norm (z : ℂ) : ‖z‖ ^ 2 = normSq z := (normSq_eq_norm_sq z).symm
/-
**Complex.one_lt_normSq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：one_lt_normSq_iff {x : Complex} : 1 < normSq x ↔ 1 < ‖x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_lt_sq_iff₀`：one_lt_sq_iff₀ (ha : 0 <= a) : 1 < a ^ 2 ↔ 1 < a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_lt_normSq_iff {x : ℂ} : 1 < normSq x ↔ 1 < ‖x‖ := by
  rw [← one_lt_sq_iff₀ (norm_nonneg _), normSq_eq_norm_sq]
/-
**Complex.one_le_normSq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：one_le_normSq_iff {x : Complex} : 1 <= normSq x ↔ 1 <= ‖x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_le_sq_iff₀`：one_le_sq_iff₀ (ha : 0 <= a) : 1 <= a ^ 2 ↔ 1 <= a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_le_normSq_iff {x : ℂ} : 1 ≤ normSq x ↔ 1 ≤ ‖x‖ := by
  rw [← one_le_sq_iff₀ (norm_nonneg _), normSq_eq_norm_sq]

@[simp]
/-
**Complex.sq_norm_sub_sq_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sq_norm_sub_sq_re (z : Complex) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sq_norm`：∀ (z : ℂ), ‖z‖ ^ 2 = Complex.normSq z
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem sq_norm_sub_sq_re (z : ℂ) : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply, ← sq, ← sq, add_sub_cancel_left]

@[simp]
/-
**Complex.sq_norm_sub_sq_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sq_norm_sub_sq_im (z : Complex) : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.sq_norm_sub_sq_re`：sq_norm_sub_sq_re (z : Complex) : ‖z‖ ^ 2 - z
.re ^ 2 = z.im ^ 2
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
theorem sq_norm_sub_sq_im (z : ℂ) : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_norm_sub_sq_re, sub_sub_cancel]
/-
**Complex.norm_add_mul_I** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_add_mul_I (x y : Real) : ‖x + y * I‖ = √(x ^ 2 + y ^ 2)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.normSq_add_mul_I`：normSq_add_mul_I (x y : Real) : normSq (x + y 
* I) = x ^ 2 + y ^ 2
-/
lemma norm_add_mul_I (x y : ℝ) : ‖x + y * I‖ = √(x ^ 2 + y ^ 2) := by
  rw [← normSq_add_mul_I]; rfl
/-
**Complex.norm_eq_sqrt_sq_add_sq** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_eq_sqrt_sq_add_sq (z : Complex) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
lemma norm_eq_sqrt_sq_add_sq (z : ℂ) : ‖z‖ = √(z.re ^ 2 + z.im ^ 2) := by
  rw [norm_def, normSq_apply, sq, sq]

@[simp 1100]
/-
**Complex.range_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：(Set.range fun x => ‖x‖) = Set.Ici 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
-/
protected theorem range_norm : range (‖·‖ : ℂ → ℝ) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun x hx ↦ ⟨x, Complex.norm_of_nonneg hx⟩

@[simp]
/-
**Complex.range_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_normSq : range normSq = Ici 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.normSq_ofReal`：normSq_ofReal (r : Real) : normSq r = r * r
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
-/
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨√x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩
/-
**Complex.norm_le_abs_re_add_abs_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_le_abs_re_add_abs_im (z : Complex) : ‖z‖ <= |z.re| + |z.im|
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
    simpa [re_add_im] using norm_add_le (z.re : ℂ) (z.im * I)

@[bound]
/-
**Complex.abs_im_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.abs_le_sqrt`：abs_le_sqrt (h : x ^ 2 <= y) : |x| <= √y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
/-
**Complex.im_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：im_le_norm (z : Complex) : z.im <= ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
-/
theorem im_le_norm (z : ℂ) : z.im ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

@[simp]
/-
**Complex.abs_re_lt_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_re_lt_norm {z : Complex} : |z.re| < ‖z‖ ↔ z.im != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Real.lt_sqrt`：lt_sqrt (hx : 0 <= x) : x < √y ↔ x ^ 2 < y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
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
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abs_re_lt_norm {z : ℂ} : |z.re| < ‖z‖ ↔ z.im ≠ 0 := by
  rw [norm_def, Real.lt_sqrt (abs_nonneg _), normSq_apply, sq_abs, ← sq, lt_add_iff_pos_right,
    mul_self_pos]

@[simp]
/-
**Complex.abs_im_lt_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_im_lt_norm {z : Complex} : |z.im| < ‖z‖ ↔ z.re != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.abs_re_lt_norm`：abs_re_lt_norm {z : Complex} : |z.re| < ‖z‖ ↔ z.
im != 0
-/
theorem abs_im_lt_norm {z : ℂ} : |z.im| < ‖z‖ ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_norm (z * I)

@[simp]
/-
**Complex.abs_re_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：abs_re_eq_norm {z : Complex} : |z.re| = ‖z‖ ↔ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
· 使用定理 `Complex.abs_re_lt_norm`：abs_re_lt_norm {z : Complex} : |z.re| < ‖z‖ ↔ z.
im != 0
-/
lemma abs_re_eq_norm {z : ℂ} : |z.re| = ‖z‖ ↔ z.im = 0 :=
  not_iff_not.1 <| (abs_re_le_norm z).lt_iff_ne.symm.trans abs_re_lt_norm

@[simp]
/-
**Complex.abs_im_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：abs_im_eq_norm {z : Complex} : |z.im| = ‖z‖ ↔ z.re = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
· 使用定理 `Complex.abs_im_lt_norm`：abs_im_lt_norm {z : Complex} : |z.im| < ‖z‖ ↔ z.
re != 0
-/
lemma abs_im_eq_norm {z : ℂ} : |z.im| = ‖z‖ ↔ z.re = 0 :=
  not_iff_not.1 <| (abs_im_le_norm z).lt_iff_ne.symm.trans abs_im_lt_norm
/-
**Complex.norm_le_sqrt_two_mul_max** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_le_sqrt_two_mul_max (z : Complex) : ‖z‖ <= √2 * max |z.re| |z.im|
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
-/
theorem norm_le_sqrt_two_mul_max (z : ℂ) : ‖z‖ ≤ √2 * max |z.re| |z.im| := by
  obtain ⟨x, y⟩ := z
  simp only [norm_def, normSq_mk, norm_def, ← sq]
  set m := max |x| |y|
  have hm₀ : 0 ≤ m := by positivity
  calc
    √(x ^ 2 + y ^ 2) ≤ √(m ^ 2 + m ^ 2) := by
      gcongr √(?_ + ?_) <;> rw [sq_le_sq, abs_of_nonneg hm₀]
      exacts [le_max_left _ _, le_max_right _ _]
    _ = √2 * m := by
      rw [← two_mul, Real.sqrt_mul, Real.sqrt_sq] <;> positivity
/-
**Complex.abs_re_div_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_re_div_norm_le_one (z : Complex) : |z.re / ‖z‖| <= 1
参数：z : Complex。
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem abs_re_div_norm_le_one (z : ℂ) : |z.re / ‖z‖| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_re_le_norm]
/-
**Complex.abs_im_div_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_im_div_norm_le_one (z : Complex) : |z.im / ‖z‖| <= 1
参数：z : Complex。
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem abs_im_div_norm_le_one (z : ℂ) : |z.im / ‖z‖| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    simp_rw [_root_.abs_div, abs_norm, div_le_iff₀ (norm_pos_iff.mpr hz), one_mul, abs_im_le_norm]
/-
**Complex.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_eq (z w : Complex) : dist z w = ‖z - w‖
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
-/
theorem dist_eq (z w : ℂ) : dist z w = ‖z - w‖ := dist_eq_norm _ _
/-
**Complex.dist_eq_re_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_eq_re_im (z w : Complex) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w
.im) ^ 2)
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
-/
theorem dist_eq_re_im (z w : ℂ) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq, dist_eq]
  rfl

@[simp]
/-
**Complex.dist_mk** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_mk (x₁ y₁ x₂ y₂ : Real) : dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 
2 + (y₁ - y₂) ^ 2)
参数：x₁ y₁ x₂ y₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.dist_eq_re_im`：dist_eq_re_im (z w : Complex) : dist z w = √((z.r
e - w.re) ^ 2 + (z.im - w.im) ^ 2)
-/
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _
/-
**Complex.dist_of_re_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_of_re_eq {z w : Complex} (h : z.re = w.re) : dist z w = dist z.im w.i
m
参数：h : z.re = w.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.dist_eq_re_im`：dist_eq_re_im (z w : Complex) : dist z w = √((z.r
e - w.re) ^ 2 + (z.im - w.im) ^ 2)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
-/
theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]
/-
**Complex.nndist_of_re_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nndist_of_re_eq {z w : Complex} (h : z.re = w.re) : nndist z w = nndist z.
im w.im
参数：h : z.re = w.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Complex.dist_of_re_eq`：dist_of_re_eq {z w : Complex} (h : z.re = w.re) :
 dist z w = dist z.im w.im
-/
theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h
/-
**Complex.edist_of_re_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：edist_of_re_eq {z w : Complex} (h : z.re = w.re) : edist z w = edist z.im 
w.im
参数：h : z.re = w.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Complex.nndist_of_re_eq`：nndist_of_re_eq {z w : Complex} (h : z.re = w.r
e) : nndist z w = nndist z.im w.im
-/
theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]
/-
**Complex.dist_of_im_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_of_im_eq {z w : Complex} (h : z.im = w.im) : dist z w = dist z.re w.r
e
参数：h : z.im = w.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.dist_eq_re_im`：dist_eq_re_im (z w : Complex) : dist z w = √((z.r
e - w.re) ^ 2 + (z.im - w.im) ^ 2)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
-/
theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]
/-
**Complex.nndist_of_im_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nndist_of_im_eq {z w : Complex} (h : z.im = w.im) : nndist z w = nndist z.
re w.re
参数：h : z.im = w.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Complex.dist_of_im_eq`：dist_of_im_eq {z w : Complex} (h : z.im = w.im) :
 dist z w = dist z.re w.re
-/
theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h
/-
**Complex.edist_of_im_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：edist_of_im_eq {z w : Complex} (h : z.im = w.im) : edist z w = edist z.re 
w.re
参数：h : z.im = w.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Complex.nndist_of_im_eq`：nndist_of_im_eq {z w : Complex} (h : z.im = w.i
m) : nndist z w = nndist z.re w.re
-/
theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]
/-
**Complex.dist_conj_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_conj_self (z : Complex) : dist (conj z) z = 2 * |z.im|
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.dist_of_re_eq`：dist_of_re_eq {z w : Complex} (h : z.re = w.re) :
 dist z w = dist z.im w.im
· 使用定理 `Complex.conj_re`：conj_re (z : Complex) : (conj z).re = z.re
· 使用定理 `Complex.conj_im`：conj_im (z : Complex) : (conj z).im = -z.im
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]
/-
**Complex.nndist_conj_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nndist_conj_self (z : Complex) : nndist (conj z) z = 2 * Real.nnabs z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.coe_two`：↑2 = 2
· 使用定理 `Real.coe_nnabs`：coe_nnabs (x : Real) : (nnabs x : Real) = |x|
· 使用定理 `Complex.dist_conj_self`：dist_conj_self (z : Complex) : dist (conj z) z =
 2 * |z.im|
-/
theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]
/-
**Complex.dist_self_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：dist_self_conj (z : Complex) : dist z (conj z) = 2 * |z.im|
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Complex.dist_conj_self`：dist_conj_self (z : Complex) : dist (conj z) z =
 2 * |z.im|
-/
theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]
/-
**Complex.nndist_self_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：nndist_self_conj (z : Complex) : nndist z (conj z) = 2 * Real.nnabs z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
· 使用定理 `Complex.nndist_conj_self`：nndist_conj_self (z : Complex) : nndist (conj 
z) z = 2 * Real.nnabs z.im
-/
theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]

/-! ### Cauchy sequences -/

/-
**Complex.isCauSeq_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq abs fun n => (f n).re
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
· 使用定理 `CauSeq.cauchy`：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i
, forall j >= i, abv (f j - f i) < ε

--- 原说明 ---
### Cauchy sequences
-/
theorem isCauSeq_re (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).re := fun _ ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦
    lt_of_le_of_lt (by simpa using abs_re_le_norm (f j - f i)) (H _ ij)
/-
**Complex.isCauSeq_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq abs fun n => (f n).im
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
· 使用定理 `CauSeq.cauchy`：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i
, forall j >= i, abv (f j - f i) < ε
-/
theorem isCauSeq_im (f : CauSeq ℂ (‖·‖)) : IsCauSeq abs fun n ↦ (f n).im := fun ε ε0 ↦
  (f.cauchy ε0).imp fun i H j ij ↦ by
    simpa only [← ofReal_sub, norm_real, sub_re, sub_im] using (abs_im_le_norm _).trans_lt <| H _ ij

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
/-
**Complex.cauSeqRe** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cauSeqRe (f : CauSeq Complex (‖·‖)) : CauSeq Real abs
参数：f : CauSeq Complex (‖·‖)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isCauSeq_re`：isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).re

--- 原说明 ---
The real part of a complex Cauchy sequence, as a real Cauchy sequence.
-/
noncomputable def cauSeqRe (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
/-
**Complex.cauSeqIm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cauSeqIm (f : CauSeq Complex (‖·‖)) : CauSeq Real abs
参数：f : CauSeq Complex (‖·‖)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isCauSeq_im`：isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).im

--- 原说明 ---
The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence.
-/
noncomputable def cauSeqIm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩
/-
**Complex.isCauSeq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCauSeq_norm {f : Nat -> Complex} (hf : IsCauSeq (‖·‖) f) : IsCauSeq abs 
((‖·‖) ∘ f)
参数：hf : IsCauSeq (‖·‖) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `abs_norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E]
 (a b : E), |‖a‖ - ‖b‖| ≤ ‖a - b‖
-/
theorem isCauSeq_norm {f : ℕ → ℂ} (hf : IsCauSeq (‖·‖) f) :
    IsCauSeq abs ((‖·‖) ∘ f) := fun ε ε0 ↦
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj ↦ lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
/-
**Complex.limAux** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：limAux (f : CauSeq Complex (‖·‖)) : Complex
参数：f : CauSeq Complex (‖·‖)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs

--- 原说明 ---
The limit of a Cauchy sequence of complex numbers.
-/
noncomputable def limAux (f : CauSeq ℂ (‖·‖)) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩
/-
**Complex.equiv_limAux** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：equiv_limAux (f : CauSeq Complex (‖·‖)) : f ≈ CauSeq.const (‖·‖) (limAux f
)
参数：f : CauSeq Complex (‖·‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Complex.isCauSeq_re`：isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).re
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isCauSeq_im`：isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).im
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Complex.norm_le_abs_re_add_abs_im`：norm_le_abs_re_add_abs_im (z : Comple
x) : ‖z‖ <= |z.re| + |z.im|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
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
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem equiv_limAux (f : CauSeq ℂ (‖·‖)) :
    f ≈ CauSeq.const (‖·‖) (limAux f) := fun ε ε0 ↦
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun _ H j ij ↦ by
    obtain ⟨H₁, H₂⟩ := H _ ij
    apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
    simpa using! add_lt_add H₁ H₂
/-
**Complex.instIsComplete** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
形式化陈述：instIsComplete : CauSeq.IsComplete Complex (‖·‖)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.equiv_limAux`：equiv_limAux (f : CauSeq Complex (‖·‖)) : f ≈ CauS
eq.const (‖·‖) (limAux f)
-/
instance instIsComplete : CauSeq.IsComplete ℂ (‖·‖) :=
  ⟨fun f ↦ ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq
/-
**Complex.lim_eq_lim_im_add_lim_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lim_eq_lim_im_add_lim_re (f : CauSeq Complex (‖·‖)) : lim f = ↑(lim (cauSe
qRe f)) + ↑(lim (cauSeqIm f)) * I
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `Complex.equiv_limAux`：equiv_limAux (f : CauSeq Complex (‖·‖)) : f ≈ CauS
eq.const (‖·‖) (limAux f)
· 使用定理 `CauSeq.ext`：ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.isCauSeq_re`：isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).re
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.isCauSeq_im`：isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).im
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ (‖·‖)) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    letI : IsAbsoluteValue (‖·‖ : ℂ → ℝ) := inferInstance
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const (‖·‖) (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ ↦
          Complex.ext (by simp [limAux, cauSeqRe, ofReal]) (by simp [limAux, cauSeqIm, ofReal])
/-
**Complex.lim_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lim_re (f : CauSeq Complex (‖·‖)) : lim (cauSeqRe f) = (lim f).re
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.lim_eq_lim_im_add_lim_re`：lim_eq_lim_im_add_lim_re (f : CauSeq C
omplex (‖·‖)) : lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lim_re (f : CauSeq ℂ (‖·‖)) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]
/-
**Complex.lim_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lim_im (f : CauSeq Complex (‖·‖)) : lim (cauSeqIm f) = (lim f).im
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.lim_eq_lim_im_add_lim_re`：lim_eq_lim_im_add_lim_re (f : CauSeq C
omplex (‖·‖)) : lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lim_im (f : CauSeq ℂ (‖·‖)) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal]
/-
**Complex.isCauSeq_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCauSeq_conj (f : CauSeq Complex (‖·‖)) : IsCauSeq (‖·‖) fun n => conj (f
 n)
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
-/
theorem isCauSeq_conj (f : CauSeq ℂ (‖·‖)) :
    IsCauSeq (‖·‖) fun n ↦ conj (f n) := fun ε ε0 ↦
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    simp_rw [← map_sub, norm_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
/-
**Complex.cauSeqConj** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cauSeqConj (f : CauSeq Complex (‖·‖)) : CauSeq Complex (‖·‖)
参数：f : CauSeq Complex (‖·‖)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isCauSeq_conj`：isCauSeq_conj (f : CauSeq Complex (‖·‖)) : IsCauS
eq (‖·‖) fun n => conj (f n)

--- 原说明 ---
The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence
.
-/
noncomputable def cauSeqConj (f : CauSeq ℂ (‖·‖)) : CauSeq ℂ (‖·‖) :=
  ⟨_, isCauSeq_conj f⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Complex.lim_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lim_conj (f : CauSeq Complex (‖·‖)) : lim (cauSeqConj f) = conj (lim f)
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `Complex.isCauSeq_conj`：isCauSeq_conj (f : CauSeq Complex (‖·‖)) : IsCauS
eq (‖·‖) fun n => conj (f n)
· 使用定理 `Complex.isCauSeq_re`：isCauSeq_re (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.lim_re`：lim_re (f : CauSeq Complex (‖·‖)) : lim (cauSeqRe f) = (
lim f).re
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.isCauSeq_im`：isCauSeq_im (f : CauSeq Complex (‖·‖)) : IsCauSeq a
bs fun n => (f n).im
· 使用定理 `Complex.lim_im`：lim_im (f : CauSeq Complex (‖·‖)) : lim (cauSeqIm f) = (
lim f).im
· 使用定理 `CauSeq.lim_neg`：lim_neg (f : CauSeq β abv) : lim (-f) = -lim f
-/
theorem lim_conj (f : CauSeq ℂ (‖·‖)) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

/-- The norm of a complex Cauchy sequence, as a real Cauchy sequence. -/
/-
**Complex.cauSeqNorm** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cauSeqNorm (f : CauSeq Complex (‖·‖)) : CauSeq Real abs
参数：f : CauSeq Complex (‖·‖)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of a complex Cauchy sequence, as a real Cauchy sequence.
-/
noncomputable def cauSeqNorm (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_norm f.2⟩
/-
**Complex.lim_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：lim_norm (f : CauSeq Complex (‖·‖)) : lim (cauSeqNorm f) = ‖lim f‖
参数：f : CauSeq Complex (‖·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lim_eq_of_equiv_const`：lim_eq_of_equiv_const {f : CauSeq β abv} {
x : β} (h : f ≈ CauSeq.const abv x) : lim f = x
· 使用定理 `Real.instIsCompleteAbs`：CauSeq.IsComplete ℝ abs
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `abs_norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E]
 (a b : E), |‖a‖ - ‖b‖| ≤ ‖a - b‖
-/
theorem lim_norm (f : CauSeq ℂ (‖·‖)) : lim (cauSeqNorm f) = ‖lim f‖ :=
  lim_eq_of_equiv_const fun ε ε0 ↦
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
/-
**Complex.ne_zero_of_re_pos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : s != 0
参数：hs : 0 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
-/
lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 :=
  fun h ↦ (zero_re ▸ h ▸ hs).false
/-
**Complex.ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : s != 0
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_re_pos`：ne_zero_of_re_pos {s : Complex} (hs : 0 < s.r
e) : s != 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 :=
  ne_zero_of_re_pos <| zero_lt_one.trans hs
/-
**Complex.re_neg_ne_zero_of_re_pos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_neg_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : (-s).re != 0
参数：hs : 0 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
-/
lemma re_neg_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : (-s).re ≠ 0 :=
  ne_iff_lt_or_gt.mpr <| Or.inl <| neg_re s ▸ (neg_lt_zero.mpr hs)
/-
**Complex.re_neg_ne_zero_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：re_neg_ne_zero_of_one_lt_re {s : Complex} (hs : 1 < s.re) : (-s).re != 0
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.re_neg_ne_zero_of_re_pos`：re_neg_ne_zero_of_re_pos {s : Complex}
 (hs : 0 < s.re) : (-s).re != 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma re_neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : (-s).re ≠ 0 :=
  re_neg_ne_zero_of_re_pos <| zero_lt_one.trans hs
/-
**Complex.norm_sub_one_sq_eq_of_norm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_sub_one_sq_eq_of_norm_eq_one {z : Complex} (hz : ‖z‖ = 1) : ‖z - 1‖ ^
 2 = 2 * (1 - z.re)
参数：hz : ‖z‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 63 条，此处仅展示前 30 条）
-/
lemma norm_sub_one_sq_eq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have : z.im * z.im = 1 - z.re * z.re := by
    replace hz := sq_eq_one_iff.mpr (.inl hz)
    rw [Complex.sq_norm, normSq_apply] at hz
    linarith
  simp [Complex.sq_norm, normSq_apply, this]
  ring
/-
**Complex.norm_sub_one_sq_eqOn_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_sub_one_sq_eqOn_sphere : (Metric.sphere (0 : Complex) 1).EqOn (‖· - 1
‖ ^ 2) (fun z => 2 * (1 - z.re))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.norm_sub_one_sq_eq_of_norm_eq_one`：norm_sub_one_sq_eq_of_norm_eq
_one {z : Complex} (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 * (1 - z.re)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma norm_sub_one_sq_eqOn_sphere :
    (Metric.sphere (0 : ℂ) 1).EqOn (‖· - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
  fun z hz ↦ norm_sub_one_sq_eq_of_norm_eq_one (by simpa using hz)
/-
**Complex.normSq_ofReal_add_I_mul_sqrt_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：normSq_ofReal_add_I_mul_sqrt_one_sub {x : Real} (hx : ‖x‖ <= 1) : normSq (
x + I * √(1 - x ^ 2)) = 1
参数：hx : ‖x‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.normSq_add_mul_I`：normSq_add_mul_I (x y : Real) : normSq (x + y 
* I) = x ^ 2 + y ^ 2
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
（共 75 条，此处仅展示前 30 条）
-/
lemma normSq_ofReal_add_I_mul_sqrt_one_sub {x : ℝ} (hx : ‖x‖ ≤ 1) :
    normSq (x + I * √(1 - x ^ 2)) = 1 := by
  simp [mul_comm I, normSq_add_mul_I,
    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]
/-
**Complex.normSq_ofReal_sub_I_mul_sqrt_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：normSq_ofReal_sub_I_mul_sqrt_one_sub {x : Real} (hx : ‖x‖ <= 1) : normSq (
x - I * √(1 - x ^ 2)) = 1
参数：hx : ‖x‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.normSq_neg`：normSq_neg (z : Complex) : normSq (-z) = normSq z
· 使用定理 `neg_sub'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a - b) = -a - -b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.normSq_ofReal_add_I_mul_sqrt_one_sub`：normSq_ofReal_add_I_mul_sq
rt_one_sub {x : Real} (hx : ‖x‖ <= 1) : normSq (x + I * √(1 - x ^ 2)) = 1
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
lemma normSq_ofReal_sub_I_mul_sqrt_one_sub {x : ℝ} (hx : ‖x‖ ≤ 1) :
    normSq (x - I * √(1 - x ^ 2)) = 1 := by
  rw [← normSq_neg, neg_sub', sub_neg_eq_add]
  simpa using normSq_ofReal_add_I_mul_sqrt_one_sub (x := -x) (by simpa)

end Complex

