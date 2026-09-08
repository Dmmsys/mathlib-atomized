/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Order.Lattice

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `NormedLatticeAddCommGroup` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

public section


/-!
### Normed lattice ordered groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

section SolidNorm

/-- Let `α` be an `AddCommGroup` with a `Lattice` structure. A norm on `α` is *solid* if, for `a`
and `b` in `α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`.
-/
/-
**HasSolidNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [NormedAddCommGroup α] → [Lattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `α` be an `AddCommGroup` with a `Lattice` structure. A norm on `α` is *solid
* if, for `a`
and `b` in `α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` i
mplies `‖a‖ ≤ ‖b‖`.
-/
class HasSolidNorm (α : Type*) [NormedAddCommGroup α] [Lattice α] : Prop where
  solid : ∀ ⦃x y : α⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α]
/-
**norm_le_norm_of_abs_le_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_norm_of_abs_le_abs {a b : α} (h : |a| <= |b|) : ‖a‖ <= ‖b‖
参数：h : |a| <= |b|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
-/
theorem norm_le_norm_of_abs_le_abs {a b : α} (h : |a| ≤ |b|) : ‖a‖ ≤ ‖b‖ :=
  HasSolidNorm.solid h

/-- If `α` has a solid norm, then the balls centered at the origin of `α` are solid sets. -/
/-
**LatticeOrderedAddCommGroup.isSolid_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LatticeOrderedAddCommGroup.isSolid_ball (r : Real) : LatticeOrderedAddComm
Group.IsSolid (Metric.ball (0 : α) r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
If `α` has a solid norm, then the balls centered at the origin of `α` are solid 
sets.
-/
theorem LatticeOrderedAddCommGroup.isSolid_ball (r : ℝ) :
    LatticeOrderedAddCommGroup.IsSolid (Metric.ball (0 : α) r) := fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSolidNorm ℝ := ⟨fun _ _ => id⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSolidNorm ℚ := ⟨fun _ _ _ => by simpa only [norm, ← Rat.cast_abs, Rat.cast_le]⟩
/-
**Int.hasSolidNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.hasSolidNorm : HasSolidNorm Int where solid x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
instance Int.hasSolidNorm : HasSolidNorm ℤ where
  solid x y h := by simpa [← Int.norm_cast_real, ← Int.cast_abs] using h

end SolidNorm

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α]

open HasSolidNorm

/-
**dual_solid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dual_solid (a b : α) (h : b ⊓ -b <= a ⊓ -a) : ‖a‖ <= ‖b‖
参数：a b : α；h : b ⊓ -b <= a ⊓ -a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a :
 α), |a| = a ⊔ -a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_inf`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a b : α), -(a ⊓ b) = -a ⊔ -b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem dual_solid (a b : α) (h : b ⊓ -b ≤ a ⊓ -a) : ‖a‖ ≤ ‖b‖ := by
  apply solid
  rw [abs]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, inf_comm _ b, inf_comm _ a]

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) OrderDual.instHasSolidNorm :
    HasSolidNorm αᵒᵈ :=
  { solid := dual_solid (α := α) }
/-
**norm_abs_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)
/-
**norm_inf_sub_inf_le_add_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ <= ‖a - c‖ + 
‖b - d‖
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_abs_eq_norm`：norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `abs_inf_sub_inf_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ad
dCommGroup α] [AddLeftMono α] (a b c : α), |a ⊓ c - b ⊓ c| ≤ |a - b|
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_inf_sub_inf_le_abs _ _ _
      · rw [inf_comm c, inf_comm c]
        exact abs_inf_sub_inf_le_abs _ _ _
/-
**norm_sup_sub_sup_le_add_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ <= ‖a - c‖ + 
‖b - d‖
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_abs_eq_norm`：norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `abs_sup_sub_sup_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ad
dCommGroup α] [AddLeftMono α] (a b c : α), |a ⊔ c - b ⊔ c| ≤ |a - b|
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [sup_comm c, sup_comm c]
        exact abs_sup_sub_sup_le_abs _ _ _
/-
**norm_inf_le_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inf_le_add (x y : α) : ‖x ⊓ y‖ <= ‖x‖ + ‖y‖
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_inf_sub_inf_le_add_norm`：norm_inf_sub_inf_le_add_norm (a b c d : α)
 : ‖a ⊓ b - c ⊓ d‖ <= ‖a - c‖ + ‖b - d‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h
/-
**norm_sup_le_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sup_le_add (x y : α) : ‖x ⊔ y‖ <= ‖x‖ + ‖y‖
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_sup_sub_sup_le_add_norm`：norm_sup_sub_sup_le_add_norm (a b c d : α)
 : ‖a ⊔ b - c ⊔ d‖ <= ‖a - c‖ + ‖b - d‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuou
s.
-/
instance (priority := 100) HasSolidNorm.continuousInf : ContinuousInf α := by
  refine ⟨continuous_iff_continuousAt.2 fun q => tendsto_iff_norm_sub_tendsto_zero.2 <| ?_⟩
  have : ∀ p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := fun _ =>
    norm_inf_sub_inf_le_add_norm _ _ _ _
  refine squeeze_zero (fun e => norm_nonneg _) this ?_
  convert!
    ((continuous_fst.tendsto q).sub <| tendsto_const_nhds).norm.add
      ((continuous_snd.tendsto q).sub <| tendsto_const_nhds).norm
  simp

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HasSolidNorm.continuousSup {α : Type*}
    [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α] : ContinuousSup α :=
  OrderDual.continuousSup αᵒᵈ

-- see Note [lower instance priority]
/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in 
the norm topology.
-/
instance (priority := 100) HasSolidNorm.toTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk
/-
**norm_abs_sub_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ <= ‖a - b‖
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `abs_abs_sub_abs_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCom
mGroup α] [AddLeftMono α] (a b : α), ||a| - |b|| ≤ |a - b|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ ≤ ‖a - b‖ := solid (abs_abs_sub_abs_le _ _)
/-
**norm_sup_sub_sup_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ <= ‖x - y‖
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `abs_sup_sub_sup_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ad
dCommGroup α] [AddLeftMono α] (a b c : α), |a ⊔ c - b ⊔ c| ≤ |a - b|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ ≤ ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)
/-
**norm_inf_sub_inf_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ <= ‖x - y‖
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
· 使用定理 `abs_inf_sub_inf_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ad
dCommGroup α] [AddLeftMono α] (a b c : α), |a ⊓ c - b ⊓ c| ≤ |a - b|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ ≤ ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)
/-
**lipschitzWith_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z
参数：z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `norm_sup_sub_sup_le_norm`：norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z 
- y ⊔ z‖ <= ‖x - y‖
-/
theorem lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z
/-
**lipschitzWith_posPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzWith_posPart : LipschitzWith 1 (posPart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_sup_right`：lipschitzWith_sup_right (z : α) : LipschitzWith
 1 fun x => x ⊔ z
-/
lemma lipschitzWith_posPart : LipschitzWith 1 (posPart : α → α) :=
  lipschitzWith_sup_right 0
/-
**lipschitzWith_negPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzWith_negPart : LipschitzWith 1 (negPart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用引理 `lipschitzWith_posPart`：lipschitzWith_posPart : LipschitzWith 1 (posPart 
: α -> α)
· 使用定理 `LipschitzWith.neg`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] [inst_1 : PseudoEMetricSpace α] {K : NNReal}   {f : α → E}, Lipschi
tzWith …
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
lemma lipschitzWith_negPart : LipschitzWith 1 (negPart : α → α) := by
  simpa [Function.comp] using! lipschitzWith_posPart.comp LipschitzWith.id.neg

@[fun_prop]
/-
**continuous_posPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_posPart : Continuous (posPart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用引理 `lipschitzWith_posPart`：lipschitzWith_posPart : LipschitzWith 1 (posPart 
: α -> α)
-/
lemma continuous_posPart : Continuous (posPart : α → α) := lipschitzWith_posPart.continuous

@[fun_prop]
/-
**continuous_negPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_negPart : Continuous (negPart : α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用引理 `lipschitzWith_negPart`：lipschitzWith_negPart : LipschitzWith 1 (negPart 
: α -> α)
-/
lemma continuous_negPart : Continuous (negPart : α → α) := lipschitzWith_negPart.continuous
/-
**isClosed_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_nonneg : IsClosed {x : α | 0 <= x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma isClosed_nonneg : IsClosed {x : α | 0 ≤ x} := by
  have : {x : α | 0 ≤ x} = negPart ⁻¹' {0} := by ext; simp [negPart_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage continuous_negPart
/-
**isClosed_le_of_isClosed_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_le_of_isClosed_nonneg {G} [AddCommGroup G] [PartialOrder G] [IsOr
deredAddMonoid G] [TopologicalSpace G] [ContinuousSub G] (h : IsClosed { x : G |
 0 <= x }) : IsClosed { p : G × G | p.fst <= p.snd }
参数：h : IsClosed { x : G | 0 <= x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem isClosed_le_of_isClosed_nonneg {G}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [TopologicalSpace G]
    [ContinuousSub G] (h : IsClosed { x : G | 0 ≤ x }) :
    IsClosed { p : G × G | p.fst ≤ p.snd } := by
  have : { p : G × G | p.fst ≤ p.snd } = (fun p : G × G ↦ p.snd - p.fst) ⁻¹' { x : G | 0 ≤ x } := by
    ext1 p; simp only [sub_nonneg, Set.preimage_ofPred_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HasSolidNorm.orderClosedTopology {E}
    [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] :
    OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg isClosed_nonneg⟩
