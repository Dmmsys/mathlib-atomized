/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Nonnegativity of values of holomorphic functions

We show that if `f` is holomorphic on an open disk `B(c,r)` and all iterated derivatives of `f`
at `c` are nonnegative real, then `f z ≥ 0` for all `z ≥ c` in the disk; see
`DifferentiableOn.nonneg_of_iteratedDeriv_nonneg`. We also provide a
variant `Differentiable.nonneg_of_iteratedDeriv_nonneg` for entire functions and versions
showing `f z ≥ f c` when all iterated derivatives except `f` itself are nonnegative.
-/

public section

open Complex

open scoped ComplexOrder

namespace DifferentiableOn

/-- A function that is holomorphic on the open disk around `c` with radius `r` and whose iterated
derivatives at `c` are all nonnegative real has nonnegative real values on `c + [0,r)`. -/
/-
**DifferentiableOn.nonneg_of_iteratedDeriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Dif
ferentiableOn`。
形式化陈述：nonneg_of_iteratedDeriv_nonneg {f : Complex -> Complex} {c : Complex} {r :
 Real} (hf : DifferentiableOn Complex f (Metric.ball c r)) (h : forall n, 0 <= i
teratedDeriv n f c) ⦃z : Complex⦄ (hz₁ : c <= z) (hz₂ : z in Metric.ball c r) : 
0 <= f z
参数：hf : DifferentiableOn Complex f (Metric.ball c r)；h : forall n, 0 <= iterated
Deriv n f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.taylorSeries_eq_on_ball'`：taylorSeries_eq_on_ball' {f : Complex 
-> Complex} (hf : DifferentiableOn Complex f (Metric.ball c r)) : ∑' n : Nat, (n
 ! : Complex)⁻¹ * iter…
· 使用定理 `Complex.eq_re_of_ofReal_le`：eq_re_of_ofReal_le {r : Real} {z : Complex} 
(hz : (r : Complex) <= z) : z = z.re
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `Complex.orderClosedTopology`：OrderClosedTopology ℂ
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.le_def`：le_def {z w : Complex} : z <= w ↔ z.re <= w.re ∧ z.im = 
w.im
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `RCLike.toPosMulReflectLT`：toPosMulReflectLT : PosMulReflectLT K where el
im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
A function that is holomorphic on the open disk around `c` with radius `r` and w
hose iterated
derivatives at `c` are all nonnegative real has nonnegative real values on `c + 
[0,r)`.
-/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄
    (hz₁ : c ≤ z) (hz₂ : z ∈ Metric.ball c r) :
    0 ≤ f z := by
  have H := taylorSeries_eq_on_ball' hz₂ hf
  rw [← sub_nonneg] at hz₁
  have hz' := eq_re_of_ofReal_le hz₁
  rw [hz'] at hz₁ H
  refine H ▸ tsum_nonneg fun n ↦ ?_
  rw [← ofReal_natCast, ← ofReal_pow, ← ofReal_inv, eq_re_of_ofReal_le (h n), ← ofReal_mul,
    ← ofReal_mul]
  norm_cast at hz₁ ⊢
  positivity [zero_re ▸ (Complex.le_def.mp (h n)).1]

end DifferentiableOn

namespace Differentiable

/-- An entire function whose iterated derivatives at `c` are all nonnegative real has nonnegative
real values on `c + ℝ≥0`. -/
/-
**Differentiable.nonneg_of_iteratedDeriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Diffe
rentiable`。
形式化陈述：nonneg_of_iteratedDeriv_nonneg {f : Complex -> Complex} (hf : Differentiab
le Complex f) {c : Complex} (h : forall n, 0 <= iteratedDeriv n f c) ⦃z : Comple
x⦄ (hz : c <= z) : 0 <= f z
参数：hf : Differentiable Complex f；h : forall n, 0 <= iteratedDeriv n f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.nonneg_of_iteratedDeriv_nonneg`：nonneg_of_iteratedDeriv
_nonneg {f : Complex -> Complex} {c : Complex} {r : Real} (hf : DifferentiableOn
 Complex f (Metric.ball c r)) (h : fo…
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
· 使用定理 `Complex.eq_re_of_ofReal_le`：eq_re_of_ofReal_le {r : Real} {z : Complex} 
(hz : (r : Complex) <= z) : z = z.re
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.nonneg_iff`：nonneg_iff {z : Complex} : 0 <= z ↔ 0 <= z.re ∧ 0 = 
z.im
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
An entire function whose iterated derivatives at `c` are all nonnegative real ha
s nonnegative
real values on `c + ℝ≥0`.
-/
theorem nonneg_of_iteratedDeriv_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (h : ∀ n, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : c ≤ z) :
    0 ≤ f z := by
  refine hf.differentiableOn.nonneg_of_iteratedDeriv_nonneg (r := (z - c).re + 1) h hz ?_
  rw [← sub_nonneg] at hz
  rw [Metric.mem_ball, dist_eq, eq_re_of_ofReal_le hz]
  simpa only [Complex.norm_of_nonneg (nonneg_iff.mp hz).1] using! lt_add_one _

/-- An entire function whose iterated derivatives at `c` are all nonnegative real (except
possibly the value itself) has values of the form `f c + nonneg. real` on the set `c + ℝ≥0`. -/
/-
**Differentiable.apply_le_of_iteratedDeriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Dif
ferentiable`。
形式化陈述：apply_le_of_iteratedDeriv_nonneg {f : Complex -> Complex} {c : Complex} (h
f : Differentiable Complex f) (h : forall n != 0, 0 <= iteratedDeriv n f c) ⦃z :
 Complex⦄ (hz : c <= z) : f c <= f z
参数：hf : Differentiable Complex f；h : forall n != 0, 0 <= iteratedDeriv n f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedDeriv_succ'`：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = ite
ratedDeriv n (deriv f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_sub_const`：deriv_sub_const (c : F) : deriv (fun y => f y - c) x = 
deriv f x
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `Differentiable.nonneg_of_iteratedDeriv_nonneg`：nonneg_of_iteratedDeriv_n
onneg {f : Complex -> Complex} (hf : Differentiable Complex f) {c : Complex} (h 
: forall n, 0 <= iteratedDeriv n f …
· 使用定理 `Differentiable.sub_const`：Differentiable.sub_const (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => f y - c

--- 原说明 ---
An entire function whose iterated derivatives at `c` are all nonnegative real (e
xcept
possibly the value itself) has values of the form `f c + nonneg. real` on the se
t `c + ℝ≥0`.
-/
theorem apply_le_of_iteratedDeriv_nonneg {f : ℂ → ℂ} {c : ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : c ≤ z) :
    f c ≤ f z := by
  have h' (n : ℕ) : 0 ≤ iteratedDeriv n (f · - f c) c := by
    cases n with
    | zero => simp only [iteratedDeriv_zero, sub_self, le_refl]
    | succ n =>
      specialize h (n + 1) n.succ_ne_zero
      rw [iteratedDeriv_succ'] at h ⊢
      rwa [funext fun x ↦ deriv_sub_const (f := f) (x := x) (f c)]
  exact sub_nonneg.mp <| nonneg_of_iteratedDeriv_nonneg (hf.sub_const _) h' hz

/-- An entire function whose iterated derivatives at `c` are all real with alternating signs
(except possibly the value itself) has values of the form `f c + nonneg. real` along the
set `c - ℝ≥0`. -/
/-
**Differentiable.apply_le_of_iteratedDeriv_alternating** 是 Mathlib 中的一个定理，位于命名空间
 `Differentiable`。
形式化陈述：apply_le_of_iteratedDeriv_alternating {f : Complex -> Complex} {c : Comple
x} (hf : Differentiable Complex f) (h : forall n != 0, 0 <= (-1) ^ n * iteratedD
eriv n f c) ⦃z : Complex⦄ (hz : z <= c) : f c <= f z
参数：hf : Differentiable Complex f；h : forall n != 0, 0 <= (-1) ^ n * iteratedDeri
v n f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Differentiable.apply_le_of_iteratedDeriv_nonneg`：apply_le_of_iteratedDer
iv_nonneg {f : Complex -> Complex} {c : Complex} (hf : Differentiable Complex f)
 (h : forall n != 0, 0 <= iteratedDer…
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `differentiable_neg`：differentiable_neg : Differentiable 𝕜 (Neg.neg : 𝕜 -
> 𝕜)
· 使用引理 `iteratedDeriv_comp_neg`：iteratedDeriv_comp_neg (n : Nat) (f : 𝕜 -> F) (a
 : 𝕜) : iteratedDeriv n (fun x => f (-x)) a = (-1 : 𝕜) ^ n • iteratedDeriv n f (
-a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
An entire function whose iterated derivatives at `c` are all real with alternati
ng signs
(except possibly the value itself) has values of the form `f c + nonneg. real` a
long the
set `c - ℝ≥0`.
-/
theorem apply_le_of_iteratedDeriv_alternating {f : ℂ → ℂ} {c : ℂ} (hf : Differentiable ℂ f)
    (h : ∀ n ≠ 0, 0 ≤ (-1) ^ n * iteratedDeriv n f c) ⦃z : ℂ⦄ (hz : z ≤ c) :
    f c ≤ f z := by
  convert!
    apply_le_of_iteratedDeriv_nonneg (f := fun z ↦ f (-z)) (hf.comp <| differentiable_neg)
      (fun n hn ↦ ?_) (neg_le_neg_iff.mpr hz) using 1
  · simp only [neg_neg]
  · simp only [neg_neg]
  · simpa only [iteratedDeriv_comp_neg, neg_neg, smul_eq_mul] using h n hn

end Differentiable

