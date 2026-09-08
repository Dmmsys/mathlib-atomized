/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Fixed points of isometries of the upper half-plane

In this file we show that the scalar multiplication by an element `g : GL (Fin 2) ℝ`
has the following set of fixed points, depending on `g`.

- if `g` preserves orientation (i.e., has positive determinant) and is an elliptic matrix,
  then `z ↦ g • z` has a unique fixed point;
- if `g` is a scalar matrix, then it acts by the identity map (proved upstream of this file);
- if `g` preserves orientation, and is a parabolic or a hyperbolic matrix,
  then it has no fixed points;
- if `g` reverses orientation and has zero trace, then it has a geodesic line of fixed points;
  - if `g 1 0 = 0`, then this is the vertical line `re z = g 0 1 / (2 * g 1 1)`;
  - otherwise, it's a half-circle with its center on the real axis;
- if `g` reverses orientation and has nonzero trace, then it has no fixed points.

As a corollary of this classification, we conclude that `PSL(2, ℝ)` acts faithfully
on the upper half-plane.
-/

open Matrix
open scoped MatrixGroups ComplexConjugate

public noncomputable section

namespace UpperHalfPlane

section GLAction

variable {g : GL (Fin 2) ℝ} {z w : ℍ}

/-
**UpperHalfPlane.gl_smul_eq_iff_num_eq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：gl_smul_eq_iff_num_eq : g • z = w ↔ num g z = σ g w * denom g z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `UpperHalfPlane.σ_sq`：σ_sq (g : GL (Fin 2) Real) (z : Complex) : σ g (σ g
 z) = z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gl_smul_eq_iff_num_eq :
    g • z = w ↔ num g z = σ g w * denom g z := by
  rw [← (σ g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

/-- If `g` is an upper triangular matrix with trace zero,
then `g` fixes the vertical line `re z = b / (2 * d)`. -/
/-
**UpperHalfPlane.gl_smul_eq_self_iff_re_eq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：gl_smul_eq_self_iff_re_eq (htrace : g.val.trace = 0) (hc : g 1 0 = 0) : g 
• z = z ↔ z.re = g 0 1 / (2 * g 1 1)
参数：htrace : g.val.trace = 0；hc : g 1 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `g` is an upper triangular matrix with trace zero,
then `g` fixes the vertical line `re z = b / (2 * d)`.
-/
theorem gl_smul_eq_self_iff_re_eq (htrace : g.val.trace = 0) (hc : g 1 0 = 0) :
    g • z = z ↔ z.re = g 0 1 / (2 * g 1 1) := by
  rw [Matrix.trace_fin_two, add_eq_zero_iff_eq_neg] at htrace
  have h₀ : g 1 1 ≠ 0 := by
    intro h₀
    simpa [Matrix.det_fin_two, hc, h₀] using g.det_ne_zero
  have h : g.val.det < 0 := by simp [Matrix.det_fin_two, *]
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, htrace, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff, h₀]
  grind

/-- If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line.
If `c = 0`, then this line is a vertical half-line in the usual geometry,
see `gl_smul_eq_self_iff_re_eq`. -/
/-
**UpperHalfPlane.gl_smul_eq_self_iff_dist_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：gl_smul_eq_self_iff_dist_sq_eq (h : g.val.det < 0) (htrace : g.val.trace =
 0) (hc : g 1 0 != 0) : g • z = z ↔ dist (z : Complex) (-g 1 1 / g 1 0) ^ 2 = (-
g.val.det) / g 1 0 ^ 2
参数：h : g.val.det < 0；htrace : g.val.trace = 0；hc : g 1 0 != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `Complex.normSq_apply`：normSq_apply (z : Complex) : normSq z = z.re * z.r
e + z.im * z.im
· 使用定理 `UpperHalfPlane.gl_smul_eq_iff_num_eq`：gl_smul_eq_iff_num_eq : g • z = w 
↔ num g z = σ g w * denom g z
· 使用定理 `UpperHalfPlane.σ.eq_1`：∀ (g : GL (Fin 2) ℝ),   UpperHalfPlane.σ g = if 0
 < ↑(Matrix.GeneralLinearGroup.det g) then ContinuousAlgEquiv.refl ℝ ℂ else Comp
lex.conjCAE
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line.
If `c = 0`, then this line is a vertical half-line in the usual geometry,
see `gl_smul_eq_self_iff_re_eq`.
-/
theorem gl_smul_eq_self_iff_dist_sq_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) ^ 2 = (-g.val.det) / g 1 0 ^ 2 := by
  rw [Matrix.trace_fin_two, ← eq_neg_iff_add_eq_zero] at htrace
  rw [eq_div_iff (by positivity), dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    gl_smul_eq_iff_num_eq, σ, g.val_det_apply, if_neg h.not_gt]
  simp [num, denom, Complex.ext_iff, htrace, Matrix.det_fin_two, field]
  grind

/-- If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line. -/
/-
**UpperHalfPlane.gl_smul_eq_self_iff_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHal
fPlane`。
形式化陈述：gl_smul_eq_self_iff_dist_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
 (hc : g 1 0 != 0) : g • z = z ↔ dist (z : Complex) (-g 1 1 / g 1 0) = √(-g.val.
det) / |g 1 0|
参数：h : g.val.det < 0；htrace : g.val.trace = 0；hc : g 1 0 != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.gl_smul_eq_self_iff_dist_sq_eq`：gl_smul_eq_self_iff_dist_
sq_eq (h : g.val.det < 0) (htrace : g.val.trace = 0) (hc : g 1 0 != 0) : g • z =
 z ↔ dist (z : Complex) (-g 1 1 / g…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_eq_iff_eq_sq`：sqrt_eq_iff_eq_sq (hx : 0 <= x) (hy : 0 <= y) : 
√x = y ↔ x = y ^ 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Real.sqrt_div'`：sqrt_div' (x) {y : Real} (hy : 0 <= y) : √(x / y) = √x /
 √y
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line.
-/
theorem gl_smul_eq_self_iff_dist_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) = √(-g.val.det) / |g 1 0| := by
  rw [gl_smul_eq_self_iff_dist_sq_eq h htrace hc, eq_comm, ← Real.sqrt_eq_iff_eq_sq, eq_comm,
    Real.sqrt_div', Real.sqrt_sq_eq_abs] <;> positivity [neg_pos.mpr h]

/-- An orientation-reversing isometry of the hyperbolic plane has a fixed point
iff the corresponding matrix has zero trace. -/
/-
**UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `UpperHalfPlane`。
形式化陈述：exists_gl_smul_eq_self_iff_trace_eq_zero (h : g.val.det < 0) : (exists z :
 ℍ, g • z = z) ↔ g.val.trace = 0
参数：h : g.val.det < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.gl_smul_eq_iff_num_eq`：gl_smul_eq_iff_num_eq : g • z = w 
↔ num g z = σ g w * denom g z
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
An orientation-reversing isometry of the hyperbolic plane has a fixed point
iff the corresponding matrix has zero trace.
-/
theorem exists_gl_smul_eq_self_iff_trace_eq_zero (h : g.val.det < 0) :
    (∃ z : ℍ, g • z = z) ↔ g.val.trace = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    linear_combination
      (norm := { simp [σ, h.not_gt, num, denom, z.im_ne_zero, Matrix.trace_fin_two, field] })
      congr($(gl_smul_eq_iff_num_eq.mp hz).im / z.im)
  · intro hadd
    by_cases hc : g 1 0 = 0
    · use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · use ⟨⟨-g 1 1 / g 1 0, √(-g.val.det) / |g 1 0|⟩, by simp [*]⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, div_pow, h.le]

/-- If `g` is an orientation-preserving map,
then the fixed points of its action on the upper half-plane
can be found from a quadratic equation.

If `c ≠ 0`, then this equation has a unique solution in the upper half-plane
given by `UpperHalfPlane.fixedPt`.
If `c = 0`, then the equation degenerates to a linear equation,
which has no solutions in the upper half-plane unless `g` is a scalar matrix.

See also `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`
for a similar lemma about the action on the projective line,
encoded as `OnePoint R`, where `R` is the ring of coefficients.
-/
/-
**UpperHalfPlane.gl_smul_eq_self_iff_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `UpperH
alfPlane`。
形式化陈述：gl_smul_eq_self_iff_quadratic (h : 0 < g.val.det) : g • z = z ↔ (g 1 0 * (
z * z) + (g 1 1 - g 0 0) * z + -g 0 1 : Complex) = 0
参数：h : 0 < g.val.det。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `g` is an orientation-preserving map,
then the fixed points of its action on the upper half-plane
can be found from a quadratic equation.

If `c ≠ 0`, then this equation has a unique solution in the upper half-plane
given by `UpperHalfPlane.fixedPt`.
If `c = 0`, then the equation degenerates to a linear equation,
which has no solutions in the upper half-plane unless `g` is a scalar matrix.

See also `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`
for a similar lemma about the action on the projective line,
encoded as `OnePoint R`, where `R` is the ring of coefficients.
-/
theorem gl_smul_eq_self_iff_quadratic (h : 0 < g.val.det) :
    g • z = z ↔ (g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + -g 0 1 : ℂ) = 0 := by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

/-- If `g` is a non-scalar orientation preserving matrix with a fixed point in `ℍ`,
then it's an elliptic matrix. -/
/-
**UpperHalfPlane.isElliptic_of_exists_smul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Up
perHalfPlane`。
形式化陈述：isElliptic_of_exists_smul_eq_self (h : 0 < g.val.det) (hgc : g ∉ Subgroup.
center _) (hfix : exists z : ℍ, g • z = z) : g.IsElliptic
参数：h : 0 < g.val.det；hgc : g ∉ Subgroup.center _；hfix : exists z : ℍ, g • z = z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
If `g` is a non-scalar orientation preserving matrix with a fixed point in `ℍ`,
then it's an elliptic matrix.
-/
theorem isElliptic_of_exists_smul_eq_self (h : 0 < g.val.det) (hgc : g ∉ Subgroup.center _)
    (hfix : ∃ z : ℍ, g • z = z) : g.IsElliptic := by
  rcases hfix with ⟨z, hz⟩
  have hc : g 1 0 ≠ 0 := by
    intro hc
    simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
    simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero]
      at hz
    grind
  refine lt_of_not_ge fun hge ↦ ?_
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h, quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  norm_cast at hz
  simp only [z.ne_ofReal, false_or] at hz

/-- The unique fixed point of an orientation-preserving elliptic matrix acting on `ℍ`. -/
/-
**UpperHalfPlane.fixedPt** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：fixedPt (g : GL (Fin 2) Real) (hell : g.IsElliptic) : ℍ
参数：g : GL (Fin 2) Real；hell : g.IsElliptic。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique fixed point of an orientation-preserving elliptic matrix acting on `ℍ
`.
-/
def fixedPt (g : GL (Fin 2) ℝ) (hell : g.IsElliptic) : ℍ :=
  ⟨(g 0 0 - g 1 1) / (2 * g 1 0) + .I * (√(-g.val.discr) / (2 * |g 1 0|)), by
    simpa [div_pos, Complex.div_re, Complex.div_im, hell.c_ne_zero]⟩

@[simp]
/-
**UpperHalfPlane.fixedPt_neg** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：fixedPt_neg (hg : (-g).IsElliptic) : fixedPt (-g) hg = fixedPt g (isEllipt
ic_neg_iff.mp hg)
参数：hg : (-g).IsElliptic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isElliptic_neg_iff`：isElliptic_neg_iff : (-m).IsElliptic ↔ m.IsEl
liptic
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.trace_neg`：trace_neg (A : Matrix n n R) : trace (-A) = -trace A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 72 条，此处仅展示前 30 条）
-/
theorem fixedPt_neg (hg : (-g).IsElliptic) :
    fixedPt (-g) hg = fixedPt g (isElliptic_neg_iff.mp hg) := by
  ext
  simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]
  ring

/-- The action of an elliptic orientation preserving matrix on `ℍ`
has a unique fixed point given by `fixedPt`. -/
/-
**UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：gl_smul_eq_self_iff_eq_fixedPt (hpos : 0 < g.val.det) (hell : g.IsElliptic
) : g • z = z ↔ z = fixedPt g hell
参数：hpos : 0 < g.val.det；hell : g.IsElliptic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `UpperHalfPlane.gl_smul_eq_self_iff_quadratic`：gl_smul_eq_self_iff_quadra
tic (h : 0 < g.val.det) : g • z = z ↔ (g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + -
g 0 1 : Complex) = 0
· 使用定理 `quadratic_eq_zero_iff`：quadratic_eq_zero_iff (ha : a != 0) {s : K} (h : 
discrim a b c = s * s) (x : K) : a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2
 * a) ∨ x =…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Matrix.IsElliptic.c_ne_zero`：∀ {R : Type u_1} [inst : CommRing R] [inst_
1 : LinearOrder R] [IsOrderedRing R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsEllip
tic → m 1 0 ≠ 0
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
The action of an elliptic orientation preserving matrix on `ℍ`
has a unique fixed point given by `fixedPt`.
-/
theorem gl_smul_eq_self_iff_eq_fixedPt (hpos : 0 < g.val.det) (hell : g.IsElliptic) :
    g • z = z ↔ z = fixedPt g hell := by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos, quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · simp [fixedPt, UpperHalfPlane.ext_iff, abs_of_pos hc, field]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im, h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]
/-
**UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：gl_smul_I_eq_I_iff_of_pos {g : GL (Fin 2) Real} (hg : 0 < g.det.val) : g •
 I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0
参数：Fin 2；hg : 0 < g.det.val。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.gl_smul_eq_iff_num_eq`：gl_smul_eq_iff_num_eq : g • z = w 
↔ num g z = σ g w * denom g z
· 使用定理 `UpperHalfPlane.σ.eq_1`：∀ (g : GL (Fin 2) ℝ),   UpperHalfPlane.σ g = if 0
 < ↑(Matrix.GeneralLinearGroup.det g) then ContinuousAlgEquiv.refl ℝ ℂ else Comp
lex.conjCAE
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gl_smul_I_eq_I_iff_of_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    g • I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, if_pos hg]
  simp [Complex.ext_iff, num, denom, and_comm]
/-
**UpperHalfPlane.gl_smul_I_eq_I_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：gl_smul_I_eq_I_iff_of_neg {g : GL (Fin 2) Real} (hg : g.det.val < 0) : g •
 I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 1 0
参数：Fin 2；hg : g.det.val < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.gl_smul_eq_iff_num_eq`：gl_smul_eq_iff_num_eq : g • z = w 
↔ num g z = σ g w * denom g z
· 使用定理 `UpperHalfPlane.σ.eq_1`：∀ (g : GL (Fin 2) ℝ),   UpperHalfPlane.σ g = if 0
 < ↑(Matrix.GeneralLinearGroup.det g) then ContinuousAlgEquiv.refl ℝ ℂ else Comp
lex.conjCAE
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gl_smul_I_eq_I_iff_of_neg {g : GL (Fin 2) ℝ} (hg : g.det.val < 0) :
    g • I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, if_neg (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

/-- A matrix acts trivially on `ℍ` iff it belongs to the center of `GL(2, ℝ)`,
i.e., it's a diagonal matrix. -/
/-
**UpperHalfPlane.forall_smul_eq_self_iff_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `U
pperHalfPlane`。
形式化陈述：forall_smul_eq_self_iff_mem_center {g : GL (Fin 2) Real} : (forall z : ℍ, 
g • z = z) ↔ g in Subgroup.center _
参数：Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.gl_smul_I_eq_I_iff_of_neg`：gl_smul_I_eq_I_iff_of_neg {g :
 GL (Fin 2) Real} (hg : g.det.val < 0) : g • I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 
1 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `UpperHalfPlane.gl_smul_eq_self_iff_re_eq`：gl_smul_eq_self_iff_re_eq (htr
ace : g.val.trace = 0) (hc : g 1 0 = 0) : g • z = z ↔ z.re = g 0 1 / (2 * g 1 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
A matrix acts trivially on `ℍ` iff it belongs to the center of `GL(2, ℝ)`,
i.e., it's a diagonal matrix.
-/
theorem forall_smul_eq_self_iff_mem_center {g : GL (Fin 2) ℝ} :
    (∀ z : ℍ, g • z = z) ↔ g ∈ Subgroup.center _ := by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rw [eq_neg_iff_add_eq_zero, ← Matrix.trace_fin_two] at ha
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq ha hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨-g 1 1 / g 1 0, 1 + √(-g.val.det) / |g 1 0|⟩, this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt ha hc, Complex.dist_eq_re_im, Real.sqrt_sq this.le]
          at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

end GLAction

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul PGL(2, ℝ) ℍ := by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

end UpperHalfPlane

