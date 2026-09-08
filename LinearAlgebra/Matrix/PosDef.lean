/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
In `Mathlib/Analysis/Matrix/Order.lean`, positive semi-definiteness is used to define the partial
order on matrices on `ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosSemidef` : a matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian
  and `xᴴMx` is nonnegative for all `x`.
* `Matrix.PosDef` : a matrix `M : Matrix n n R` is positive definite if it is Hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.

## Main results

* `Matrix.PosSemidef.fromBlocks₁₁` and `Matrix.PosSemidef.fromBlocks₂₂`: If a matrix `A` is
  positive definite, then `[A B; Bᴴ D]` is positive semidefinite if and only if `D - Bᴴ A⁻¹ B` is
  positive semidefinite.
* `Matrix.PosDef.isUnit`: A positive definite matrix in a field is invertible.
-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidAlgebra
assert_not_exists NormedGroup

open Matrix

namespace Matrix

variable {m n R R' : Type*}
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-!
## Positive semidefinite matrices
-/

/-- A matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian and `xᴴ * M * x` is
nonnegative for all `x` of finite support. -/
/-
**Matrix.PosSemidef** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：PosSemidef (M : Matrix n n R) : Prop
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian and `xᴴ 
* M * x` is
nonnegative for all `x` of finite support.
-/
def PosSemidef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ ∀ x : n →₀ R, 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj
/-
**Matrix.PosSemidef.diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] {d : n → R}
, 0 ≤ d → (Matrix.diagonal d).PosSemidef
参数：Matrix.diagonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_diagonal_of_self_adjoint`：isHermitian_diagonal_of_sel
f_adjoint [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v) : (diagonal v).IsHe
rmitian
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `star_left_conjugate_nonneg`：star_left_conjugate_nonneg {a : R} (ha : 0 <
= a) (c : R) : 0 <= star c * a * c
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
protected theorem PosSemidef.diagonal [StarOrderedRing R] [DecidableEq n] {d : n → R} (h : 0 ≤ d) :
    PosSemidef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]

/-- A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegative. -/
/-
**Matrix.posSemidef_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] {d : n → R}
, (Matrix.diagonal d).PosSemidef ↔ ∀ (i : n), 0 ≤ d i
参数：Matrix.diagonal d；i : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.PosSemidef.diagonal`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring
 R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_
4 : DecidableEq …

--- 原说明 ---
A diagonal matrix is positive semidefinite iff its diagonal entries are nonnegat
ive.
-/
@[simp] lemma posSemidef_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n → R} :
    PosSemidef (diagonal d) ↔ ∀ i, 0 ≤ d i :=
  ⟨fun ⟨_, hP⟩ i ↦ by simpa using hP (.single i 1), .diagonal⟩

namespace PosSemidef

/-
**Matrix.PosSemidef.isHermitian** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian
参数：hM : M.PosSemidef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1
/-
**Matrix.PosSemidef.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m -> n) : (M.submatr
ix e e).PosSemidef
参数：hM : M.PosSemidef；e : m -> n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : Type 
u_4} [inst : Star α] {A : Matrix n n α},   A.IsHermitian → ∀ (f : m → n), (A.sub
matrix f f).IsHerm…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) :
    (M.submatrix e e).PosSemidef := by
  refine ⟨hM.1.submatrix _, fun x ↦ ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 <| x.mapDomain e
/-
**Matrix.PosSemidef.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef
参数：hM : M.PosSemidef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Matrix.IsHermitian.transpose`：∀ {α : Type u_1} {n : Type u_4} [inst : St
ar α] {A : Matrix n n α}, A.IsHermitian → A.transpose.IsHermitian
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finsupp.sum_comm`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {M' : T
ype u_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommM
onoid …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
（共 31 条，此处仅展示前 30 条）
-/
theorem transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

@[simp]
/-
**Matrix.PosSemidef._root_.Matrix.posSemidef_transpose_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Matrix.PosSemidef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posSemidef_transpose_iff {M : Matrix n n R'} : Mᵀ.PosSemidef ↔ M.PosSemidef :=
  ⟨.transpose, .transpose⟩
/-
**Matrix.PosSemidef.conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef
参数：hM : M.PosSemidef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef := hM.1.symm ▸ hM

@[simp]
/-
**Matrix.PosSemidef._root_.Matrix.posSemidef_conjTranspose_iff** 是 Mathlib 中的一个定
理，位于命名空间 `Matrix.PosSemidef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posSemidef_conjTranspose_iff {M : Matrix n n R} :
    Mᴴ.PosSemidef ↔ M.PosSemidef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩
/-
**Matrix.PosSemidef.add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {m : Type u_1} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [AddLeftMono R]   {A B : Matrix m m R}, A.PosSemidef → B.P
osSemidef → (A + B).PosSemidef
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.add`：∀ {α : Type u_1} {n : Type u_4} [inst : AddMonoi
d α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α},   A.IsHermitian → B.IsHerm
itian → (A +…
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩
/-
**Matrix.PosSemidef.smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] {α : Type u_5}   [inst_3 : CommSemiring α] [inst_4 : Parti
alOrder α] [inst_5 : StarRing α] [StarOrderedRing α] [inst_7 : Algebra α R]   [S
tarModule α R] [PosSMulMono α R] {x : Matrix n n R}, x.PosSemidef → ∀ {a : α}, 0
 ≤ a → (a • x).PosSemidef
参数：a • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {x : Matrix n n R}
    (hx : x.PosSemidef) {a : α} (ha : 0 ≤ a) : (a • x).PosSemidef := by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)
/-
**Matrix.PosSemidef.zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R], Matrix.PosSemidef 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_zero`：isHermitian_zero : (0 : Matrix n n α).IsHermiti
an
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma zero : PosSemidef (0 : Matrix n n R) := ⟨isHermitian_zero, by simp⟩
/-
**Matrix.PosSemidef.one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n], Matrix.Pos
Semidef 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_one`：isHermitian_one [DecidableEq n] : (1 : Matrix n 
n α).IsHermitian
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected lemma one [StarOrderedRing R] [DecidableEq n] : PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩
/-
**Matrix.PosSemidef.natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] (d : ℕ), (↑
d).PosSemidef
参数：d : ℕ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_natCast`：isHermitian_natCast [DecidableEq n] (d : Nat
) : (d : Matrix n n α).IsHermitian
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem natCast [StarOrderedRing R] [DecidableEq n] (d : ℕ) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_natCast _, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]⟩
/-
**Matrix.PosSemidef.ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] (d : ℕ) [in
st_5 : d.AtLeastTwo], (OfNat.ofNat d).PosSemidef
参数：d : ℕ；OfNat.ofNat d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosSemidef.natCast`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring 
R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4
 : DecidableEq …
-/
protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : ℕ) [d.AtLeastTwo] :
    PosSemidef (ofNat(d) : Matrix n n R) :=
  .natCast d
/-
**Matrix.PosSemidef.intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] (d : ℤ), 0 
≤ d → (↑d).PosSemidef
参数：d : ℤ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_intCast`：isHermitian_intCast [DecidableEq n] (d : Int
) : (d : Matrix n n α).IsHermitian
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : ℤ) (hd : 0 ≤ d) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x => Finsupp.sum_nonneg fun i _ ↦ Finsupp.sum_nonneg fun j _ ↦ by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]⟩

@[simp]
/-
**Matrix.PosSemidef._root_.Matrix.posSemidef_intCast_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Matrix.PosSemidef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Matrix.posSemidef_intCast_iff
    [StarOrderedRing R] [DecidableEq n] [Nonempty n] [Nontrivial R] (d : ℤ) :
    PosSemidef (d : Matrix n n R) ↔ 0 ≤ d := by simp [← diagonal_intCast']
/-
**Matrix.PosSemidef.diag_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 <= A i i
参数：hA : A.PosSemidef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 ≤ A i i := by
  simpa using hA.2 <| .single i 1

end PosSemidef

@[simp]
/-
**Matrix.posSemidef_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) : (M.submatrix e
 e).PosSemidef ↔ M.PosSemidef
参数：e : m ≃ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.PosSemidef.submatrix`：submatrix {M : Matrix n n R} (hM : M.PosSem
idef) (e : m -> n) : (M.submatrix e e).PosSemidef
-/
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
/-
**Matrix.posSemidef_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_sum {ι : Type*} [AddLeftMono R] {x : ι -> Matrix n n R} (s : Fi
nset ι) (h : forall i in s, PosSemidef (x i)) : PosSemidef (∑ i in s, x i)
参数：s : Finset ι；h : forall i in s, PosSemidef (x i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isSelfAdjoint_sum`：isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [Star
AddMonoid R] (s : Finset ι) {x : ι -> R} (h : forall i in s, IsSelfAdjoint (x i)
) : IsS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finsupp.sum_finsetSum_comm`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_
8} {N : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {s : Finset β}   (
f : α →₀ M) (h :…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem posSemidef_sum {ι : Type*} [AddLeftMono R]
    {x : ι → Matrix n n R} (s : Finset ι) (h : ∀ i ∈ s, PosSemidef (x i)) :
    PosSemidef (∑ i ∈ s, x i) := by
  refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi |>.1, fun y => ?_⟩
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

/-!
## Positive definite matrices
-/

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
/-
**Matrix.PosDef** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：PosDef (M : Matrix n n R)
参数：M : Matrix n n R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`.
-/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ ∀ ⦃x : n →₀ R⦄, x ≠ 0 → 0 < x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj

namespace PosDef

/-
**Matrix.PosDef.isHermitian** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1
/-
**Matrix.PosDef.posSemidef** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef :=
  ⟨hM.1, fun x ↦ by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩
/-
**Matrix.PosDef.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：submatrix {M : Matrix n n R} (hM : M.PosDef) {e : m -> n} (he : Function.I
njective e) : (M.submatrix e e).PosDef
参数：hM : M.PosDef；he : Function.Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : Type 
u_4} [inst : Star α] {A : Matrix n n α},   A.IsHermitian → ∀ (f : m → n), (A.sub
matrix f f).IsHerm…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {x y : α} {z : β}, f y = z → (f x ≠ z ↔ x ≠ y)
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
-/
theorem submatrix {M : Matrix n n R} (hM : M.PosDef) {e : m → n}
    (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  refine ⟨hM.1.submatrix _, fun x hx ↦ ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
    hM.2 <| Finsupp.mapDomain_injective he |>.ne_iff' Finsupp.mapDomain_zero |>.2 hx
/-
**Matrix.PosDef.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `Matrix.IsHermitian.transpose`：∀ {α : Type u_1} {n : Type u_4} [inst : St
ar α] {A : Matrix n n α}, A.IsHermitian → A.transpose.IsHermitian
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finsupp.sum_comm`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {M' : T
ype u_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommM
onoid …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
（共 32 条，此处仅展示前 30 条）
-/
theorem transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

@[simp]
/-
**Matrix.PosDef.transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.PosDef.transpose`：transpose {M : Matrix n n R'} (hM : M.PosDef) :
 Mᵀ.PosDef
-/
theorem transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.transpose), .transpose⟩
/-
**Matrix.PosDef.diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] [NoZeroDivi
sors R] {d : n → R}, (∀ (i : n), 0 < d i) → (Matrix.diagonal d).PosDef
参数：∀ (i : n), 0 < d i；Matrix.diagonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_diagonal_of_self_adjoint`：isHermitian_diagonal_of_sel
f_adjoint [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v) : (diagonal v).IsHe
rmitian
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finsupp.sum_pos'`：sum_pos' (h : forall i in f.support, 0 <= g i (f i)) (
hf : exists i in f.support, 0 < g i (f i)) : 0 < f.sum g
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.sum_nonneg`：sum_nonneg (h : forall i in f.support, 0 <= h₁ i (f 
i)) : 0 <= f.sum h₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `star_left_conjugate_nonneg`：star_left_conjugate_nonneg {a : R} (ha : 0 <
= a) (c : R) : 0 <= star c * a * c
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
（共 35 条，此处仅展示前 30 条）
-/
protected theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n → R} (h : ∀ i, 0 < d i) :
    PosDef (diagonal d) where
  left := isHermitian_diagonal_of_self_adjoint _ <| funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ ↦ Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]
/-
**Matrix.PosDef._root_.Matrix.posDef_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n → R} :
    PosDef (diagonal d) ↔ ∀ i, 0 < d i :=
  ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

@[simp, nontriviality]
/-
**Matrix.PosDef.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.PosDef
参数：h : Subsingleton R；M : Matrix n n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.of_subsingleton`：∀ {α : Type u_1} {n : Type u_4} [ins
t : Star α] {A : Matrix n n α} [Subsingleton α], A.IsHermitian
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.PosDef :=
  ⟨.of_subsingleton, fun _ hx ↦ (hx <| Subsingleton.elim ..).elim⟩
/-
**Matrix.PosDef.one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] [NoZeroDivi
sors R], Matrix.PosDef 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.PosDef.diagonal`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] 
[inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : 
DecidableEq …
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
-/
protected theorem one [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] :
    PosDef (1 : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun i ↦ zero_lt_one' R
/-
**Matrix.PosDef.natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] [NoZeroDivi
sors R] (d : ℕ), d ≠ 0 → (↑d).PosDef
参数：d : ℕ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.PosDef.diagonal`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] 
[inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : 
DecidableEq …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
protected theorem natCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) (hd : d ≠ 0) :
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

@[simp]
/-
**Matrix.PosDef._root_.Matrix.posDef_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_natCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : ℕ} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
  posDef_diagonal_iff.trans <| by simp
/-
**Matrix.PosDef.ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] [NoZeroDivi
sors R] (d : ℕ) [inst_6 : d.AtLeastTwo], (OfNat.ofNat d).PosDef
参数：d : ℕ；OfNat.ofNat d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.natCast`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [
inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : D
ecidableEq …
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
protected theorem ofNat [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℕ) [d.AtLeastTwo] :
    PosDef (ofNat(d) : Matrix n n R) :=
  .natCast d (NeZero.ne _)
/-
**Matrix.PosDef.intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : DecidableEq n] [NoZeroDivi
sors R] (d : ℤ), 0 < d → (↑d).PosDef
参数：d : ℤ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.PosDef.diagonal`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] 
[inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : 
DecidableEq …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
-/
protected theorem intCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : ℤ) (hd : 0 < d) :
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ ↦ by simpa [pos_iff_ne_zero]

@[simp]
/-
**Matrix.PosDef._root_.Matrix.posDef_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_intCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : ℤ} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
  posDef_diagonal_iff.trans <| by simp
/-
**Matrix.PosDef.add_posSemidef** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {m : Type u_1} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [AddLeftMono R]   {A B : Matrix m m R}, A.PosDef → B.PosSe
midef → (A + B).PosDef
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.add`：∀ {α : Type u_1} {n : Type u_4} [inst : AddMonoi
d α] [inst_1 : StarAddMonoid α] {A B : Matrix n n α},   A.IsHermitian → B.IsHerm
itian → (A +…
· 使用定理 `Matrix.PosDef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.PosDef
) : M.IsHermitian
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma add_posSemidef [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩
/-
**Matrix.PosDef.posSemidef_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {m : Type u_1} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [AddLeftMono R]   {A B : Matrix m m R}, A.PosSemidef → B.P
osDef → (A + B).PosDef
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.add_posSemidef`：∀ {m : Type u_1} {R : Type u_3} [inst : Ri
ng R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [AddLeftMono R]   {A B : M
atrix m m R}, A.Po…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected lemma posSemidef_add [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosDef) : (A + B).PosDef :=
  add_comm A B ▸ hB.add_posSemidef hA
/-
**Matrix.PosDef.add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {m : Type u_1} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [AddLeftMono R]   {A B : Matrix m m R}, A.PosDef → B.PosDe
f → (A + B).PosDef
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.add_posSemidef`：∀ {m : Type u_1} {R : Type u_3} [inst : Ri
ng R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [AddLeftMono R]   {A B : M
atrix m m R}, A.Po…
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
-/
protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosDef) : (A + B).PosDef :=
  hA.add_posSemidef hB.posSemidef
/-
**Matrix.PosDef._root_.Matrix.posDef_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDe
f`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_sum {ι : Type*} [AddLeftMono R] {A : ι → Matrix m m R}
    {s : Finset ι} (hs : s.Nonempty) (hA : ∀ i ∈ s, (A i).PosDef) : (∑ i ∈ s, A i).PosDef := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
      · exact PosDef.add (hA _ <| Finset.mem_insert_self i hi) <|
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)
/-
**Matrix.PosDef.smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] {α : Type u_5}   [inst_3 : CommSemiring α] [inst_4 : Parti
alOrder α] [inst_5 : StarRing α] [StarOrderedRing α] [inst_7 : Algebra α R]   [S
tarModule α R] [PosSMulStrictMono α R] {x : Matrix n n R}, x.PosDef → ∀ {a : α},
 0 < a → (a • x).PosDef
参数：a • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulStrictMono α R]
    {x : Matrix n n R} (hx : x.PosDef) {a : α} (ha : 0 < a) : (a • x).PosDef := by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha.le) hx.1, fun y hy => ?_⟩
  simpa [← Finsupp.smul_sum] using smul_pos ha (hx.2 hy)
/-
**Matrix.PosDef.conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：conjTranspose {M : Matrix n n R} (hM : M.PosDef) : Mᴴ.PosDef
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem conjTranspose {M : Matrix n n R} (hM : M.PosDef) : Mᴴ.PosDef := hM.1.symm ▸ hM

@[simp]
/-
**Matrix.PosDef._root_.Matrix.posDef_conjTranspose_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_conjTranspose_iff {M : Matrix n n R} : Mᴴ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩
/-
**Matrix.PosDef.diag_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：diag_pos [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n} : 0 < A
 i i
参数：hA : A.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma diag_pos [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n} : 0 < A i i := by
  simpa [trace] using hA.2 (x := Finsupp.single i 1)

end PosDef

/-!
## Finite positive semidefinite matrices
-/

variable [Fintype n] [Fintype m]

/-- A finite matrix `M : Matrix n n R` is positive semidefinite iff it is
Hermitian and `xᴴ * M * x` is nonnegative for all `x`. -/
/-
**Matrix.posSemidef_iff_dotProduct_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_iff_dotProduct_mulVec {M : Matrix n n R} : M.PosSemidef ↔ M.IsH
ermitian ∧ forall x, 0 <= star x ⬝ᵥ (M *ᵥ x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A finite matrix `M : Matrix n n R` is positive semidefinite iff it is
Hermitian and `xᴴ * M * x` is nonnegative for all `x`.
-/
theorem posSemidef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := by
  simp [PosSemidef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

namespace PosSemidef

@[simp]
/-
**Matrix.PosSemidef.dotProduct_mulVec_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.P
osSemidef`。
形式化陈述：dotProduct_mulVec_nonneg {M : Matrix n n R} (hM : M.PosSemidef) : forall x
 : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x)
参数：hM : M.PosSemidef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.posSemidef_iff_dotProduct_mulVec`：posSemidef_iff_dotProduct_mulVe
c {M : Matrix n n R} : M.PosSemidef ↔ M.IsHermitian ∧ forall x, 0 <= star x ⬝ᵥ (
M *ᵥ x)
-/
theorem dotProduct_mulVec_nonneg {M : Matrix n n R} (hM : M.PosSemidef) :
    ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := (posSemidef_iff_dotProduct_mulVec.mp hM).2
/-
**Matrix.PosSemidef.of_dotProduct_mulVec_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.PosSemidef`。
形式化陈述：of_dotProduct_mulVec_nonneg {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 
: forall x, 0 <= star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef
参数：hM1 : M.IsHermitian；hM2 : forall x, 0 <= star x ⬝ᵥ (M *ᵥ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.posSemidef_iff_dotProduct_mulVec`：posSemidef_iff_dotProduct_mulVe
c {M : Matrix n n R} : M.PosSemidef ↔ M.IsHermitian ∧ forall x, 0 <= star x ⬝ᵥ (
M *ᵥ x)
-/
lemma of_dotProduct_mulVec_nonneg {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ x, 0 ≤ star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

omit [Fintype m] in variable [Finite m] in
/-
**Matrix.PosSemidef.conjTranspose_mul_mul_same** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
.PosSemidef`。
形式化陈述：conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Mat
rix n m R) : PosSemidef (Bᴴ * A * B)
参数：hA : PosSemidef A；B : Matrix n m R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`：of_dotProduct_mulVec_nonn
eg {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 : forall x, 0 <= star x ⬝ᵥ (M *
ᵥ x)) : M.PosSemidef
· 使用定理 `Matrix.isHermitian_conjTranspose_mul_mul`：isHermitian_conjTranspose_mul_
mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α) (hA : A.IsHermitian) : (Bᴴ
 * A * B).IsHermitian
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.star_mulVec`：star_mulVec [Fintype n] [StarRing α] (M : Matrix m n
 α) (v : n -> α) : star (M *ᵥ v) = star v ᵥ* Mᴴ
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.PosSemidef.dotProduct_mulVec_nonneg`：dotProduct_mulVec_nonneg {M 
: Matrix n n R} (hM : M.PosSemidef) : forall x : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x)
-/
lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  have := Fintype.ofFinite m
  refine of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x ↦ ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hA.dotProduct_mulVec_nonneg (B *ᵥ x)

omit [Fintype m] in variable [Finite m] in
/-
**Matrix.PosSemidef.mul_mul_conjTranspose_same** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
.PosSemidef`。
形式化陈述：mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A) (B : Mat
rix m n R) : PosSemidef (B * A * Bᴴ)
参数：hA : PosSemidef A；B : Matrix m n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.PosSemidef.conjTranspose_mul_mul_same`：conjTranspose_mul_mul_same
 {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) : PosSemidef (Bᴴ * A 
* B)
-/
lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix m n R) :
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ
/-
**Matrix.PosSemidef.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [inst_3 : Fintype n]   [StarOrderedRing R] [inst_5 : Decid
ableEq n] {M : Matrix n n R}, M.PosSemidef → ∀ (k : ℕ), (M ^ k).PosSemidef
参数：k : ℕ；M ^ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma pow [StarOrderedRing R] [DecidableEq n]
    {M : Matrix n n R} (hM : M.PosSemidef) (k : ℕ) :
    PosSemidef (M ^ k) :=
  match k with
  | 0 => .one
  | 1 => by simpa using hM
  | (k + 2) => by
    rw [pow_succ, pow_succ']
    simpa only [hM.isHermitian.eq] using (hM.pow k).mul_mul_conjTranspose_same M
/-
**Matrix.PosSemidef.inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R' : Type u_4} [inst : CommRing R'] [inst_1 : PartialOrd
er R'] [inst_2 : StarRing R']   [inst_3 : Fintype n] [inst_4 : DecidableEq n] {M
 : Matrix n n R'}, M.PosSemidef → M⁻¹.PosSemidef
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosSemidef.conjTranspose`：conjTranspose {M : Matrix n n R} (hM : 
M.PosSemidef) : Mᴴ.PosSemidef
· 使用引理 `Matrix.PosSemidef.conjTranspose_mul_mul_same`：conjTranspose_mul_mul_same
 {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) : PosSemidef (Bᴴ * A 
* B)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.mul_nonsing_inv_cancel_right`：mul_nonsing_inv_cancel_right (B : M
atrix m n α) (h : IsUnit A.det) : B * A * A⁻¹ = B
· 使用定理 `Matrix.nonsing_inv_apply_not_isUnit`：nonsing_inv_apply_not_isUnit (h : ¬
IsUnit A.det) : A⁻¹ = 0
· 使用定理 `Matrix.PosSemidef.zero`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] 
[inst_1 : PartialOrder R] [inst_2 : StarRing R], Matrix.PosSemidef 0
-/
protected lemma inv [DecidableEq n] {M : Matrix n n R'} (hM : M.PosSemidef) : M⁻¹.PosSemidef := by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero
/-
**Matrix.PosSemidef.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：∀ {n : Type u_2} {R' : Type u_4} [inst : CommRing R'] [inst_1 : PartialOrd
er R'] [inst_2 : StarRing R']   [inst_3 : Fintype n] [StarOrderedRing R'] [inst_
5 : DecidableEq n] {M : Matrix n n R'},   M.PosSemidef → ∀ (z : ℤ), (M ^ z).PosS
emidef
参数：z : ℤ；M ^ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Matrix.PosSemidef.pow`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [
inst_1 : PartialOrder R] [inst_2 : StarRing R] [inst_3 : Fintype n]   [StarOrder
edRing R] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.zpow_neg_natCast`：zpow_neg_natCast (A : M) (n : Nat) : A ^ (-n : 
Int) = (A ^ n)⁻¹
· 使用定理 `Matrix.PosSemidef.inv`：∀ {n : Type u_2} {R' : Type u_4} [inst : CommRing
 R'] [inst_1 : PartialOrder R'] [inst_2 : StarRing R']   [inst_3 : Fintype n] [i
nst_4 : Dec…
-/
protected lemma zpow [StarOrderedRing R'] [DecidableEq n]
    {M : Matrix n n R'} (hM : M.PosSemidef) (z : ℤ) :
    (M ^ z).PosSemidef := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv
/-
**Matrix.PosSemidef.trace_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 <=
 A.trace
参数：hA : A.PosSemidef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_nonneg`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Preorder M] [AddLeftMono M]   {f : ι → M}, 0
 ≤ f → 0…
· 使用引理 `Matrix.PosSemidef.diag_nonneg`：diag_nonneg {A : Matrix n n R} (hA : A.Po
sSemidef) {i : n} : 0 <= A i i
-/
lemma trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 ≤ A.trace :=
  Fintype.sum_nonneg fun _ ↦ hA.diag_nonneg

end PosSemidef

omit [Fintype n] in variable [Finite n] in
/-- The conjugate transpose of a matrix multiplied by the matrix is positive semidefinite -/
/-
**Matrix.posSemidef_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
 PosSemidef (Aᴴ * A)
参数：A : Matrix m n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`：of_dotProduct_mulVec_nonn
eg {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 : forall x, 0 <= star x ⬝ᵥ (M *
ᵥ x)) : M.PosSemidef
· 使用定理 `Matrix.isHermitian_conjTranspose_mul_self`：isHermitian_conjTranspose_mul
_self [Fintype m] (A : Matrix m n α) : (Aᴴ * A).IsHermitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Matrix.vecMul_conjTranspose`：vecMul_conjTranspose [Fintype n] [StarRing 
α] (A : Matrix m n α) (x : n -> α) : x ᵥ* Aᴴ = star (A *ᵥ star x)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r

--- 原说明 ---
The conjugate transpose of a matrix multiplied by the matrix is positive semidef
inite
-/
theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_self _) fun x => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

omit [Fintype m] in variable [Finite m] in
/-- A matrix multiplied by its conjugate transpose is positive semidefinite -/
/-
**Matrix.posSemidef_self_mul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
 PosSemidef (A * Aᴴ)
参数：A : Matrix m n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.posSemidef_conjTranspose_mul_self`：posSemidef_conjTranspose_mul_s
elf [StarOrderedRing R] (A : Matrix m n R) : PosSemidef (Aᴴ * A)

--- 原说明 ---
A matrix multiplied by its conjugate transpose is positive semidefinite
-/
theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

section trace
-- TODO: move these results to an earlier file

variable {R : Type*} [PartialOrder R] [NonUnitalRing R]
  [StarRing R] [StarOrderedRing R] [NoZeroDivisors R]

/-
**Matrix.trace_conjTranspose_mul_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix`。
形式化陈述：trace_conjTranspose_mul_self_eq_zero_iff {A : Matrix m n R} : (Aᴴ * A).tra
ce = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.star_vec_dotProduct_vec`：star_vec_dotProduct_vec [AddCommMonoid R
] [Mul R] [Star R] [Fintype m] [Fintype n] (A B : Matrix m n R) : star (vec A) ⬝
ᵥ vec B = (Aᴴ * B).t…
· 使用定理 `dotProduct_star_self_eq_zero`：dotProduct_star_self_eq_zero {v : n -> R} 
: star v ⬝ᵥ v = 0 ↔ v = 0
· 使用定理 `Matrix.vec_eq_zero_iff`：vec_eq_zero_iff [Zero R] {A : Matrix m n R} : ve
c A = 0 ↔ A = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trace_conjTranspose_mul_self_eq_zero_iff {A : Matrix m n R} :
    (Aᴴ * A).trace = 0 ↔ A = 0 := by
  rw [← star_vec_dotProduct_vec, dotProduct_star_self_eq_zero, vec_eq_zero_iff]
/-
**Matrix.trace_mul_conjTranspose_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix`。
形式化陈述：trace_mul_conjTranspose_self_eq_zero_iff {A : Matrix m n R} : (A * Aᴴ).tra
ce = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`：trace_conjTranspose_mul
_self_eq_zero_iff {A : Matrix m n R} : (Aᴴ * A).trace = 0 ↔ A = 0
-/
theorem trace_mul_conjTranspose_self_eq_zero_iff {A : Matrix m n R} :
    (A * Aᴴ).trace = 0 ↔ A = 0 := by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

end trace

section conjugate
variable [DecidableEq n] {U x : Matrix n n R}

/-- For an invertible matrix `U`, `star U * x * U` is positive semi-definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_left_conjugate_nonneg_iff` for a similar statement for star-ordered rings. -/
/-
**Matrix.IsUnit.posSemidef_star_left_conjugate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix.IsUnit`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [inst_3 : Fintype n]   [inst_4 : DecidableEq n] {U x : Mat
rix n n R}, IsUnit U → ((star U * x * U).PosSemidef ↔ x.PosSemidef)
参数：(star U * x * U).PosSemidef ↔ x.PosSemidef。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用引理 `Matrix.PosSemidef.conjTranspose_mul_mul_same`：conjTranspose_mul_mul_same
 {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) : PosSemidef (Bᴴ * A 
* B)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `Matrix.star_eq_conjTranspose`：star_eq_conjTranspose [Star α] (M : Matrix
 m m α) : star M = Mᴴ

--- 原说明 ---
For an invertible matrix `U`, `star U * x * U` is positive semi-definite iff `x`
 is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_left_conjugate_nonneg_iff` for a similar statement for star-ord
ered rings.
-/
theorem IsUnit.posSemidef_star_left_conjugate_iff (hU : IsUnit U) :
    PosSemidef (star U * x * U) ↔ x.PosSemidef := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conjTranspose_mul_mul_same _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/-- For an invertible matrix `U`, `U * x * star U` is positive semi-definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_right_conjugate_nonneg_iff` for a similar statement for star-ordered rings. -/
/-
**Matrix.IsUnit.posSemidef_star_right_conjugate_iff** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.IsUnit`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : StarRing R] [inst_3 : Fintype n]   [inst_4 : DecidableEq n] {U x : Mat
rix n n R}, IsUnit U → ((U * x * star U).PosSemidef ↔ x.PosSemidef)
参数：(U * x * star U).PosSemidef ↔ x.PosSemidef。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.IsUnit.posSemidef_star_left_conjugate_iff`：∀ {n : Type u_2} {R : 
Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [inst_
3 : Fintype n]   [inst_4 : DecidableEq…
· 使用定理 `IsUnit.star`：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul R] {a : 
R}, IsUnit a → IsUnit (star a)

--- 原说明 ---
For an invertible matrix `U`, `U * x * star U` is positive semi-definite iff `x`
 is.
This works on any ⋆-ring with a partial order.

See `IsUnit.star_right_conjugate_nonneg_iff` for a similar statement for star-or
dered rings.
-/
theorem IsUnit.posSemidef_star_right_conjugate_iff (hU : IsUnit U) :
    PosSemidef (U * x * star U) ↔ x.PosSemidef := by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

end conjugate

omit [Fintype n] [Fintype m] in variable [Finite n] [Finite m] in
/-- The matrix `vecMulVec a (star a)` is always positive semi-definite. -/
/-
**Matrix.posSemidef_vecMulVec_self_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n -> R) : (vecMulV
ec a (star a)).PosSemidef
参数：a : n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v

--- 原说明 ---
The matrix `vecMulVec a (star a)` is always positive semi-definite.
-/
theorem posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n → R) :
    (vecMulVec a (star a)).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

omit [Fintype n] in variable [Finite n] in
/-- The matrix `vecMulVec (star a) a` is always positive semi-definite. -/
/-
**Matrix.posSemidef_vecMulVec_star_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n -> R) : (vecMulV
ec (star a) a).PosSemidef
参数：a : n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
The matrix `vecMulVec (star a) a` is always positive semi-definite.
-/
theorem posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n → R) :
    (vecMulVec (star a) a).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]

/-!
## Finite Positive definite matrices
-/

/-
**Matrix.posDef_iff_dotProduct_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：posDef_iff_dotProduct_mulVec {M : Matrix n n R} : M.PosDef ↔ M.IsHermitian
 ∧ forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M *ᵥ x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.coe_eq_zero`：coe_eq_zero {f : α ->₀ M} : (f : α -> M) = 0 ↔ f = 
0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
## Finite Positive definite matrices
-/
theorem posDef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosDef ↔ M.IsHermitian ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x) := by
  have (x : n →₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 ↦ Finsupp.coe_eq_zero.mpr h1,fun h2 ↦ Finsupp.coe_eq_zero.mp h2⟩
  simp [PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

namespace PosDef

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
@[simp]
/-
**Matrix.PosDef.dotProduct_mulVec_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x != 0)
 : 0 < star x ⬝ᵥ (M *ᵥ x)
参数：hM : M.PosDef；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.posDef_iff_dotProduct_mulVec`：posDef_iff_dotProduct_mulVec {M : M
atrix n n R} : M.PosDef ↔ M.IsHermitian ∧ forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M
 *ᵥ x)

--- 原说明 ---
A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`.
-/
lemma dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x ≠ 0) :
    0 < star x ⬝ᵥ (M *ᵥ x) := (posDef_iff_dotProduct_mulVec.mp hM).2 hx
/-
**Matrix.PosDef.of_dotProduct_mulVec_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDe
f`。
形式化陈述：of_dotProduct_mulVec_pos {M : Matrix n n R} (hM1 : M.IsHermitian) (hM2 : f
orall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef
参数：hM1 : M.IsHermitian；hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M *ᵥ x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.posDef_iff_dotProduct_mulVec`：posDef_iff_dotProduct_mulVec {M : M
atrix n n R} : M.PosDef ↔ M.IsHermitian ∧ forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M
 *ᵥ x)
-/
lemma of_dotProduct_mulVec_pos {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef :=
  posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩
/-
**Matrix.PosDef.conjTranspose_mul_mul_same** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Pos
Def`。
形式化陈述：conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.P
osDef) (hB : Function.Injective B.mulVec) : (Bᴴ * A * B).PosDef
参数：hA : A.PosDef；hB : Function.Injective B.mulVec。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosDef.of_dotProduct_mulVec_pos`：of_dotProduct_mulVec_pos {M : Ma
trix n n R} (hM1 : M.IsHermitian) (hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M 
*ᵥ x)) : M.PosDef
· 使用定理 `Matrix.isHermitian_conjTranspose_mul_mul`：isHermitian_conjTranspose_mul_
mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α) (hA : A.IsHermitian) : (Bᴴ
 * A * B).IsHermitian
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Matrix.mulVec_zero`：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.star_mulVec`：star_mulVec [Fintype n] [StarRing α] (M : Matrix m n
 α) (v : n -> α) : star (M *ᵥ v) = star v ᵥ* Mᴴ
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
-/
lemma conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
  refine of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_mul _ hA.1) fun x hx => ?_
  have : B *ᵥ x ≠ 0 := fun h => hx <| hB.eq_iff' (mulVec_zero _) |>.1 h
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.dotProduct_mulVec_pos this
/-
**Matrix.PosDef.mul_mul_conjTranspose_same** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Pos
Def`。
形式化陈述：mul_mul_conjTranspose_same {A : Matrix n n R} {B : Matrix m n R} (hA : A.P
osDef) (hB : Function.Injective B.vecMul) : (B * A * Bᴴ).PosDef
参数：hA : A.PosDef；hB : Function.Injective B.vecMul。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `Matrix.PosDef.conjTranspose_mul_mul_same`：conjTranspose_mul_mul_same {A 
: Matrix n n R} {B : Matrix n m R} (hA : A.PosDef) (hB : Function.Injective B.mu
lVec) : (Bᴴ * A * B).PosDef
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.star_vecMul`：star_vecMul [Fintype m] [StarRing α] (M : Matrix m n
 α) (v : m -> α) : star (v ᵥ* M) = Mᴴ *ᵥ star v
-/
lemma mul_mul_conjTranspose_same {A : Matrix n n R} {B : Matrix m n R} (hA : A.PosDef)
    (hB : Function.Injective B.vecMul) :
    (B * A * Bᴴ).PosDef := by
  replace hB := star_injective.comp <| hB.comp star_injective
  simp_rw [Function.comp_def, star_vecMul, star_star] at hB
  simpa using hA.conjTranspose_mul_mul_same (B := Bᴴ) hB
/-
**Matrix.PosDef.conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`
。
形式化陈述：conjTranspose_mul_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix 
m n R) (hA : Function.Injective A.mulVec) : PosDef (Aᴴ * A)
参数：A : Matrix m n R；hA : Function.Injective A.mulVec。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用引理 `Matrix.PosDef.conjTranspose_mul_mul_same`：conjTranspose_mul_mul_same {A 
: Matrix n n R} {B : Matrix n m R} (hA : A.PosDef) (hB : Function.Injective B.mu
lVec) : (Bᴴ * A * B).PosDef
· 使用定理 `Matrix.PosDef.one`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : Decid
ableEq …
-/
theorem conjTranspose_mul_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.mulVec) :
    PosDef (Aᴴ * A) := by
  classical
  simpa using conjTranspose_mul_mul_same .one hA
/-
**Matrix.PosDef.mul_conjTranspose_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`
。
形式化陈述：mul_conjTranspose_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix 
m n R) (hA : Function.Injective A.vecMul) : PosDef (A * Aᴴ)
参数：A : Matrix m n R；hA : Function.Injective A.vecMul。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用引理 `Matrix.PosDef.mul_mul_conjTranspose_same`：mul_mul_conjTranspose_same {A 
: Matrix n n R} {B : Matrix m n R} (hA : A.PosDef) (hB : Function.Injective B.ve
cMul) : (B * A * Bᴴ).PosDef
· 使用定理 `Matrix.PosDef.one`：∀ {n : Type u_2} {R : Type u_3} [inst : Ring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 : Decid
ableEq …
-/
theorem mul_conjTranspose_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.vecMul) :
    PosDef (A * Aᴴ) := by
  classical
  simpa using mul_mul_conjTranspose_same .one hA
/-
**Matrix.PosDef.of_toQuadraticForm'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：of_toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
 [TrivialStar R] [DecidableEq n] {M : Matrix n n R} (hM : M.IsSymm) (hMq : M.toQ
uadraticForm'.PosDef) : M.PosDef
参数：hM : M.IsSymm；hMq : M.toQuadraticForm'.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosDef.of_dotProduct_mulVec_pos`：of_dotProduct_mulVec_pos {M : Ma
trix n n R} (hM1 : M.IsHermitian) (hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M 
*ᵥ x)) : M.PosDef
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)
· 使用定理 `Matrix.toLinearMap₂'_apply'`：∀ {n : Type u_11} {m : Type u_12} [inst : F
intype n] [inst_1 : Fintype m] [inst_2 : DecidableEq n]   [inst_3 : DecidableEq 
m] {T : Type u_16…
-/
theorem of_toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [DecidableEq n] {M : Matrix n n R} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine of_dotProduct_mulVec_pos (by simpa) fun x hx ↦ ?_
  simpa [toQuadraticForm', toLinearMap₂'_apply'] using hMq x hx
/-
**Matrix.PosDef.toQuadraticForm'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [T
rivialStar R] [DecidableEq n] {M : Matrix n n R} (hM : M.PosDef) : M.toQuadratic
Form'.PosDef
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLinearMap₂'_apply'`：∀ {n : Type u_11} {m : Type u_12} [inst : F
intype n] [inst_1 : Fintype m] [inst_2 : DecidableEq n]   [inst_3 : DecidableEq 
m] {T : Type u_16…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
-/
theorem toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [DecidableEq n] {M : Matrix n n R} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simpa [Matrix.toQuadraticForm', toLinearMap₂'_apply'] using hM.dotProduct_mulVec_pos hx

/-- See also `LinearMap.isPosSemidef_iff_posSemidef_toMatrix` for the semi-definite case. -/
/-
**Matrix.PosDef._root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix** 是 
Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `LinearMap.isPosSemidef_iff_posSemidef_toMatrix` for the semi-definite 
case.
-/
theorem _root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    {R M : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [AddCommGroup M] [Module R M] [DecidableEq n]
    (b : Module.Basis n R M) (B : LinearMap.BilinForm R M) (hB_symm : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ (B.toMatrix b).PosDef := by
  have aux (i j : n) (s t : R) : t * B (b i) (b j) * s = t * (s * B (b j) (b i)) := by
    grind [hB_symm.eq (b i) (b j)]
  refine ⟨fun h ↦ ⟨?_, fun v hv ↦ ?_⟩, fun h v hv ↦ ?_⟩
  · simp [isHermitian_iff_isSymm, IsSymm.ext_iff, hB_symm.eq (b _) (b _)]
  · simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, ← aux] using
      h _ (b.repr.symm.map_ne_zero_iff.mpr hv)
  · rw [B.toQuadraticMap_apply, ← b.linearCombination_repr (x := v)]
    simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, aux]
      using h.2 (b.repr.map_ne_zero_iff.mpr hv)
/-
**Matrix.PosDef.trace_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：trace_pos [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {A : Ma
trix n n R} (hA : A.PosDef) : 0 < A.trace
参数：hA : A.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用引理 `Matrix.PosDef.diag_pos`：diag_pos [Nontrivial R] {A : Matrix n n R} (hA :
 A.PosDef) {i : n} : 0 < A i i
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
lemma trace_pos [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {A : Matrix n n R}
    (hA : A.PosDef) : 0 < A.trace :=
  Finset.sum_pos (fun _ _ ↦ hA.diag_pos) Finset.univ_nonempty

section Field
variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]

/-
**Matrix.PosDef.isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : IsUnit M
参数：hM : M.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.not_injective_iff`：not_injective_iff : ¬ Injective f ↔ exists a
 b, f a = f b ∧ a != b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Matrix.mulVec_injective_iff_isUnit`：mulVec_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.mulVec ↔ IsUnit A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mulVec_sub`：mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n ->
 α) : A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
-/
theorem isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : IsUnit M := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : ∃ a ≠ 0, M *ᵥ a = 0 := by
    obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp <| mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.dotProduct_mulVec_pos ha
/-
**Matrix.PosDef.inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
形式化陈述：∀ {n : Type u_2} [inst : Fintype n] {K : Type u_5} [inst_1 : Field K] [ins
t_2 : PartialOrder K] [inst_3 : StarRing K]   [inst_4 : DecidableEq n] {M : Matr
ix n n K}, M.PosDef → M⁻¹.PosDef
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosDef.mul_mul_conjTranspose_same`：mul_mul_conjTranspose_same {A 
: Matrix n n R} {B : Matrix m n R} (hA : A.PosDef) (hB : Function.Injective B.ve
cMul) : (B * A * Bᴴ).PosDef
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matrix.PosDef.isUnit`：isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.
PosDef) : IsUnit M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.inv_mul_of_invertible`：inv_mul_of_invertible [Invertible A] : A⁻¹
 * A = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.PosDef.conjTranspose`：conjTranspose {M : Matrix n n R} (hM : M.Po
sDef) : Mᴴ.PosDef
-/
protected theorem inv [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : M⁻¹.PosDef := by
  have := hM.mul_mul_conjTranspose_same (B := M⁻¹) ?_
  · let _ := hM.isUnit.invertible
    simpa using this.conjTranspose
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, hM.isUnit]

@[simp]
/-
**Matrix.PosDef._root_.Matrix.posDef_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.P
osDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.posDef_inv_iff [DecidableEq n] {M : Matrix n n K} :
    M⁻¹.PosDef ↔ M.PosDef :=
  ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| h.isUnit).invertible
    Matrix.inv_inv_of_invertible M ▸ h.inv, (·.inv)⟩

end Field

section conjugate
variable [DecidableEq n] {x U : Matrix n n R}

/-- For an invertible matrix `U`, `star U * x * U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_left_conjugate_iff'` for a similar statement for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity when the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`). -/
/-
**Matrix.PosDef._root_.Matrix.IsUnit.posDef_star_left_conjugate_iff** 是 Mathlib 
中的一个定理，位于命名空间 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an invertible matrix `U`, `star U * x * U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_left_conjugate_iff'` for a similar statement
 for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity wh
en the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`).
-/
theorem _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff (hU : IsUnit U) :
    PosDef (star U * x * U) ↔ x.PosDef := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conjTranspose_mul_mul_same <| mulVec_injective_of_isUnit hU⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (Units.isUnit U⁻¹))
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/-- For an invertible matrix `U`, `U * x * star U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_right_conjugate_iff` for a similar statement for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity when the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`). -/
/-
**Matrix.PosDef._root_.Matrix.IsUnit.posDef_star_right_conjugate_iff** 是 Mathlib
 中的一个定理，位于命名空间 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an invertible matrix `U`, `U * x * star U` is positive definite iff `x` is.
This works on any ⋆-ring with a partial order.

See `IsUnit.isStrictlyPositive_star_right_conjugate_iff` for a similar statement
 for star-ordered
rings. For matrices, positive definiteness is equivalent to strict positivity wh
en the underlying
field is `ℝ` or `ℂ` (see `Matrix.isStrictlyPositive_iff_posDef`).
-/
theorem _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff (hU : IsUnit U) :
    PosDef (U * x * star U) ↔ x.PosDef := by
  simpa using hU.star.posDef_star_left_conjugate_iff

end conjugate

section SchurComplement

variable [StarOrderedRing R']

omit [Fintype n] in variable [Finite n] in
/-
**Matrix.PosDef.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks₁₁ [DecidableEq m] {A : Matrix m m R'}
    (B : Matrix m n R') (D : Matrix n n R') (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  have := Fintype.ofFinite n
  rw [posSemidef_iff_dotProduct_mulVec, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) ⊕ᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (posSemidef_iff_dotProduct_mulVec.mp h).2

omit [Fintype m] in variable [Finite m] in
/-
**Matrix.PosDef.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.PosDef`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromBlocks₂₂ [DecidableEq n] (A : Matrix m m R')
    (B : Matrix m n R') {D : Matrix n n R'} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert! fromBlocks₁₁ Bᴴ A hD <;> simp

end SchurComplement

end PosDef

end Matrix

namespace QuadraticForm


variable {n : Type*} [Fintype n]

/-
**QuadraticForm.posDef_of_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm Real (n -> Real)} (
hQ : Q.toMatrix'.PosDef) : Q.PosDef
参数：n -> Real；hQ : Q.toMatrix'.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.toQuadraticMap_associated`：toQuadraticMap_associated : (ass
ociatedHom S Q).toQuadraticMap = Q
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `Matrix.PosDef.toQuadraticForm'`：toQuadraticForm' {R : Type*} [CommRing R
] [PartialOrder R] [StarRing R] [TrivialStar R] [DecidableEq n] {M : Matrix n n 
R} (hM : M.PosDef) :…
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
-/
theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← Q.toQuadraticMap_associated ℝ,
    ← (LinearMap.toMatrix₂' ℝ).left_inv (Q.associatedHom ℝ)]
  exact hQ.toQuadraticForm'
/-
**QuadraticForm.posDef_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm Real (n -> Real)} (hQ 
: Q.PosDef) : Q.toMatrix'.PosDef
参数：n -> Real；hQ : Q.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.of_toQuadraticForm'`：of_toQuadraticForm' {R : Type*} [Comm
Ring R] [PartialOrder R] [StarRing R] [TrivialStar R] [DecidableEq n] {M : Matri
x n n R} (hM : M.IsSymm…
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `QuadraticForm.isSymm_toMatrix'`：isSymm_toMatrix' (Q : QuadraticForm R (n
 -> R)) : Q.toMatrix'.IsSymm
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `QuadraticMap.toQuadraticMap_associated`：toQuadraticMap_associated : (ass
ociatedHom S Q).toQuadraticMap = Q
-/
theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm ℝ (n → ℝ)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← Q.toQuadraticMap_associated ℝ,
    ← (LinearMap.toMatrix₂' ℝ).left_inv (Q.associatedHom ℝ)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ

end QuadraticForm

