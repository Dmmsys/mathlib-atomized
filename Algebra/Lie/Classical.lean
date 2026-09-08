/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `LieAlgebra.SpecialLinear.sl`
  * `LieAlgebra.Symplectic.sp`
  * `LieAlgebra.Orthogonal.so`
  * `LieAlgebra.Orthogonal.so'`
  * `LieAlgebra.Orthogonal.soIndefiniteEquiv`
  * `LieAlgebra.Orthogonal.typeD`
  * `LieAlgebra.Orthogonal.typeB`
  * `LieAlgebra.Orthogonal.typeDEquivSo'`
  * `LieAlgebra.Orthogonal.typeBEquivSo'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lieEquivMatrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
`2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `typeDEquivSo'`, `soIndefiniteEquiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/

@[expose] public section


universe u₁ u₂

namespace LieAlgebra

open Matrix

variable (n p q l : Type*) (R : Type u₂)
variable [DecidableEq p] [DecidableEq q] [DecidableEq l]
variable [CommRing R]

@[simp]
/-
**LieAlgebra.matrix_trace_commutator_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`
。
形式化陈述：matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.tra
ce ⁅X, Y⁆ = 0
参数：X Y : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_sub`：trace_sub (A B : Matrix n n R) : trace (A - B) = trace
 A - trace B
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.trace_mul_comm`：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A
 : Matrix m n R) (B : Matrix n m R) : trace (A * B) = trace (B * A)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

variable [DecidableEq n]
attribute [local instance 100] LieRing.ofAssociativeRing

namespace SpecialLinear

/-- The special linear Lie algebra: square matrices of trace zero. -/
/-
**LieAlgebra.SpecialLinear.sl** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SpecialLinea
r`。
形式化陈述：sl [Fintype n] : LieSubalgebra R (Matrix n n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special linear Lie algebra: square matrices of trace zero.
-/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
    lie_mem' := fun _ _ => LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ _ _ }
/-
**LieAlgebra.SpecialLinear.sl_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Spec
ialLinear`。
形式化陈述：sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val
 * A.val
参数：A B : sl n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl

section ElementaryBasis

variable {n R} [Fintype n] (i j k : n)

/-- When `i ≠ j`, the single-element matrices are elements of `sl n R`.

Along with some elements produced by `singleSubSingle`, these form a natural basis of `sl n R`. -/
/-
**LieAlgebra.SpecialLinear.single** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SpecialL
inear`。
形式化陈述：single (h : i != j) : R ->ₗ[R] sl n R
参数：h : i != j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `i ≠ j`, the single-element matrices are elements of `sl n R`.

Along with some elements produced by `singleSubSingle`, these form a natural bas
is of `sl n R`.
-/
def single (h : i ≠ j) : R →ₗ[R] sl n R :=
  Matrix.singleLinearMap R i j |>.codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h

@[simp]
/-
**LieAlgebra.SpecialLinear.val_single** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Spec
ialLinear`。
形式化陈述：val_single (h : i != j) (r : R) : (single i j h r).val = Matrix.single i j
 r
参数：h : i != j；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem val_single (h : i ≠ j) (r : R) : (single i j h r).val = Matrix.single i j r :=
  rfl

/-- The matrices with matching positive and negative elements on the diagonal are elements of
`sl n R`. Along with `single`, a subset of these form a basis for `sl n R`. -/
/-
**LieAlgebra.SpecialLinear.singleSubSingle** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra
.SpecialLinear`。
形式化陈述：singleSubSingle : R ->ₗ[R] sl n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrices with matching positive and negative elements on the diagonal are el
ements of
`sl n R`. Along with `single`, a subset of these form a basis for `sl n R`.
-/
def singleSubSingle : R →ₗ[R] sl n R :=
  LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
    LinearMap.sub_mem_ker_iff.mpr <| by simp

@[simp]
/-
**LieAlgebra.SpecialLinear.val_singleSubSingle** 是 Mathlib 中的一个定理，位于命名空间 `LieAlg
ebra.SpecialLinear`。
形式化陈述：val_singleSubSingle (r : R) : (singleSubSingle i j r).val = Matrix.single 
i i r - Matrix.single j j r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem val_singleSubSingle (r : R) :
    (singleSubSingle i j r).val = Matrix.single i i r - Matrix.single j j r :=
  rfl

@[simp]
/-
**LieAlgebra.SpecialLinear.singleSubSingle_add_singleSubSingle** 是 Mathlib 中的一个定
理，位于命名空间 `LieAlgebra.SpecialLinear`。
形式化陈述：singleSubSingle_add_singleSubSingle (r : R) : singleSubSingle i j r + sing
leSubSingle j k r = singleSubSingle i k r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleSubSingle_add_singleSubSingle (r : R) :
    singleSubSingle i j r + singleSubSingle j k r = singleSubSingle i k r := by
  ext : 1; simp

@[simp]
/-
**LieAlgebra.SpecialLinear.singleSubSingle_sub_singleSubSingle** 是 Mathlib 中的一个定
理，位于命名空间 `LieAlgebra.SpecialLinear`。
形式化陈述：singleSubSingle_sub_singleSubSingle (r : R) : singleSubSingle i k r - sing
leSubSingle i j r = singleSubSingle j k r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleSubSingle_sub_singleSubSingle (r : R) :
    singleSubSingle i k r - singleSubSingle i j r = singleSubSingle j k r := by
  ext : 1; simp

@[simp]
/-
**LieAlgebra.SpecialLinear.singleSubSingle_sub_singleSubSingle'** 是 Mathlib 中的一个
定理，位于命名空间 `LieAlgebra.SpecialLinear`。
形式化陈述：singleSubSingle_sub_singleSubSingle' (r : R) : singleSubSingle i k r - sin
gleSubSingle j k r = singleSubSingle i j r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleSubSingle_sub_singleSubSingle' (r : R) :
    singleSubSingle i k r - singleSubSingle j k r = singleSubSingle i j r := by
  ext : 1; simp

end ElementaryBasis

/-
**LieAlgebra.SpecialLinear.sl_non_abelian** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.
SpecialLinear`。
形式化陈述：sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) : ¬IsLi
eAbelian (sl n R)
参数：h : 1 < Fintype.card n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Fintype.exists_pair_of_one_lt_card`：exists_pair_of_one_lt_card (h : 1 < 
card α) : exists a b : α, a != b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LieAlgebra.SpecialLinear.sl_bracket`：sl_bracket [Fintype n] (A B : sl n 
R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
（共 31 条，此处仅展示前 30 条）
-/
theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero, ← sl_bracket, c.trivial, ZeroMemClass.coe_zero]
  simpa [A, B, Matrix.single, Matrix.mul_apply, hij.symm] using congr_fun (congr_fun c' i) i

end SpecialLinear

namespace Symplectic

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
/-
**LieAlgebra.Symplectic.sp** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Symplectic`。
形式化陈述：sp [Fintype l] : LieSubalgebra R (Matrix (l oplus l) (l oplus l) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical 
skew-symmetric
bilinear form.
-/
def sp [Fintype l] : LieSubalgebra R (Matrix (l ⊕ l) (l ⊕ l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)

end Symplectic

namespace Orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
/-
**LieAlgebra.Orthogonal.so** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：so [Fintype n] : LieSubalgebra R (Matrix n n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to th
e symmetric
bilinear form defined by the identity matrix.
-/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]
/-
**LieAlgebra.Orthogonal.mem_so** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Orthogonal`
。
形式化陈述：mem_so [Fintype n] (A : Matrix n n R) : A in so n R ↔ Aᵀ = -A
参数：A : Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Orthogonal.so.eq_1`：∀ (n : Type u_1) (R : Type u₂) [inst : Co
mmRing R] [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieAlgebra.Orthogonal
.so n R = skewAdjoi…
· 使用定理 `mem_skewAdjointMatricesLieSubalgebra`：mem_skewAdjointMatricesLieSubalgeb
ra (A : Matrix n n R) : A in skewAdjointMatricesLieSubalgebra J ↔ A in skewAdjoi
ntMatricesSubmodule J
· 使用定理 `mem_skewAdjointMatricesSubmodule`：mem_skewAdjointMatricesSubmodule : A₁ 
in skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_so [Fintype n] (A : Matrix n n R) : A ∈ so n R ↔ Aᵀ = -A := by
  rw [so, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
/-
**LieAlgebra.Orthogonal.indefiniteDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra
.Orthogonal`。
形式化陈述：indefiniteDiagonal : Matrix (p oplus q) (p oplus q) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indefinite diagonal matrix with `p` 1s and `q` -1s.
-/
def indefiniteDiagonal : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => -1

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
/-
**LieAlgebra.Orthogonal.so'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p oplus q) (p oplus
 q) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to 
the symmetric
bilinear form defined by the indefinite diagonal matrix.
-/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p ⊕ q) (p ⊕ q) R) :=
  skewAdjointMatricesLieSubalgebra <| indefiniteDiagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
/-
**LieAlgebra.Orthogonal.Pso** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：Pso (i : R) : Matrix (p oplus q) (p oplus q) R
参数：i : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix for transforming the indefinite diagonal bilinear form into the definit
e one, provided
the parameter `i` is a square root of -1.
-/
def Pso (i : R) : Matrix (p ⊕ q) (p ⊕ q) R :=
  Matrix.diagonal <| Sum.elim (fun _ => 1) fun _ => i

variable [Fintype p] [Fintype q]
/-
**LieAlgebra.Orthogonal.pso_inv** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Orthogonal
`。
形式化陈述：pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1
参数：hi : i * i = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, h, one_apply]
  · -- x : p, y : q
    simp [Pso]
  · -- x : q, y : p
    simp [Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, h, hi, one_apply]

/-- There is a constructive inverse of `Pso p q R i`. -/
@[instance_reducible]
/-
**LieAlgebra.Orthogonal.invertiblePso** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orth
ogonal`。
形式化陈述：invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i)
参数：hi : i * i = -1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Orthogonal.pso_inv`：pso_inv {i : R} (hi : i * i = -1) : Pso p
 q R i * Pso p q R (-i) = 1

--- 原说明 ---
There is a constructive inverse of `Pso p q R i`.
-/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)
/-
**LieAlgebra.Orthogonal.indefiniteDiagonal_transform** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra.Orthogonal`。
形式化陈述：indefiniteDiagonal_transform {i : R} (hi : i * i = -1) : (Pso p q R i)ᵀ * 
indefiniteDiagonal p q R * Pso p q R i = 1
参数：hi : i * i = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
/-
**LieAlgebra.Orthogonal.soIndefiniteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.
Orthogonal`。
形式化陈述：soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p oplus 
q) R
参数：hi : i * i = -1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the indefinite and definite orthogonal Lie algebras, over
 a ring
containing a square root of -1.
-/
noncomputable def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.Orthogonal.soIndefiniteEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra.Orthogonal`。
形式化陈述：soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) : (soInd
efiniteEquiv p q R hi A : Matrix (p oplus q) (p oplus q) R) = (Pso p q R i)⁻¹ * 
(A : Matrix (p oplus q) (p oplus q) R) * Pso p q R i
参数：hi : i * i = -1；A : so' p q R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Orthogonal.soIndefiniteEquiv.eq_1`：∀ (p : Type u_2) (q : Type
 u_3) (R : Type u₂) [inst : DecidableEq p] [inst_1 : DecidableEq q] [inst_2 : Co
mmRing R]   [inst_3 : Fintype p] […
· 使用定理 `LieEquiv.trans_apply`：trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) 
(x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x)
· 使用定理 `LieEquiv.ofEq_apply`：ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Se
t L₁) = L') (x : L) : (↑(ofEq L L' h x) : L₁) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `skewAdjointMatricesLieSubalgebraEquiv_apply`：skewAdjointMatricesLieSubal
gebraEquiv_apply (P : Matrix n n R) (h : Invertible P) (A : skewAdjointMatricesL
ieSubalgebra J) : ↑(skewAdjointMa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (p ⊕ q) (p ⊕ q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (p ⊕ q) (p ⊕ q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  simp only [so', skewAdjointMatricesLieSubalgebraEquiv_apply]

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

```
[ 0 1 ]
[ 1 0 ]
```
-/
/-
**LieAlgebra.Orthogonal.JD** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：JD : Matrix (l oplus l) (l oplus l) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

```
[ 0 1 ]
[ 1 0 ]
```
-/
def JD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
/-
**LieAlgebra.Orthogonal.typeD** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：typeD [Fintype l]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The classical Lie algebra of type D as a Lie subalgebra of matrices associated t
o the matrix
`JD`.
-/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

```
[ 1 -1 ]
[ 1  1 ]
``` -/
/-
**LieAlgebra.Orthogonal.PD** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：PD : Matrix (l oplus l) (l oplus l) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix transforming the bilinear form defined by the matrix `JD` into a split-
signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

```
[ 1 -1 ]
[ 1  1 ]
```
-/
def PD : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
/-
**LieAlgebra.Orthogonal.S** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The split-signature diagonal matrix.
-/
def S :=
  indefiniteDiagonal l l R
/-
**LieAlgebra.Orthogonal.s_as_blocks** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Orthog
onal`。
形式化陈述：s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.diagonal_neg`：diagonal_neg [NegZeroClass α] (d : n -> α) : -diago
nal d = diagonal fun i => -d i
· 使用定理 `Matrix.fromBlocks_diagonal`：fromBlocks_diagonal (d₁ : l -> α) (d₂ : m ->
 α) : fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂)
-/
theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  rfl
/-
**LieAlgebra.Orthogonal.jd_transform** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Ortho
gonal`。
形式化陈述：jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LieAlgebra.Orthogonal.PD.eq_1`：∀ (l : Type u_4) (R : Type u₂) [inst : De
cidableEq l] [inst_1 : CommRing R],   LieAlgebra.Orthogonal.PD l R = Matrix.from
Blocks 1 (-1) 1 1
· 使用定理 `LieAlgebra.Orthogonal.s_as_blocks`：s_as_blocks : S l R = Matrix.fromBloc
ks 1 0 0 (-1)
· 使用定理 `Matrix.fromBlocks_smul`：fromBlocks_smul [SMul R α] (x : R) (A : Matrix n
 l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : x • fromBlocks 
A B C D = fr…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
-/
theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h, PD, s_as_blocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
  simp [two_smul]
/-
**LieAlgebra.Orthogonal.pd_inv** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Orthogonal`
。
形式化陈述：pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟(2 : R) • (PD l R)ᵀ = 
1
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Orthogonal.PD.eq_1`：∀ (l : Type u_4) (R : Type u₂) [inst : De
cidableEq l] [inst_1 : CommRing R],   LieAlgebra.Orthogonal.PD l R = Matrix.from
Blocks 1 (-1) 1 1
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `Matrix.fromBlocks_smul`：fromBlocks_smul [SMul R α] (x : R) (A : Matrix n
 l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : x • fromBlocks 
A B C D = fr…
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Matrix.fromBlocks_one`：fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 
0 (1 : Matrix m m α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_multiply]
  simp
/-
**LieAlgebra.Orthogonal.invertiblePD** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Ortho
gonal`。
形式化陈述：invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R)
参数：2 : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Orthogonal.pd_inv`：pd_inv [Fintype l] [Invertible (2 : R)] : 
PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1
-/
instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
/-
**LieAlgebra.Orthogonal.typeDEquivSo'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orth
ogonal`。
形式化陈述：typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R
参数：2 : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between two possible definitions of the classical Lie algebra of 
type D.
-/
noncomputable def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

```
[ 2 0 0 ]
[ 0 0 1 ]
[ 0 1 0 ]
```

where sizes of the blocks are:

```
[`1 x 1` `1 x l` `1 x l`]
[`l x 1` `l x l` `l x l`]
[`l x 1` `l x l` `l x l`]
```
-/
/-
**LieAlgebra.Orthogonal.JB** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：JB
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

```
[ 2 0 0 ]
[ 0 0 1 ]
[ 0 1 0 ]
```

where sizes of the blocks are:

```
[`1 x 1` `1 x l` `1 x l`]
[`l x 1` `l x l` `l x l`]
[`l x 1` `l x l` `l x l`]
```
-/
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
/-
**LieAlgebra.Orthogonal.typeB** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：typeB [Fintype l]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The classical Lie algebra of type B as a Lie subalgebra of matrices associated t
o the matrix
`JB`.
-/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)

/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

```
[ 1 0  0 ]
[ 0 1 -1 ]
[ 0 1  1 ]
```

where sizes of the blocks are:

```
[`1 x 1` `1 x l` `1 x l`]
[`l x 1` `l x l` `l x l`]
[`l x 1` `l x l` `l x l`]
``` -/
/-
**LieAlgebra.Orthogonal.PB** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orthogonal`。
形式化陈述：PB
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

```
[ 1 0  0 ]
[ 0 1 -1 ]
[ 0 1  1 ]
```

where sizes of the blocks are:

```
[`1 x 1` `1 x l` `1 x l`]
[`l x 1` `l x l` `l x l`]
[`l x 1` `l x l` `l x l`]
```
-/
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

variable [Fintype l]
/-
**LieAlgebra.Orthogonal.pb_inv** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Orthogonal`
。
形式化陈述：pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟(PD l R))
 = 1
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Orthogonal.PB.eq_1`：∀ (l : Type u_4) (R : Type u₂) [inst : De
cidableEq l] [inst_1 : CommRing R],   LieAlgebra.Orthogonal.PB l R = Matrix.from
Blocks 1 0 0 (LieAl…
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.fromBlocks_one`：fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 
0 (1 : Matrix m m α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟(PD l R)) = 1 := by
  rw [PB, Matrix.fromBlocks_multiply, mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]
/-
**LieAlgebra.Orthogonal.invertiblePB** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Ortho
gonal`。
形式化陈述：invertiblePB [Invertible (2 : R)] : Invertible (PB l R)
参数：2 : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Orthogonal.pb_inv`：pb_inv [Invertible (2 : R)] : PB l R * Mat
rix.fromBlocks 1 0 0 (⅟(PD l R)) = 1
-/
instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)
/-
**LieAlgebra.Orthogonal.jb_transform** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Ortho
gonal`。
形式化陈述：jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1
 0 0 (S l R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LieAlgebra.Orthogonal.jd_transform`：jd_transform [Fintype l] : (PD l R)ᵀ
 * JD l R * PD l R = (2 : R) • S l R
· 使用定理 `Matrix.fromBlocks_smul`：fromBlocks_smul [SMul R α] (x : R) (A : Matrix n
 l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : x • fromBlocks 
A B C D = fr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
/-
**LieAlgebra.Orthogonal.indefiniteDiagonal_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LieA
lgebra.Orthogonal`。
形式化陈述：indefiniteDiagonal_assoc : indefiniteDiagonal (Unit oplus l) l R = Matrix.
reindexLieEquiv (Equiv.sumAssoc Unit l l).symm (Matrix.fromBlocks 1 0 0 (indefin
iteDiagonal l l R))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Unit ⊕ l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr, Sum.elim_inr, Sum.inl_injective.eq_iff,
      Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
/-
**LieAlgebra.Orthogonal.typeBEquivSo'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Orth
ogonal`。
形式化陈述：typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit oplus l) l 
R
参数：2 : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between two possible definitions of the classical Lie algebra of 
type B.
-/
noncomputable def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit ⊕ l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jb_transform, ← val_unitOfInvertible (2 : R), ← Units.smul_def, LieSubalgebra.mem_coe,
    LieSubalgebra.mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]

end Orthogonal

end LieAlgebra

