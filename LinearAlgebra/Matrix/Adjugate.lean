/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.updateCol i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the minors of `A`.
Instead of defining a minor by deleting row `i` and column `j` of `A`, we
replace the `i`th row of `A` with the `j`th basis vector; the resulting matrix
has the same determinant but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

* `Matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
* `Matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/

@[expose] public section


namespace Matrix

universe u v w

variable {m : Type u} {n : Type v} {α : Type w}
variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

open Matrix Polynomial Equiv Equiv.Perm Finset

section Cramer

/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramerMap`.
  After defining `cramerMap` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/


variable (A : Matrix n n α) (b : n → α)

/-- `cramerMap A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramerMap A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramerMap A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramerMap` is well-defined but not necessarily useful.
-/
/-
**Matrix.cramerMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：cramerMap (i : n) : α
参数：i : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cramerMap A b i` is the determinant of the matrix `A` with column `i` replaced 
with `b`,
  and thus `cramerMap A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramerMap A` sends the vector `b
` to `A.det • x`.
  Otherwise, the outcome of `cramerMap` is well-defined but not necessarily usef
ul.
-/
def cramerMap (i : n) : α :=
  (A.updateCol i b).det
/-
**Matrix.cramerMap_is_linear** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramerMap_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_updateCol_add`：det_updateCol_add (M : Matrix n n R) (j : n) (
u v : n -> R) : det (updateCol M j <| u + v) = det (updateCol M j u) + det (upda
teCol M j v)
· 使用定理 `Matrix.det_updateCol_smul`：det_updateCol_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateCol M j <| s • u) = s * det (updateCol M j u)
-/
theorem cramerMap_is_linear (i : n) : IsLinearMap α fun b => cramerMap A b i :=
  { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }
/-
**Matrix.cramer_is_linear** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_is_linear : IsLinearMap α (cramerMap A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLinearMap.map_add`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _r
oot_.Modu…
· 使用定理 `Matrix.cramerMap_is_linear`：cramerMap_is_linear (i : n) : IsLinearMap α 
fun b => cramerMap A b i
· 使用定理 `IsLinearMap.map_smul`：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _
root_.Modu…
-/
theorem cramer_is_linear : IsLinearMap α (cramerMap A) := by
  constructor <;> intros <;> ext i
  · apply (cramerMap_is_linear A i).1
  · apply (cramerMap_is_linear A i).2

/-- `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
-/
/-
**Matrix.cramer** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：cramer (A : Matrix n n α) : (n -> α) ->ₗ[α] (n -> α)
参数：A : Matrix n n α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.cramer_is_linear`：cramer_is_linear : IsLinearMap α (cramerMap A)

--- 原说明 ---
`cramer A b i` is the determinant of the matrix `A` with column `i` replaced wit
h `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A * x = b` has a unique solution in `x`, `cramer A` sends the vector `b` t
o `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
-/
def cramer (A : Matrix n n α) : (n → α) →ₗ[α] (n → α) :=
  IsLinearMap.mk' (cramerMap A) (cramer_is_linear A)
/-
**Matrix.cramer_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det
参数：i : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det :=
  rfl
/-
**Matrix.cramer_transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Matrix.updateCol_transpose`：updateCol_transpose [DecidableEq m] : update
Col Mᵀ i b = (updateRow M i b)ᵀ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem cramer_transpose_apply (i : n) : cramer Aᵀ b i = (A.updateRow i b).det := by
  rw [cramer_apply, updateCol_transpose, det_transpose]
/-
**Matrix.cramer_transpose_row_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.updateCol_transpose`：updateCol_transpose [DecidableEq m] : update
Col Mᵀ i b = (updateRow M i b)ᵀ
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem cramer_transpose_row_self (i : n) : Aᵀ.cramer (A i) = Pi.single i A.det := by
  ext j
  rw [cramer_apply, Pi.single_apply]
  split_ifs with h
  · -- i = j: this entry should be `A.det`
    subst h
    simp only [updateCol_transpose, det_transpose, updateRow_eq_self]
  · -- i ≠ j: this entry should be 0
    rw [updateCol_transpose, det_transpose]
    apply det_zero_of_row_eq h
    rw [updateRow_self, updateRow_ne (Ne.symm h)]
/-
**Matrix.cramer_row_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_row_self (i : n) (h : forall j, b j = A j i) : A.cramer b = Pi.sing
le i A.det
参数：i : n；h : forall j, b j = A j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cramer_transpose_row_self`：cramer_transpose_row_self (i : n) : Aᵀ
.cramer (A i) = Pi.single i A.det
-/
theorem cramer_row_self (i : n) (h : ∀ j, b j = A j i) : A.cramer b = Pi.single i A.det := by
  rw [← transpose_transpose A, det_transpose]
  convert! cramer_transpose_row_self Aᵀ i
  exact funext h

@[simp]
/-
**Matrix.cramer_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_one : cramer (1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Matrix.cramer_row_self`：cramer_row_self (i : n) (h : forall j, b j = A j
 i) : A.cramer b = Pi.single i A.det
· 使用定理 `Matrix.one_eq_pi_single`：one_eq_pi_single {i j} : (1 : Matrix n n α) i j
 = Pi.single (M
· 使用定理 `Pi.single_comm`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} [
inst_1 : Zero M] (i : ι) (x : M) (j : ι),   Pi.single i x j = Pi.single j x i
-/
theorem cramer_one : cramer (1 : Matrix n n α) = 1 := by
  ext i j
  convert! congr_fun (cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
  · intro j
    rw [Matrix.one_eq_pi_single, Pi.single_comm]
/-
**Matrix.cramer_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_smul (r : α) (A : Matrix n n α) : cramer (r • A) = r ^ (Fintype.car
d n - 1) • cramer A
参数：r : α；A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_updateCol_smul_left`：det_updateCol_smul_left (M : Matrix n n 
R) (j : n) (s : R) (u : n -> R) : det (updateCol (s • M) j u) = s ^ (Fintype.car
d n - 1) * det (upda…
-/
theorem cramer_smul (r : α) (A : Matrix n n α) :
    cramer (r • A) = r ^ (Fintype.card n - 1) • cramer A :=
  LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

@[simp]
/-
**Matrix.cramer_subsingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n -> α)
 (i : n) : cramer A b i = b i
参数：A : Matrix n n α；b : n -> α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Matrix.det_eq_elem_of_subsingleton`：det_eq_elem_of_subsingleton [Subsing
leton n] (A : Matrix n n R) (k : n) : det A = A k k
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
-/
theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) :
    cramer A b i = b i := by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]
/-
**Matrix.cramer_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Matrix.det_eq_zero_of_column_eq_zero`：det_eq_zero_of_column_eq_zero {A :
 Matrix n n R} (j : n) (h : forall i, A i j = 0) : det A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cramer_zero [Nontrivial n] : cramer (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

/-- Use linearity of `cramer` to take it out of a summation. -/
/-
**Matrix.sum_cramer** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_cramer {β} (s : Finset β) (f : β -> n -> α) : (∑ x in s, cramer A (f x
)) = cramer A (∑ x in s, f x)
参数：s : Finset β；f : β -> n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
Use linearity of `cramer` to take it out of a summation.
-/
theorem sum_cramer {β} (s : Finset β) (f : β → n → α) :
    (∑ x ∈ s, cramer A (f x)) = cramer A (∑ x ∈ s, f x) :=
  (map_sum (cramer A) ..).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
/-
**Matrix.sum_cramer_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sum_cramer_apply {β} (s : Finset β) (f : n -> β -> α) (i : n) : (∑ x in s,
 cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x in s, f j x) i
参数：s : Finset β；f : n -> β -> α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.sum_cramer`：sum_cramer {β} (s : Finset β) (f : β -> n -> α) : (∑ 
x in s, cramer A (f x)) = cramer A (∑ x in s, f x)
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a 
summation.
-/
theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x ∈ s, cramer A (fun j => f j x) i) = cramer A (fun j : n => ∑ x ∈ s, f j x) i :=
  calc
    (∑ x ∈ s, cramer A (fun j => f j x) i) = (∑ x ∈ s, cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = cramer A (fun j : n => ∑ x ∈ s, f j x) i := by
      rw [sum_cramer, cramer_apply]
      congr with j
      apply Finset.sum_apply
/-
**Matrix.cramer_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n -> α) : crame
r (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e
参数：A : Matrix m m α；e : n ≃ m；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.updateCol_submatrix_equiv`：updateCol_submatrix_equiv [DecidableEq
 o] [DecidableEq n] (A : Matrix m n α) (j : o) (c : l -> α) (e : l ≃ m) (f : o ≃
 n) : updateCol (A.sub…
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n → α) :
    cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘ e := by
  ext i
  simp_rw [Function.comp_apply, cramer_apply, updateCol_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp_def]
/-
**Matrix.cramer_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n -> α) : cramer (reind
ex e e A) b = cramer A (b ∘ e) ∘ e.symm
参数：e : m ≃ n；A : Matrix m m α；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.cramer_submatrix_equiv`：cramer_submatrix_equiv (A : Matrix m m α)
 (e : n ≃ m) (b : n -> α) : cramer (A.submatrix e e) b = cramer A (b ∘ e.symm) ∘
 e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n → α) :
    cramer (reindex e e A) b = cramer A (b ∘ e) ∘ e.symm :=
  cramer_submatrix_equiv _ _ _

end Cramer

section Adjugate

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/


/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking minors,
  i.e. the determinant of the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we use the
  matrix replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
/-
**Matrix.adjugate** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：adjugate (A : Matrix n n α) : Matrix n n α
参数：A : Matrix n n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking minors,
  i.e. the determinant of the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we use the
  matrix replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : Matrix n n α) : Matrix n n α :=
  of fun i => cramer Aᵀ (Pi.single i 1)
/-
**Matrix.adjugate_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.s
ingle i 1)
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjugate_def (A : Matrix n n α) : adjugate A = of fun i => cramer Aᵀ (Pi.single i 1) :=
  rfl
/-
**Matrix.adjugate_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_apply (A : Matrix n n α) (i j : n) : adjugate A i j = (A.updateRo
w j (Pi.single i 1)).det
参数：A : Matrix n n α；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_def`：adjugate_def (A : Matrix n n α) : adjugate A = of f
un i => cramer Aᵀ (Pi.single i 1)
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Matrix.updateCol_transpose`：updateCol_transpose [DecidableEq m] : update
Col Mᵀ i b = (updateRow M i b)ᵀ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem adjugate_apply (A : Matrix n n α) (i j : n) :
    adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
  rw [adjugate_def, of_apply, cramer_apply, updateCol_transpose, det_transpose]
/-
**Matrix.adjugate_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `Matrix.adjugate_apply`：adjugate_apply (A : Matrix n n α) (i j : n) : adj
ugate A i j = (A.updateRow j (Pi.single i 1)).det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dite_eq_ite`：∀ {P : Prop} {α : Sort u_1} {a b : α} [inst : Decidable P],
 (if x : P then a else b) = if P then a else b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
（共 33 条，此处仅展示前 30 条）
-/
theorem adjugate_transpose (A : Matrix n n α) : (adjugate A)ᵀ = adjugate Aᵀ := by
  ext i j
  rw [transpose_apply, adjugate_apply, adjugate_apply, updateRow_transpose, det_transpose]
  rw [det_apply', det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases h : i = σ j
  · -- Everything except `(i, j)` (= `(σ j, j)`) is given by A, and the rest is a single `1`.
    congr
    ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [updateRow_apply, updateCol_apply]
    simp_rw [this]
    rw [← dite_eq_ite, ← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateCol A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateCol_self, Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    simp only [Perm.coe_inv, apply_symm_apply, updateRow_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')
/-
**Matrix.IsSymm.adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {n : Type v} {α : Type w} [inst : DecidableEq n] [inst_1 : Fintype n] [i
nst_2 : CommRing α] {A : Matrix n n α},   A.IsSymm → A.adjugate.IsSymm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Matrix.adjugate_transpose`：adjugate_transpose (A : Matrix n n α) : (adju
gate A)ᵀ = adjugate Aᵀ
· 使用定理 `Matrix.IsSymm.eq`：∀ {α : Type u_1} {n : Type u_3} {A : Matrix n n α}, A.
IsSymm → A.transpose = A
-/
theorem IsSymm.adjugate {A : Matrix n n α} (hA : A.IsSymm) : A.adjugate.IsSymm := by
  rw [IsSymm, Matrix.adjugate_transpose, hA.eq]

@[simp]
/-
**Matrix.adjugate_submatrix_equiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) : adjugate (A
.submatrix e e) = (adjugate A).submatrix e e
参数：e : n ≃ m；A : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.update_comp_equiv`：update_comp_equiv [DecidableEq α'] [Decidabl
eEq α] (f : α -> β) (g : α' ≃ α) (a : α) (v : β) : update f a v ∘ g = update (f 
∘ g) (g.symm a) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_apply`：adjugate_apply (A : Matrix n n α) (i j : n) : adj
ugate A i j = (A.updateRow j (Pi.single i 1)).det
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `Matrix.updateRow_submatrix_equiv`：updateRow_submatrix_equiv [DecidableEq
 l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o -> α) (e : l ≃ m) (f : o ≃
 n) : updateRow (A.sub…
-/
theorem adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) :
    adjugate (A.submatrix e e) = (adjugate A).submatrix e e := by
  ext i j
  have : (fun j ↦ Pi.single i 1 <| e.symm j) = Pi.single (e i) 1 :=
    Function.update_comp_equiv (0 : n → α) e.symm i 1
  rw [adjugate_apply, submatrix_apply, adjugate_apply, ← det_submatrix_equiv_self e,
    updateRow_submatrix_equiv, this]
/-
**Matrix.adjugate_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_reindex (e : m ≃ n) (A : Matrix m m α) : adjugate (reindex e e A)
 = reindex e e (adjugate A)
参数：e : m ≃ n；A : Matrix m m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_submatrix_equiv_self`：adjugate_submatrix_equiv_self (e :
 n ≃ m) (A : Matrix m m α) : adjugate (A.submatrix e e) = (adjugate A).submatrix
 e e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem adjugate_reindex (e : m ≃ n) (A : Matrix m m α) :
    adjugate (reindex e e A) = reindex e e (adjugate A) :=
  adjugate_submatrix_equiv_self _ _

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
/-
**Matrix.cramer_eq_adjugate_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n -> α) : cramer A b = A
.adjugate *ᵥ b
参数：A : Matrix n n α；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.adjugate_transpose`：adjugate_transpose (A : Matrix n n α) : (adju
gate A)ᵀ = adjugate Aᵀ
· 使用定理 `Matrix.adjugate_def`：adjugate_def (A : Matrix n n α) : adjugate A = of f
un i => cramer Aᵀ (Pi.single i 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pi_eq_sum_univ`：pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {
R : Type*} [NonAssocSemiring R] (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = 
j th…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by so
me matrix. This
matrix is `A.adjugate`.
-/
theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n → α) :
    cramer A b = A.adjugate *ᵥ b := by
  nth_rw 2 [← A.transpose_transpose]
  rw [← adjugate_transpose, adjugate_def]
  have : b = ∑ i, b i • (Pi.single i 1 : n → α) := by
    refine (pi_eq_sum_univ b).trans ?_
    congr with j
    simp [Pi.single_apply, eq_comm]
  conv_lhs =>
    rw [this]
  ext k
  simp [mulVec, dotProduct, mul_comm]
/-
**Matrix.mul_adjugate_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_adjugate_apply (A : Matrix n n α) (i j k) : A i k * adjugate A k j = c
ramer Aᵀ (Pi.single k (A i k)) j
参数：A : Matrix n n α；i j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Matrix.adjugate.eq_1`：∀ {n : Type v} {α : Type w} [inst : DecidableEq n]
 [inst_1 : Fintype n] [inst_2 : CommRing α] (A : Matrix n n α),   A.adjugate = M
atrix.of f…
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Pi.single_smul'`：single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMul
Action α β] [DecidableEq I] (i : I) (r : α) (x : β) : single (M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
    A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j := by
  rw [← smul_eq_mul, adjugate, of_apply, ← Pi.smul_apply, ← map_smul, ← Pi.single_smul',
    smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.mul_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n
 α)
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.mul_adjugate_apply`：mul_adjugate_apply (A : Matrix n n α) (i j k)
 : A i k * adjugate A k j = cramer Aᵀ (Pi.single k (A i k)) j
· 使用定理 `Matrix.sum_cramer_apply`：sum_cramer_apply {β} (s : Finset β) (f : n -> β
 -> α) (i : n) : (∑ x in s, cramer A (fun j => f j x) i) = cramer A (fun j : n =
> ∑ x in s, f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.cramer_transpose_row_self`：cramer_transpose_row_self (i : n) : Aᵀ
.cramer (A i) = Pi.single i A.det
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n α) := by
  ext i j
  rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]
/-
**Matrix.adjugate_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_mul (A : Matrix n n α) : adjugate A * A = A.det • (1 : Matrix n n
 α)
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.adjugate_transpose`：adjugate_transpose (A : Matrix n n α) : (adju
gate A)ᵀ = adjugate Aᵀ
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
-/
theorem adjugate_mul (A : Matrix n n α) : adjugate A * A = A.det • (1 : Matrix n n α) :=
  calc
    adjugate A * A = (Aᵀ * adjugate Aᵀ)ᵀ := by
      rw [← adjugate_transpose, ← transpose_mul, transpose_transpose]
    _ = _ := by rw [mul_adjugate Aᵀ, det_transpose, transpose_smul, transpose_one]
/-
**Matrix.adjugate_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_smul (r : α) (A : Matrix n n α) : adjugate (r • A) = r ^ (Fintype
.card n - 1) • adjugate A
参数：r : α；A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate.eq_1`：∀ {n : Type v} {α : Type w} [inst : DecidableEq n]
 [inst_1 : Fintype n] [inst_2 : CommRing α] (A : Matrix n n α),   A.adjugate = M
atrix.of f…
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.cramer_smul`：cramer_smul (r : α) (A : Matrix n n α) : cramer (r •
 A) = r ^ (Fintype.card n - 1) • cramer A
-/
theorem adjugate_smul (r : α) (A : Matrix n n α) :
    adjugate (r • A) = r ^ (Fintype.card n - 1) • adjugate A := by
  rw [adjugate, adjugate, transpose_smul, cramer_smul]
  rfl

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A * x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp]
/-
**Matrix.mulVec_cramer** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_cramer (A : Matrix n n α) (b : n -> α) : A *ᵥ cramer A b = A.det • 
b
参数：A : Matrix n n α；b : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cramer_eq_adjugate_mulVec`：cramer_eq_adjugate_mulVec (A : Matrix 
n n α) (b : n -> α) : cramer A b = A.adjugate *ᵥ b
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.smul_mulVec`：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (M : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v

--- 原说明 ---
A stronger form of **Cramer's rule** that allows us to solve some instances of `
A * x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) conditi
on is that `A.det`
divides `b`.
-/
theorem mulVec_cramer (A : Matrix n n α) (b : n → α) : A *ᵥ cramer A b = A.det • b := by
  rw [cramer_eq_adjugate_mulVec, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
/-
**Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理
，位于命名空间 `Matrix`。
形式化陈述：det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors {M : Matrix n n α} {v
 : n -> α} (h : M *ᵥ v = 0) {i : n} (hi : v i in nonZeroDivisors α) : M.det = 0
参数：h : M *ᵥ v = 0；hi : v i in nonZeroDivisors α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`：mul_right_mem_nonZeroDivisors
_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.adjugate_mul`：adjugate_mul (A : Matrix n n α) : adjugate A * A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.smul_mulVec`：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (M : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用定理 `Matrix.mulVec_zero`：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 
= 0
-/
theorem det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors {M : Matrix n n α} {v : n → α}
    (h : M *ᵥ v = 0) {i : n} (hi : v i ∈ nonZeroDivisors α) : M.det = 0 := by
  apply mul_right_mem_nonZeroDivisors_eq_zero_iff hi |>.mp
  simpa [adjugate_mul, smul_mulVec] using congr((M.adjugate *ᵥ $h) i)
/-
**Matrix.adjugate_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate.congr_simp`：∀ {n : Type v} {α : Type w} {inst : Decidabl
eEq n} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [inst_3 : CommRing α]   (A 
A_1 : Matrix n n…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Matrix.adjugate_apply`：adjugate_apply (A : Matrix n n α) (i j : n) : adj
ugate A i j = (A.updateRow j (Pi.single i 1)).det
· 使用定理 `Matrix.det_eq_elem_of_subsingleton`：det_eq_elem_of_subsingleton [Subsing
leton n] (A : Matrix n n R) (k : n) : det A = A k k
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : adjugate A = 1 := by
  ext i j
  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]
/-
**Matrix.adjugate_eq_one_of_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1)
 : adjugate A = 1
参数：h : Fintype.card n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_subsingleton`：adjugate_subsingleton [Subsingleton n] (A 
: Matrix n n α) : adjugate A = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton : car
d α <= 1 ↔ Subsingleton α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    adjugate A = 1 :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  adjugate_subsingleton _

@[simp]
/-
**Matrix.adjugate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Matrix.det_eq_zero_of_column_eq_zero`：det_eq_zero_of_column_eq_zero {A :
 Matrix n n R} (j : n) (h : forall i, A i j = 0) : det A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem adjugate_zero [Nontrivial n] : adjugate (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

@[simp]
/-
**Matrix.adjugate_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_one : adjugate (1 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.cramer_one`：cramer_one : cramer (1 : Matrix n n α) = 1
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjugate_one : adjugate (1 : Matrix n n α) = 1 := by
  ext
  simp [adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]
/-
**Matrix.adjugate_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_diagonal (v : n -> α) : adjugate (diagonal v) = diagonal fun i =>
 ∏ j in Finset.univ.erase i, v j
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_updateCol_single`：diagonal_updateCol_single [DecidableEq
 n] [Zero α] (v : n -> α) (i : n) (x : α) : (diagonal v).updateCol i (Pi.single 
i x) = diagonal (Funct…
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_update_of_mem`：prod_update_of_mem [DecidableEq ι] {s : Finse
t ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) : ∏ x in s, Function.update f i b
 x = b * ∏ x in…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Matrix.det_eq_zero_of_row_eq_zero`：det_eq_zero_of_row_eq_zero {A : Matri
x n n R} (i : n) (h : forall j, A i j = 0) : det A = 0
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
-/
theorem adjugate_diagonal (v : n → α) :
    adjugate (diagonal v) = diagonal fun i => ∏ j ∈ Finset.univ.erase i, v j := by
  ext i j
  simp only [adjugate_def, cramer_apply, diagonal_transpose, of_apply]
  obtain rfl | hij := eq_or_ne i j
  · rw [diagonal_apply_eq, diagonal_updateCol_single, det_diagonal,
      prod_update_of_mem (Finset.mem_univ _), sdiff_singleton_eq_erase, one_mul]
  · rw [diagonal_apply_ne _ hij]
    refine det_eq_zero_of_row_eq_zero j fun k => ?_
    obtain rfl | hjk := eq_or_ne k j
    · rw [updateCol_self, Pi.single_eq_of_ne' hij]
    · rw [updateCol_ne hjk, diagonal_apply_ne' _ hjk]
/-
**Matrix._root_.RingHom.map_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingHom.map_adjugate {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) := by
  ext i k
  have : Pi.single i (1 : S) = f ∘ Pi.single i 1 := by
    rw [← f.map_one]
    exact Pi.single_op (fun _ => f) (fun _ => f.map_zero) i (1 : R)
  rw [adjugate_apply, RingHom.mapMatrix_apply, map_apply, RingHom.mapMatrix_apply, this, ←
    map_updateRow, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← adjugate_apply]
/-
**Matrix._root_.AlgHom.map_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.map_adjugate {R A B : Type*} [CommSemiring R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (M : Matrix n n A) :
    f.mapMatrix M.adjugate = Matrix.adjugate (f.mapMatrix M) :=
  f.toRingHom.map_adjugate _
/-
**Matrix.det_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card
 n - 1)
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.adjugate_subsingleton`：adjugate_subsingleton [Subsingleton n] (A 
: Matrix n n α) : adjugate A = 1
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.nat_succ_le`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `AddMonoidAlgebra.instIsLeftCancelAddZeroOfIsCancelAddOfUniqueSums`：∀ {R 
: Type u_1} {A : Type u_2} [inst : Semiring R] [IsCancelAdd R] [IsLeftCancelMulZ
ero R] [inst_3 : Add A]   [UniqueSums A], IsLeftCancelM…
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instUniqueSumsFinsupp`：∀ {ι : Type u_1} {G : Type u_2} [inst : AddZeroCl
ass G] [UniqueSums G], UniqueSums (ι →₀ G)
· 使用定理 `TwoUniqueSums.toUniqueSums`：∀ (G : Type u_1) [inst : Add G] [TwoUniqueSu
ms G], UniqueSums G
· 使用定理 `TwoUniqueSums.of_covariant_left`：∀ {G : Type u} [inst : Add G] [IsLeftCa
ncelAdd G] [inst_2 : LinearOrder G] [AddRightStrictMono G], TwoUniqueSums G
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
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
（共 44 条，此处仅展示前 30 条）
-/
theorem det_adjugate (A : Matrix n n α) : (adjugate A).det = A.det ^ (Fintype.card n - 1) := by
  -- get rid of the `- 1`
  rcases (Fintype.card n).eq_zero_or_pos with h_card | h_card
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    rw [h_card, Nat.zero_sub, pow_zero, adjugate_subsingleton, det_one]
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_det, ←
      AlgHom.map_det, ← map_pow, this]
  apply mul_left_cancel₀ (show A'.det ≠ 0 from det_mvPolynomialX_ne_zero n ℤ)
  calc
    A'.det * A'.adjugate.det = (A' * adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by rw [mul_adjugate A', det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ', h_card]

@[simp]
/-
**Matrix.adjugate_fin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : adjugate A = 0
参数：A : Matrix (Fin 0) (Fin 0) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : adjugate A = 0 :=
  Subsingleton.elim _ _

@[simp]
/-
**Matrix.adjugate_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : adjugate A = 1
参数：A : Matrix (Fin 1) (Fin 1) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_subsingleton`：adjugate_subsingleton [Subsingleton n] (A 
: Matrix n n α) : adjugate A = 1
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : adjugate A = 1 :=
  adjugate_subsingleton A
/-
**Matrix.adjugate_fin_succ_eq_det_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_succ_eq_det_submatrix {n : Nat} (A : Matrix (Fin n.succ) (Fin
 n.succ) α) (i j) : adjugate A i j = (-1) ^ (j + i : Nat) * det (A.submatrix j.s
uccAbove i.succAbove)
参数：A : Matrix (Fin n.succ) (Fin n.succ) α；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_apply`：adjugate_apply (A : Matrix n n α) (i j : n) : adj
ugate A i j = (A.updateRow j (Pi.single i 1)).det
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_updateRow_succAbove`：submatrix_updateRow_succAbove (A :
 Matrix (Fin m.succ) n' α) (v : n' -> α) (f : o' -> n') (i : Fin m.succ) : (A.up
dateRow i v).submatrix i.s…
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem adjugate_fin_succ_eq_det_submatrix {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) :
    adjugate A i j = (-1) ^ (j + i : ℕ) * det (A.submatrix j.succAbove i.succAbove) := by
  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
  rw [Fintype.sum_eq_single i fun h hjk => ?_, Pi.single_eq_same, mul_one]
  rw [Pi.single_eq_of_ne hjk, mul_zero, zero_mul]
/-
**Matrix.adjugate_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) : adjugate A = !![A 1 1, -
A 0 1; -A 1 0, A 0 0]
参数：A : Matrix (Fin 2) (Fin 2) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_fin_succ_eq_det_submatrix`：adjugate_fin_succ_eq_det_subm
atrix {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) : adjugate A i j 
= (-1) ^ (j + i : Nat) * det (A…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Fin.succAbove_ne_zero_zero`：succAbove_ne_zero_zero [NeZero n] {a : Fin (
n + 1)} (ha : a != 0) : a.succAbove 0 = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 31 条，此处仅展示前 30 条）
-/
theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

@[simp]
/-
**Matrix.adjugate_fin_two_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_two_of (a b c d : α) : adjugate !![a, b; c, d] = !![d, -b; -c
, a]
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_fin_two`：adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α)
 : adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0]
-/
theorem adjugate_fin_two_of (a b c d : α) : adjugate !![a, b; c, d] = !![d, -b; -c, a] :=
  adjugate_fin_two _
/-
**Matrix.adjugate_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) α) : adjugate A = !![A 1 1 
* A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 * A 2 1, A 0 1 * A 1 2 - A 0 2
 * A 1 1; -(A 1 0 * A 2 2) + A 1 2 * A 2 0, A 0 0 * A 2 2 - A 0 2 * A 2 0, -(A 0
 0 * A 1 2) + A 0 2 * A 1 0; A 1 0 * A 2 1 - A 1 1 * A 2 0, -(A 0 0 * A 2 1) + A
 0 1 * A 2 0, A 0 0 * A 1 1 - A 0 1 * A 1 0]
参数：A : Matrix (Fin 3) (Fin 3) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_fin_succ_eq_det_submatrix`：adjugate_fin_succ_eq_det_subm
atrix {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) α) (i j) : adjugate A i j 
= (-1) ^ (j + i : Nat) * det (A…
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 79 条，此处仅展示前 30 条）
-/
theorem adjugate_fin_three (A : Matrix (Fin 3) (Fin 3) α) :
    adjugate A =
    !![A 1 1 * A 2 2 - A 1 2 * A 2 1,
      -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
      -(A 1 0 * A 2 2) + A 1 2 * A 2 0,
      A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
      A 1 0 * A 2 1 - A 1 1 * A 2 0,
      -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0] := by
  ext i j
  rw [adjugate_fin_succ_eq_det_submatrix, det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Fin.succAbove, Fin.lt_def] <;> ring

set_option linter.style.whitespace false in -- Use spaces to format a matrix.
@[simp]
/-
**Matrix.adjugate_fin_three_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_fin_three_of (a b c d e f g h i : α) : adjugate !![a, b, c; d, e,
 f; g, h, i] = !![ e * i - f * h, -(b * i) + c * h, b * f - c * e; -(d * i) + f 
* g, a * i - c * g, -(a * f) + c * d; d * h - e * g, -(a * h) + b * g, a * e - b
 * d]
参数：a b c d e f g h i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_fin_three`：adjugate_fin_three (A : Matrix (Fin 3) (Fin 3
) α) : adjugate A = !![A 1 1 * A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 *
 A 2 1, A 0 1 *…
-/
theorem adjugate_fin_three_of (a b c d e f g h i : α) :
    adjugate !![a, b, c; d, e, f; g, h, i] =
      !![  e * i  - f * h, -(b * i) + c * h,   b * f  - c * e;
         -(d * i) + f * g,   a * i  - c * g, -(a * f) + c * d;
           d * h  - e * g, -(a * h) + b * g,   a * e  - b * d] :=
  adjugate_fin_three _
/-
**Matrix.det_eq_sum_mul_adjugate_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) : det A = ∑ j : n, 
A i j * adjugate A j i
参数：A : Matrix n n α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.adjugate.congr_simp`：∀ {n : Type v} {α : Type w} {inst : Decidabl
eEq n} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [inst_3 : CommRing α]   (A 
A_1 : Matrix n n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Matrix.adjugate_reindex`：adjugate_reindex (e : m ≃ n) (A : Matrix m m α)
 : adjugate (reindex e e A) = reindex e e (adjugate A)
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
-/
theorem det_eq_sum_mul_adjugate_row (A : Matrix n n α) (i : n) :
    det A = ∑ j : n, A i j * adjugate A j i := by
  have : Nonempty n := ⟨i⟩
  obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hn'
  let A' := reindex e e A
  suffices det A' = ∑ j : Fin n'.succ, A' (e i) j * adjugate A' j (e i) by
    simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ← e.sum_comp,
      Equiv.symm_apply_apply] at this
    exact this
  rw [det_succ_row A' (e i)]
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ← adjugate_fin_succ_eq_det_submatrix]
/-
**Matrix.det_eq_sum_mul_adjugate_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) : det A = ∑ i : n, 
A i j * adjugate A j i
参数：A : Matrix n n α；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.det_eq_sum_mul_adjugate_row`：det_eq_sum_mul_adjugate_row (A : Mat
rix n n α) (i : n) : det A = ∑ j : n, A i j * adjugate A j i
-/
theorem det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) :
    det A = ∑ i : n, A i j * adjugate A j i := by
  simpa only [det_transpose, ← adjugate_transpose] using! det_eq_sum_mul_adjugate_row Aᵀ j
/-
**Matrix.adjugate_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adj
ugate Aᴴ
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_adjugate`：∀ {n : Type v} [inst : DecidableEq n] [inst_1 : Fi
ntype n] {R : Type u_1} {S : Type u_2} [inst_2 : CommRing R]   [inst_3 : CommRin
g S] (f : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_transpose`：adjugate_transpose (A : Matrix n n α) : (adju
gate A)ᵀ = adjugate Aᵀ
-/
theorem adjugate_conjTranspose [StarRing α] (A : Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ := by
  dsimp only [conjTranspose]
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) := (starRingEnd α).map_adjugate Aᵀ
  rw [A.adjugate_transpose, this]
/-
**Matrix.isRegular_of_isLeftRegular_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.de
t) : IsRegular A
参数：hA : IsLeftRegular A.det。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.matrix`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst
 : Mul α] {k : α}, IsLeftRegular k → IsSMulRegular (Matrix m n α) k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.adjugate_mul`：adjugate_mul (A : Matrix n n α) : adjugate A * A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
-/
theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by
  constructor
  · intro B C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B, ← Matrix.one_mul C, ← Matrix.smul_mul, ← Matrix.smul_mul, ←
      adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro B C (h : B * A = C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B, ← Matrix.mul_one C, ← Matrix.mul_smul, ← Matrix.mul_smul, ←
      mul_adjugate, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
/-
**Matrix.adjugate_mul_distrib_aux** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det) (
hB : IsLeftRegular B.det) : adjugate (A * B) = adjugate B * adjugate A
参数：A B : Matrix n n α；hA : IsLeftRegular A.det；hB : IsLeftRegular B.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `IsLeftRegular.mul`：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLe
ftRegular b) : IsLeftRegular (a * b)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Matrix.isRegular_of_isLeftRegular_det`：isRegular_of_isLeftRegular_det {A
 : Matrix n n α} (hA : IsLeftRegular A.det) : IsRegular A
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem adjugate_mul_distrib_aux (A B : Matrix n n α) (hA : IsLeftRegular A.det)
    (hB : IsLeftRegular B.det) : adjugate (A * B) = adjugate B * adjugate A := by
  have hAB : IsLeftRegular (A * B).det := by
    rw [det_mul]
    exact hA.mul hB
  refine (isRegular_of_isLeftRegular_det hAB).left ?_
  simp only
  rw [mul_adjugate, Matrix.mul_assoc, ← Matrix.mul_assoc B, mul_adjugate,
    smul_mul, Matrix.one_mul, Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm, ← det_mul]

/-- Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
/-
**Matrix.adjugate_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A * B) = adjugate B 
* adjugate A
参数：A B : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.map_adjugate`：∀ {n : Type v} [inst : DecidableEq n] [inst_1 : Fi
ntype n] {R : Type u_1} {S : Type u_2} [inst_2 : CommRing R]   [inst_3 : CommRin
g S] (f : …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.Monic.isRegular`：∀ {R : Type u_1} [inst : Ring R] {p : Polyno
mial R}, p.Monic → IsRegular p
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_det_X_one_add_C`：leadingCoeff_det_X_one_add_C (A
 : Matrix n n α) : leadingCoeff (det ((X : α[X]) • (1 : Matrix n n α[X]) + A.map
 C)) = 1
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Matrix.adjugate_mul_distrib_aux`：adjugate_mul_distrib_aux (A B : Matrix 
n n α) (hA : IsLeftRegular A.det) (hB : IsLeftRegular B.det) : adjugate (A * B) 
= adjugate B * adjuga…
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c

--- 原说明 ---
Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Sectio
n 5.3
-/
theorem adjugate_mul_distrib (A B : Matrix n n α) : adjugate (A * B) = adjugate B * adjugate A := by
  let g : Matrix n n α → Matrix n n α[X] := fun M =>
    M.map Polynomial.C + (Polynomial.X : α[X]) • (1 : Matrix n n α[X])
  let f' : Matrix n n α[X] →+* Matrix n n α := (Polynomial.evalRingHom 0).mapMatrix
  have f'_inv : ∀ M, f' (g M) = M := by
    intro
    ext
    simp [f', g]
  have f'_adj : ∀ M : Matrix n n α, f' (adjugate (g M)) = adjugate M := by
    intro
    rw [RingHom.map_adjugate, f'_inv]
  have f'_g_mul : ∀ M N : Matrix n n α, f' (g M * g N) = M * N := by
    intro M N
    rw [map_mul, f'_inv, f'_inv]
  have hu : ∀ M : Matrix n n α, IsRegular (g M).det := by
    intro M
    refine Polynomial.Monic.isRegular ?_
    simp only [g, Polynomial.Monic.def, ← Polynomial.leadingCoeff_det_X_one_add_C M, add_comm]
  rw [← f'_adj, ← f'_adj, ← f'_adj, ← f'.map_mul, ←
    adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left, RingHom.map_adjugate,
    RingHom.map_adjugate, f'_inv, f'_g_mul]

@[simp]
/-
**Matrix.adjugate_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_pow (A : Matrix n n α) (k : Nat) : adjugate (A ^ k) = adjugate A 
^ k
参数：A : Matrix n n α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.adjugate_one`：adjugate_one : adjugate (1 : Matrix n n α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Matrix.adjugate_mul_distrib`：adjugate_mul_distrib (A B : Matrix n n α) :
 adjugate (A * B) = adjugate B * adjugate A
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : adjugate (A ^ k) = adjugate A ^ k := by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', adjugate_mul_distrib, IH, pow_succ]
/-
**Matrix.det_smul_adjugate_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_smul_adjugate_adjugate (A : Matrix n n α) : det A • adjugate (adjugate
 A) = det A ^ (Fintype.card n - 1) • A
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.adjugate_mul_distrib`：adjugate_mul_distrib (A B : Matrix n n α) :
 adjugate (A * B) = adjugate B * adjugate A
· 使用定理 `Matrix.adjugate_mul`：adjugate_mul (A : Matrix n n α) : adjugate A * A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.adjugate_smul`：adjugate_smul (r : α) (A : Matrix n n α) : adjugat
e (r • A) = r ^ (Fintype.card n - 1) • adjugate A
· 使用定理 `Matrix.adjugate_one`：adjugate_one : adjugate (1 : Matrix n n α) = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.mul_adjugate`：mul_adjugate (A : Matrix n n α) : A * adjugate A = 
A.det • (1 : Matrix n n α)
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
-/
theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • adjugate (adjugate A) = det A ^ (Fintype.card n - 1) • A := by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← adjugate_mul_distrib, adjugate_mul, adjugate_smul, adjugate_one]
  rwa [← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this

/-- Note that this is not true for `Fintype.card n = 1` since `1 - 2 = 0` and not `-1`. -/
/-
**Matrix.adjugate_adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n != 1) : adjugate 
(adjugate A) = det A ^ (Fintype.card n - 2) • A
参数：A : Matrix n n α；h : Fintype.card n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Simproc.add_sub_le`：∀ (a : ℕ) {b c : ℕ}, b ≤ c → a + b - c = a - (c 
- b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `AddMonoidAlgebra.instIsLeftCancelAddZeroOfIsCancelAddOfUniqueSums`：∀ {R 
: Type u_1} {A : Type u_2} [inst : Semiring R] [IsCancelAdd R] [IsLeftCancelMulZ
ero R] [inst_3 : Add A]   [UniqueSums A], IsLeftCancelM…
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instUniqueSumsFinsupp`：∀ {ι : Type u_1} {G : Type u_2} [inst : AddZeroCl
ass G] [UniqueSums G], UniqueSums (ι →₀ G)
· 使用定理 `TwoUniqueSums.toUniqueSums`：∀ (G : Type u_1) [inst : Add G] [TwoUniqueSu
ms G], UniqueSums G
· 使用定理 `TwoUniqueSums.of_covariant_left`：∀ {G : Type u} [inst : Add G] [IsLeftCa
ncelAdd G] [inst_2 : LinearOrder G] [AddRightStrictMono G], TwoUniqueSums G
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Note that this is not true for `Fintype.card n = 1` since `1 - 2 = 0` and not `-
1`.
-/
theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n ≠ 1) :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A := by
  -- get rid of the `- 2`
  rcases h_card : Fintype.card n with _ | n'
  · subsingleton [Fintype.card_eq_zero_iff.mp h_card]
  cases n'
  · exact (h h_card).elim
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  suffices adjugate (adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_adjugate, this,
      ← AlgHom.map_det, ← map_pow (MvPolynomial.aeval fun p : n × n ↦ A p.1 p.2),
      AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  have is_reg : IsSMulRegular (MvPolynomial (n × n) ℤ) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ)
  apply is_reg.matrix
  simp only
  rw [smul_smul, ← pow_succ', h_card', det_smul_adjugate_adjugate]

/-- A weaker version of `Matrix.adjugate_adjugate` that uses `Nontrivial`. -/
/-
**Matrix.adjugate_adjugate'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] : adjugate (adjugate 
A) = det A ^ (Fintype.card n - 2) • A
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.adjugate_adjugate`：adjugate_adjugate (A : Matrix n n α) (h : Fint
ype.card n != 1) : adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α

--- 原说明 ---
A weaker version of `Matrix.adjugate_adjugate` that uses `Nontrivial`.
-/
theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    adjugate (adjugate A) = det A ^ (Fintype.card n - 2) • A :=
  adjugate_adjugate _ <| Fintype.one_lt_card.ne'

end Adjugate

end Matrix

