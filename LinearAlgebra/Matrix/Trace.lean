/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Trace of a matrix

This file defines the trace of a matrix, the map sending a matrix to the sum of its diagonal
entries.

See also `LinearAlgebra.Trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/

@[expose] public section


open Matrix

namespace Matrix

variable {ι m n p : Type*} {α R S : Type*}
variable [Fintype m] [Fintype n] [Fintype p]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The trace of a square matrix. For more bundled versions, see:
* `Matrix.traceAddMonoidHom`
* `Matrix.traceLinearMap`
-/
/-
**Matrix.trace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：trace (A : Matrix n n R) : R
参数：A : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trace of a square matrix. For more bundled versions, see:
* `Matrix.traceAddMonoidHom`
* `Matrix.traceLinearMap`
-/
def trace (A : Matrix n n R) : R :=
  ∑ i, diag A i
/-
**Matrix.trace_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_6} [inst : AddCommMonoid R] {o : Type u_8} [inst_1 : Fintype
 o] [inst_2 : DecidableEq o] (d : o → R),   (Matrix.diagonal d).trace = ∑ i, d i
参数：d : o → R；Matrix.diagonal d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma trace_diagonal {o} [Fintype o] [DecidableEq o] (d : o → R) :
    trace (diagonal d) = ∑ i, d i := by
  simp only [trace, diag_apply, diagonal_apply_eq]

variable (n R)

@[simp]
/-
**Matrix.trace_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_zero : trace (0 : Matrix n n R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem trace_zero : trace (0 : Matrix n n R) = 0 :=
  (Finset.sum_const (0 : R)).trans <| smul_zero _

variable {n R}

@[simp]
/-
**Matrix.trace_eq_zero_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：trace_eq_zero_of_isEmpty [IsEmpty n] (A : Matrix n n R) : trace A = 0
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_eq_zero_of_isEmpty [IsEmpty n] (A : Matrix n n R) : trace A = 0 := by simp [trace]

@[simp]
/-
**Matrix.trace_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B
参数：A B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
-/
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B :=
  Finset.sum_add_distrib

@[simp]
/-
**Matrix.trace_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) : trace (r • A) = 
r • trace A
参数：r : α；A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
-/
theorem trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) :
    trace (r • A) = r • trace A :=
  Finset.smul_sum.symm

@[simp]
/-
**Matrix.trace_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trace_transpose (A : Matrix n n R) : trace Aᵀ = trace A :=
  rfl

@[simp]
/-
**Matrix.trace_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star
 (trace A)
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
-/
theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : trace Aᴴ = star (trace A) :=
  (star_sum _ _).symm

variable (n α R)

/-- `Matrix.trace` as an `AddMonoidHom` -/
@[simps]
/-
**Matrix.traceAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：traceAddMonoidHom : Matrix n n R ->+ R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_zero`：trace_zero : trace (0 : Matrix n n R) = 0
· 使用定理 `Matrix.trace_add`：trace_add (A B : Matrix n n R) : trace (A + B) = trace
 A + trace B

--- 原说明 ---
`Matrix.trace` as an `AddMonoidHom`
-/
def traceAddMonoidHom : Matrix n n R →+ R where
  toFun := trace
  map_zero' := trace_zero n R
  map_add' := trace_add

/-- `Matrix.trace` as a `LinearMap` -/
@[simps]
/-
**Matrix.traceLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：traceLinearMap [Semiring α] [Module α R] : Matrix n n R ->ₗ[α] R where toF
un
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_add`：trace_add (A B : Matrix n n R) : trace (A + B) = trace
 A + trace B

--- 原说明 ---
`Matrix.trace` as a `LinearMap`
-/
def traceLinearMap [Semiring α] [Module α R] : Matrix n n R →ₗ[α] R where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

variable {n α R}

@[simp]
/-
**Matrix.trace_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_list_sum (l : List (Matrix n n R)) : trace l.sum = (l.map trace).sum
参数：l : List (Matrix n n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem trace_list_sum (l : List (Matrix n n R)) : trace l.sum = (l.map trace).sum :=
  map_list_sum (traceAddMonoidHom n R) l

@[simp]
/-
**Matrix.trace_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.sum = (s.map tr
ace).sum
参数：s : Multiset (Matrix n n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : trace s.sum = (s.map trace).sum :=
  map_multiset_sum (traceAddMonoidHom n R) s

@[simp]
/-
**Matrix.trace_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_sum (s : Finset ι) (f : ι -> Matrix n n R) : trace (∑ i in s, f i) =
 ∑ i in s, trace (f i)
参数：s : Finset ι；f : ι -> Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem trace_sum (s : Finset ι) (f : ι → Matrix n n R) :
    trace (∑ i ∈ s, f i) = ∑ i ∈ s, trace (f i) :=
  map_sum (traceAddMonoidHom n R) f s
/-
**Matrix._root_.AddMonoidHom.map_trace** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoidHom.map_trace [AddCommMonoid S] {F : Type*} [FunLike F R S]
    [AddMonoidHomClass F R S] (f : F) (A : Matrix n n R) :
    f (trace A) = trace (A.map f) :=
  map_sum f (fun i => diag A i) Finset.univ
/-
**Matrix.trace_blockDiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：trace_blockDiagonal [DecidableEq p] (M : p -> Matrix n n R) : trace (block
Diagonal M) = ∑ i, trace (M i)
参数：M : p -> Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.sum_prod_type`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5} 
[inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ ×
 α₂ → γ), ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
lemma trace_blockDiagonal [DecidableEq p] (M : p → Matrix n n R) :
    trace (blockDiagonal M) = ∑ i, trace (M i) := by
  simp [blockDiagonal, trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]
/-
**Matrix.trace_blockDiagonal'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：trace_blockDiagonal' [DecidableEq p] {m : p -> Type*} [forall i, Fintype (
m i)] (M : forall i, Matrix (m i) (m i) R) : trace (blockDiagonal' M) = ∑ i, tra
ce (M i)
参数：m i；M : forall i, Matrix (m i) (m i) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
-/
lemma trace_blockDiagonal' [DecidableEq p] {m : p → Type*} [∀ i, Fintype (m i)]
    (M : ∀ i, Matrix (m i) (m i) R) :
    trace (blockDiagonal' M) = ∑ i, trace (M i) := by
  simp [blockDiagonal', trace, Finset.sum_sigma']

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R]

@[simp]
/-
**Matrix.trace_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B
参数：A B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
-/
theorem trace_sub (A B : Matrix n n R) : trace (A - B) = trace A - trace B :=
  Finset.sum_sub_distrib ..

@[simp]
/-
**Matrix.trace_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_neg (A : Matrix n n R) : trace (-A) = -trace A
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
-/
theorem trace_neg (A : Matrix n n R) : trace (-A) = -trace A :=
  Finset.sum_neg_distrib ..

end AddCommGroup

section One

variable [DecidableEq n] [AddCommMonoidWithOne R]

@[simp]
/-
**Matrix.trace_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_one : trace (1 : Matrix n n R) = Fintype.card n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.diag_one`：diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : M
atrix n n α) = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

end One

section Mul

@[simp]
/-
**Matrix.trace_transpose_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_transpose_mul [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matr
ix n m R) : trace (Aᵀ * Bᵀ) = trace (A * B)
参数：A : Matrix m n R；B : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem trace_transpose_mul [AddCommMonoid R] [Mul R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (Aᵀ * Bᵀ) = trace (A * B) :=
  Finset.sum_comm
/-
**Matrix.trace_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Mat
rix n m R) : trace (A * B) = trace (B * A)
参数：A : Matrix m n R；B : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.trace_transpose`：trace_transpose (A : Matrix n n R) : trace Aᵀ = 
trace A
· 使用定理 `Matrix.trace_transpose_mul`：trace_transpose_mul [AddCommMonoid R] [Mul R
] (A : Matrix m n R) (B : Matrix n m R) : trace (Aᵀ * Bᵀ) = trace (A * B)
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
-/
theorem trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = trace (B * A) := by rw [← trace_transpose, ← trace_transpose_mul, transpose_mul]
/-
**Matrix.trace_mul_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n
 p R) (C : Matrix p m R) : trace (A * B * C) = trace (C * A * B)
参数：A : Matrix m n R；B : Matrix n p R；C : Matrix p m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.trace_mul_comm`：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A
 : Matrix m n R) (B : Matrix n m R) : trace (A * B) = trace (B * A)
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
-/
theorem trace_mul_cycle [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * B * C) = trace (C * A * B) := by
  rw [trace_mul_comm, Matrix.mul_assoc]
/-
**Matrix.trace_mul_cycle'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix 
n p R) (C : Matrix p m R) : trace (A * (B * C)) = trace (C * (A * B))
参数：A : Matrix m n R；B : Matrix n p R；C : Matrix p m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.trace_mul_comm`：trace_mul_comm [AddCommMonoid R] [CommMagma R] (A
 : Matrix m n R) (B : Matrix n m R) : trace (A * B) = trace (B * A)
-/
theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : trace (A * (B * C)) = trace (C * (A * B)) := by
  rw [← Matrix.mul_assoc, trace_mul_comm]

@[simp]
/-
**Matrix.trace_replicateCol_mul_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] [NonUnitalNonAs
socSemiring R] (a b : n -> R) : trace (replicateCol ι a * replicateRow ι b) = a 
⬝ᵥ b
参数：a b : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem trace_replicateCol_mul_replicateRow {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R]
    (a b : n → R) : trace (replicateCol ι a * replicateRow ι b) = a ⬝ᵥ b := by
  apply Finset.sum_congr rfl
  simp [mul_apply]

@[simp]
/-
**Matrix.trace_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_vecMulVec [NonUnitalNonAssocSemiring R] (a b : n -> R) : trace (vecM
ulVec a b) = a ⬝ᵥ b
参数：a b : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v
· 使用定理 `Matrix.trace_replicateCol_mul_replicateRow`：trace_replicateCol_mul_repli
cateRow {ι : Type*} [Unique ι] [NonUnitalNonAssocSemiring R] (a b : n -> R) : tr
ace (replicateCol ι a * replicat…
-/
theorem trace_vecMulVec [NonUnitalNonAssocSemiring R] (a b : n → R) :
    trace (vecMulVec a b) = a ⬝ᵥ b := by
  rw [vecMulVec_eq Unit, trace_replicateCol_mul_replicateRow]

end Mul

/-
**Matrix.trace_submatrix_succ** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：trace_submatrix_succ {n : Nat} [AddCommMonoid R] (M : Matrix (Fin n.succ) 
(Fin n.succ) R) : M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M
参数：M : Matrix (Fin n.succ) (Fin n.succ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `finSuccEquiv_symm_some`：finSuccEquiv_symm_some (m : Fin n) : (finSuccEqu
iv n).symm (some m) = m.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trace_submatrix_succ {n : ℕ} [AddCommMonoid R]
    (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + trace (submatrix M Fin.succ Fin.succ) = trace M := by
  delta trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

section CommSemiring

variable [DecidableEq m] [CommSemiring R]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
/-
**Matrix.trace_units_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) : trace ((M : Ma
trix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N
参数：M : (Matrix m m R)ˣ；N : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.trace_mul_cycle`：trace_mul_cycle [NonUnitalCommSemiring R] (A : M
atrix m n R) (B : Matrix n p R) (C : Matrix p m R) : trace (A * B * C) = trace (
C * A * B)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem trace_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N := by
  rw [trace_mul_cycle, Units.inv_mul, one_mul]

set_option linter.docPrime false in
-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so that the ascription isn't needed
/-
**Matrix.trace_units_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) : trace ((↑M⁻¹ 
: Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N
参数：M : (Matrix m m R)ˣ；N : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_units_conj`：trace_units_conj (M : (Matrix m m R)ˣ) (N : Mat
rix m m R) : trace ((M : Matrix _ _ _) * N * (↑M⁻¹ : Matrix _ _ _)) = trace N
-/
theorem trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N :=
  trace_units_conj M⁻¹ N

end CommSemiring

section Fin

variable [AddCommMonoid R]

/-! ### Special cases for `Fin n` for low values of `n`
-/

@[simp]
/-
**Matrix.trace_fin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : trace A = 0
参数：A : Matrix (Fin 0) (Fin 0) R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Special cases for `Fin n` for low values of `n`
-/
theorem trace_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : trace A = 0 :=
  rfl
/-
**Matrix.trace_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : trace A = A 0 0
参数：A : Matrix (Fin 1) (Fin 1) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
-/
theorem trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : trace A = A 0 0 :=
  add_zero _
/-
**Matrix.trace_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1
参数：A : Matrix (Fin 2) (Fin 2) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : trace A = A 0 0 + A 1 1 :=
  congr_arg (_ + ·) (add_zero (A 1 1))
/-
**Matrix.trace_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : trace A = A 0 0 + A 1 1 +
 A 2 2
参数：A : Matrix (Fin 3) (Fin 3) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) : trace A = A 0 0 + A 1 1 + A 2 2 := by
  rw [← add_zero (A 2 2), add_assoc]
  rfl

@[simp]
/-
**Matrix.trace_fin_one_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_one_of (a : R) : trace !![a] = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_fin_one`：trace_fin_one (A : Matrix (Fin 1) (Fin 1) R) : tra
ce A = A 0 0
-/
theorem trace_fin_one_of (a : R) : trace !![a] = a :=
  trace_fin_one _

@[simp]
/-
**Matrix.trace_fin_two_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d
参数：a b c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
-/
theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d :=
  trace_fin_two _

@[simp]
/-
**Matrix.trace_fin_three_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_fin_three_of (a b c d e f g h i : R) : trace !![a, b, c; d, e, f; g,
 h, i] = a + e + i
参数：a b c d e f g h i : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_fin_three`：trace_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
 trace A = A 0 0 + A 1 1 + A 2 2
-/
theorem trace_fin_three_of (a b c d e f g h i : R) :
    trace !![a, b, c; d, e, f; g, h, i] = a + e + i :=
  trace_fin_three _

end Fin

section single

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]
variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

@[simp]
/-
**Matrix.trace_single_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_single_eq_of_ne (h : i != j) : trace (single i j c) = 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.diag_single_of_ne`：diag_single_of_ne (h : i != j) : diag (single 
i j c) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_single_eq_of_ne (h : i ≠ j) : trace (single i j c) = 0 := by
  simp [trace, h]

@[simp]
/-
**Matrix.trace_single_eq_same** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_single_eq_same : trace (single i i c) = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.diag_single_same`：diag_single_same : diag (single i i c) = Pi.sin
gle i c
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_single_eq_same : trace (single i i c) = c := by
  simp [trace]
/-
**Matrix.trace_single_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_single_mul [NonUnitalNonAssocSemiring R] [Fintype m] (i : n) (j : m)
 (a : R) (x : Matrix m n R) : (single i j a * x).trace = a • x j i
参数：i : n；j : m；a : R；x : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι) (f g : ι → M),   (∑ x ∈ 
s, if p th…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_single_mul [NonUnitalNonAssocSemiring R] [Fintype m]
    (i : n) (j : m) (a : R) (x : Matrix m n R) :
    (single i j a * x).trace = a • x j i := by
  simp [trace, mul_apply, single, ite_and]
/-
**Matrix.trace_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_mul_single [NonUnitalNonAssocSemiring R] [Fintype m] (x : Matrix m n
 R) (i : n) (j : m) (a : R) : (x * single i j a).trace = MulOpposite.op a • x j 
i
参数：x : Matrix m n R；i : n；j : m；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_mul_single [NonUnitalNonAssocSemiring R] [Fintype m]
    (x : Matrix m n R) (i : n) (j : m) (a : R) :
    (x * single i j a).trace = MulOpposite.op a • x j i := by
  simp [trace, mul_apply, single, ite_and]

end single

/-
**Matrix.trace_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：trace_surjective [AddCommMonoid R] [Nonempty n] : Function.Surjective (tra
ce : Matrix n n R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.trace_single_eq_same`：trace_single_eq_same : trace (single i i c)
 = c
-/
theorem trace_surjective [AddCommMonoid R] [Nonempty n] :
    Function.Surjective (trace : Matrix n n R → R) := fun r ↦ by
  classical
  inhabit n
  exact ⟨single default default r, trace_single_eq_same default r⟩

/-- Matrices `A` and `B` are equal iff `(x * A).trace = (x * B).trace` for all `x`. -/
/-
**Matrix.ext_iff_trace_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_trace_mul_left [NonAssocSemiring R] {A B : Matrix m n R} : A = B ↔
 forall x, (x * A).trace = (x * B).trace
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.trace_single_mul`：trace_single_mul [NonUnitalNonAssocSemiring R] 
[Fintype m] (i : n) (j : m) (a : R) (x : Matrix m n R) : (single i j a * x).trac
e = a • x j i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Matrices `A` and `B` are equal iff `(x * A).trace = (x * B).trace` for all `x`.
-/
theorem ext_iff_trace_mul_left [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ ∀ x, (x * A).trace = (x * B).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_single_mul] using h (single j i (1 : R))

/-- Matrices `A` and `B` are equal iff `(A * x).trace = (B * x).trace` for all `x`. -/
/-
**Matrix.ext_iff_trace_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_trace_mul_right [NonAssocSemiring R] {A B : Matrix m n R} : A = B 
↔ forall x, (A * x).trace = (B * x).trace
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.trace_mul_single`：trace_mul_single [NonUnitalNonAssocSemiring R] 
[Fintype m] (x : Matrix m n R) (i : n) (j : m) (a : R) : (x * single i j a).trac
e = MulOpposi…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Matrices `A` and `B` are equal iff `(A * x).trace = (B * x).trace` for all `x`.
-/
theorem ext_iff_trace_mul_right [NonAssocSemiring R] {A B : Matrix m n R} :
    A = B ↔ ∀ x, (A * x).trace = (B * x).trace := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext i j
  classical
  simpa [trace_mul_single] using h (single j i (1 : R))

end Matrix

