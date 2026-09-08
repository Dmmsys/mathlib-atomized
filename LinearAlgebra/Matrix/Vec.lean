/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Vectorization of matrices

This file defines `Matrix.vec A`, the vectorization of a matrix `A`,
formed by stacking the columns of A into a single large column vector.

Since mathlib indices matrices by arbitrary types rather than `Fin n`,
the result of `Matrix.vec` on `A : Matrix m n R` is indexed by `n × m`.
The `Fin (n * m)` interpretation can be restored by composing with `finProdFinEquiv.symm`:
```lean
-- ![1, 2, 3, 4]
#eval vec !![1, 3; 2, 4] ∘ finProdFinEquiv.symm
```

While it may seem more natural to index by `m × n`, keeping the indices in the same order,
this would amount to stacking the rows into one long row, and goes against the literature.
If you want this function, you can write `Matrix.vec Aᵀ` instead.

### References

* [Wikipedia](https://en.wikipedia.org/wiki/Vectorization_(mathematics))
-/

@[expose] public section
namespace Matrix

variable {ι l m n p R S}

/-- All the matrix entries, arranged into one column. -/
@[simp]
/-
**Matrix.vec** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vec (A : Matrix m n R) : n × m -> R
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All the matrix entries, arranged into one column.
-/
def vec (A : Matrix m n R) : n × m → R :=
  fun ij => A ij.2 ij.1

@[simp]
/-
**Matrix.vec_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_of (f : m -> n -> R) : vec (of f) = Function.uncurry (flip f)
参数：f : m -> n -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_of (f : m → n → R) : vec (of f) = Function.uncurry (flip f) := rfl
/-
**Matrix.vec_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_transpose (A : Matrix m n R) : vec Aᵀ = vec A ∘ Prod.swap
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_transpose (A : Matrix m n R) : vec Aᵀ = vec A ∘ Prod.swap := rfl
/-
**Matrix.vec_eq_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_eq_uncurry (A : Matrix m n R) : vec A = Function.uncurry fun i j => A 
j i
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_eq_uncurry (A : Matrix m n R) : vec A = Function.uncurry fun i j => A j i := rfl
/-
**Matrix.vec_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B := by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]
/-
**Matrix.vec_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_bijective : Function.Bijective (vec : Matrix m n R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.swap_bijective`：∀ {α : Sort u_1} {β : Sort u_2} {γ : α → β → So
rt u_3}, Function.Bijective Function.swap
-/
theorem vec_bijective : Function.Bijective (vec : Matrix m n R → _) :=
  Equiv.curry _ _ _ |>.symm.bijective.comp Function.swap_bijective
/-
**Matrix.vec_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_map (A : Matrix m n R) (f : R -> S) : vec (A.map f) = f ∘ vec A
参数：A : Matrix m n R；f : R -> S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_map (A : Matrix m n R) (f : R → S) : vec (A.map f) = f ∘ vec A := rfl

@[simp]
/-
**Matrix.vec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_zero [Zero R] : vec (0 : Matrix m n R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_zero [Zero R] : vec (0 : Matrix m n R) = 0 :=
  rfl

@[simp]
/-
**Matrix.vec_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_eq_zero_iff [Zero R] {A : Matrix m n R} : vec A = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vec_inj`：vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B
-/
theorem vec_eq_zero_iff [Zero R] {A : Matrix m n R} : vec A = 0 ↔ A = 0 := vec_inj (B := 0)

@[simp]
/-
**Matrix.vec_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_add [Add R] (A B : Matrix m n R) : vec (A + B) = vec A + vec B
参数：A B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_add [Add R] (A B : Matrix m n R) : vec (A + B) = vec A + vec B :=
  rfl
/-
**Matrix.vec_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_neg [Neg R] (A : Matrix m n R) : vec (-A) = -vec A
参数：A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_neg [Neg R] (A : Matrix m n R) : vec (-A) = -vec A :=
  rfl

@[simp]
/-
**Matrix.vec_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_sub [Sub R] (A B : Matrix m n R) : vec (A - B) = vec A - vec B
参数：A B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_sub [Sub R] (A B : Matrix m n R) : vec (A - B) = vec A - vec B :=
  rfl

@[simp]
/-
**Matrix.vec_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : vec (r • A) = r • vec
 A
参数：r : α；A : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : vec (r • A) = r • vec A :=
  rfl
/-
**Matrix.vec_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_sum [AddCommMonoid R] (s : Finset ι) (A : ι -> Matrix m n R) : vec (∑ 
i in s, A i) = ∑ i in s, vec (A i)
参数：s : Finset ι；A : ι -> Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec_sum [AddCommMonoid R] (s : Finset ι) (A : ι → Matrix m n R) :
    vec (∑ i ∈ s, A i) = ∑ i ∈ s, vec (A i) := by
  ext
  simp_rw [vec, Finset.sum_apply, vec, Matrix.sum_apply]
/-
**Matrix.vec_dotProduct_vec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Fintype m] [Fintype n] (A B 
: Matrix m n R) : vec A ⬝ᵥ vec B = (Aᵀ * B).trace
参数：A B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    vec A ⬝ᵥ vec B = (Aᵀ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]
/-
**Matrix.star_vec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_vec [Star R] (x : Matrix m n R) : star x.vec = (x.map star).vec
参数：x : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_vec [Star R] (x : Matrix m n R) :
    star x.vec = (x.map star).vec :=
  rfl
/-
**Matrix.star_vec_dotProduct_vec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Star R] [Fintype m] [Fi
ntype n] (A B : Matrix m n R) : star (vec A) ⬝ᵥ vec B = (Aᴴ * B).trace
参数：A B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vec_dotProduct_vec`：vec_dotProduct_vec [AddCommMonoid R] [Mul R] 
[Fintype m] [Fintype n] (A B : Matrix m n R) : vec A ⬝ᵥ vec B = (Aᵀ * B).trace
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Star R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    star (vec A) ⬝ᵥ vec B = (Aᴴ * B).trace := by
  simp_rw [star_vec, vec_dotProduct_vec, ← conjTranspose_transpose, transpose_transpose]
/-
**Matrix.vec_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_hadamard [Mul R] (A B : Matrix m n R) : vec (A ⊙ B) = vec A * vec B
参数：A B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vec_hadamard [Mul R] (A B : Matrix m n R) : vec (A ⊙ B) = vec A * vec B := rfl

@[simp]
/-
**Matrix.vec_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_single [DecidableEq m] [DecidableEq n] [Zero R] (i : m) (j : n) (r : R
) : vec (Matrix.single i j r) = Pi.single (j, i) r
参数：i : m；j : n；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
· 使用定理 `Matrix.vec_of`：vec_of (f : m -> n -> R) : vec (of f) = Function.uncurry 
(flip f)
· 使用定理 `Function.uncurry_flip`：uncurry_flip {α β γ} (f : α -> β -> γ) : uncurry 
(flip f) = uncurry f ∘ Prod.swap
· 使用定理 `Pi.uncurry_single_single`：∀ {ι : Type u_1} {ι' : Type u_2} [inst : Decid
ableEq ι] {M : Type u_9} [inst_1 : Zero M] [inst_2 : DecidableEq ι']   (i : ι) (
i' : ι') (b : …
· 使用定理 `Pi.single_comp_equiv`：∀ {α : Type u_2} {m : Type u_5} {n : Type u_6} [in
st : DecidableEq n] [inst_1 : DecidableEq m] [inst_2 : Zero α]   (σ : n ≃ m) (i 
: m) (x : …
-/
theorem vec_single [DecidableEq m] [DecidableEq n] [Zero R] (i : m) (j : n) (r : R) :
    vec (Matrix.single i j r) = Pi.single (j, i) r := by
  rw [single_eq_of_single_single, vec_of, Function.uncurry_flip, Pi.uncurry_single_single]
  exact Pi.single_comp_equiv (Equiv.prodComm _ _) _ _

section Kronecker
open scoped Kronecker

section CommSemigroup
variable [CommSemigroup R]

/-
**Matrix.hadamard_kronecker_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：hadamard_kronecker_hadamard (A B : Matrix l m R) (C D : Matrix n p R) : (A
 ⊙ B) otimesₖ (C ⊙ D) = (A otimesₖ C) ⊙ (B otimesₖ D)
参数：A B : Matrix l m R；C D : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
-/
theorem hadamard_kronecker_hadamard (A B : Matrix l m R) (C D : Matrix n p R) :
    (A ⊙ B) ⊗ₖ (C ⊙ D) = (A ⊗ₖ C) ⊙ (B ⊗ₖ D) :=
  ext fun _ _ => mul_mul_mul_comm _ _ _ _
/-
**Matrix.kronecker_hadamard_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_hadamard_kronecker (A : Matrix l m R) (B : Matrix n p R) (C : Ma
trix l m R) (D : Matrix n p R) : (A otimesₖ B) ⊙ (C otimesₖ D) = (A ⊙ C) otimesₖ
 (B ⊙ D)
参数：A : Matrix l m R；B : Matrix n p R；C : Matrix l m R；D : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.hadamard_kronecker_hadamard`：hadamard_kronecker_hadamard (A B : M
atrix l m R) (C D : Matrix n p R) : (A ⊙ B) otimesₖ (C ⊙ D) = (A otimesₖ C) ⊙ (B
 otimesₖ D)
-/
theorem kronecker_hadamard_kronecker
    (A : Matrix l m R) (B : Matrix n p R) (C : Matrix l m R) (D : Matrix n p R) :
    (A ⊗ₖ B) ⊙ (C ⊗ₖ D) = (A ⊙ C) ⊗ₖ (B ⊙ D) :=
  hadamard_kronecker_hadamard _ _ _ _ |>.symm

end CommSemigroup

section NonUnitalSemiring
variable [NonUnitalSemiring R] [Fintype m] [Fintype n]

/-- Technical lemma shared with `kronecker_mulVec_vec` and `vec_mul_eq_mulVec`. -/
/-
**Matrix.kronecker_mulVec_vec_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_mulVec_vec_of_commute (A : Matrix l m R) (X : Matrix m n R) (B :
 Matrix p n R) (hB : forall x i j, Commute x (B i j)) : (B otimesₖ A) *ᵥ vec X =
 vec (A * X * Bᵀ)
参数：A : Matrix l m R；X : Matrix m n R；B : Matrix p n R；hB : forall x i j, Commute
 x (B i j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Technical lemma shared with `kronecker_mulVec_vec` and `vec_mul_eq_mulVec`.
-/
theorem kronecker_mulVec_vec_of_commute (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
    (hB : ∀ x i j, Commute x (B i j)) :
    (B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ) := by
  ext ⟨k, l⟩
  simp_rw [vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, vec, (hB ..).eq]

/-- Technical lemma shared with `vec_vecMul_kronecker` and `vec_mul_eq_vecMul`. -/
/-
**Matrix.vec_vecMul_kronecker_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_vecMul_kronecker_of_commute (A : Matrix m l R) (X : Matrix m n R) (B :
 Matrix n p R) (hA : forall x i j, Commute (A i j) x) : vec X ᵥ* (B otimesₖ A) =
 vec (Aᵀ * X * B)
参数：A : Matrix m l R；X : Matrix m n R；B : Matrix n p R；hA : forall x i j, Commute
 (A i j) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.right_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S}, Com
mute b c → ∀ (a : S), a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Technical lemma shared with `vec_vecMul_kronecker` and `vec_mul_eq_vecMul`.
-/
theorem vec_vecMul_kronecker_of_commute (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
    (hA : ∀ x i j, Commute (A i j) x) :
    vec X ᵥ* (B ⊗ₖ A) = vec (Aᵀ * X * B) := by
  ext ⟨k, l⟩
  simp_rw [vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, vec]

end NonUnitalSemiring

section NonUnitalCommSemiring
variable [NonUnitalCommSemiring R] [Fintype m] [Fintype n]

/-
**Matrix.kronecker_mulVec_vec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n
 R) : (B otimesₖ A) *ᵥ vec X = vec (A * X * Bᵀ)
参数：A : Matrix l m R；X : Matrix m n R；B : Matrix p n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.kronecker_mulVec_vec_of_commute`：kronecker_mulVec_vec_of_commute 
(A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) (hB : forall x i j, Com
mute x (B i j)) : (B otimesₖ…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) :
    (B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ) :=
  kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _
/-
**Matrix.vec_vecMul_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p
 R) : vec X ᵥ* (B otimesₖ A) = vec (Aᵀ * X * B)
参数：A : Matrix m l R；X : Matrix m n R；B : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vec_vecMul_kronecker_of_commute`：vec_vecMul_kronecker_of_commute 
(A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) (hA : forall x i j, Com
mute (A i j) x) : vec X ᵥ* (…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) :
    vec X ᵥ* (B ⊗ₖ A) = vec (Aᵀ * X * B) :=
  vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _ => Commute.all _ _

end NonUnitalCommSemiring

section Semiring
variable [Semiring R] [Fintype m] [Fintype n]

/-
**Matrix.vec_mul_eq_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_mul_eq_mulVec [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R) : 
vec (A * B) = (1 otimesₖ A) *ᵥ vec B
参数：A : Matrix l m R；B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.kronecker_mulVec_vec_of_commute`：kronecker_mulVec_vec_of_commute 
(A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) (hB : forall x i j, Com
mute x (B i j)) : (B otimesₖ…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
-/
theorem vec_mul_eq_mulVec [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R) :
    vec (A * B) = (1 ⊗ₖ A) *ᵥ vec B := by
  rw [kronecker_mulVec_vec_of_commute, transpose_one, Matrix.mul_one]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]
/-
**Matrix.vec_mul_eq_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_mul_eq_vecMul [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R) : 
vec (A * B) = A.vec ᵥ* (B otimesₖ 1)
参数：A : Matrix m n R；B : Matrix n p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vec_vecMul_kronecker_of_commute`：vec_vecMul_kronecker_of_commute 
(A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) (hA : forall x i j, Com
mute (A i j) x) : vec X ᵥ* (…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
-/
theorem vec_mul_eq_vecMul [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R) :
    vec (A * B) = A.vec ᵥ* (B ⊗ₖ 1) := by
  rw [vec_vecMul_kronecker_of_commute, transpose_one, Matrix.one_mul]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

end Semiring

section Hadamard

variable [NonUnitalSemiring R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

/-- The Hadamard bilinear form equals the Kronecker bilinear form on diagonal embeddings. -/
/-
**Matrix.dotProduct_hadamard_mulVec_eq_kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix`。
形式化陈述：dotProduct_hadamard_mulVec_eq_kronecker (x : m -> R) (A B : Matrix m n R) 
(x' : n -> R) : x ⬝ᵥ (A ⊙ B) *ᵥ x' = vec (diagonal x) ⬝ᵥ (A otimesₖ B) *ᵥ vec (d
iagonal x')
参数：x : m -> R；A B : Matrix m n R；x' : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Fintype.sum_prod_type`：∀ {γ : Type u_3} {α₁ : Type u_4} {α₂ : Type u_5} 
[inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid γ]   (f : α₁ ×
 α₂ → γ), ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hadamard bilinear form equals the Kronecker bilinear form on diagonal embedd
ings.
-/
theorem dotProduct_hadamard_mulVec_eq_kronecker
    (x : m → R) (A B : Matrix m n R) (x' : n → R) :
    x ⬝ᵥ (A ⊙ B) *ᵥ x' = vec (diagonal x) ⬝ᵥ (A ⊗ₖ B) *ᵥ vec (diagonal x') := by
  simp [diagonal, mulVec, dotProduct, Fintype.sum_prod_type]

/-- The starred Hadamard bilinear form equals the starred Kronecker bilinear form on diagonal
embeddings. -/
/-
**Matrix.star_dotProduct_hadamard_mulVec_eq_kronecker** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix`。
形式化陈述：star_dotProduct_hadamard_mulVec_eq_kronecker [StarAddMonoid R] (x : m -> R
) (A B : Matrix m n R) (x' : n -> R) : star x ⬝ᵥ (A ⊙ B) *ᵥ x' = star (vec (diag
onal x)) ⬝ᵥ (A otimesₖ B) *ᵥ vec (diagonal x')
参数：x : m -> R；A B : Matrix m n R；x' : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_hadamard_mulVec_eq_kronecker`：dotProduct_hadamard_mulV
ec_eq_kronecker (x : m -> R) (A B : Matrix m n R) (x' : n -> R) : x ⬝ᵥ (A ⊙ B) *
ᵥ x' = vec (diagonal x) ⬝ᵥ (A otimes…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.map_diagonal_star`：map_diagonal_star [AddMonoid α] [StarAddMonoid
 α] (x : n -> α) : (diagonal x).map star = diagonal (star x)
· 使用定理 `Matrix.star_vec`：star_vec [Star R] (x : Matrix m n R) : star x.vec = (x.
map star).vec

--- 原说明 ---
The starred Hadamard bilinear form equals the starred Kronecker bilinear form on
 diagonal
embeddings.
-/
theorem star_dotProduct_hadamard_mulVec_eq_kronecker [StarAddMonoid R]
    (x : m → R) (A B : Matrix m n R) (x' : n → R) :
    star x ⬝ᵥ (A ⊙ B) *ᵥ x' = star (vec (diagonal x)) ⬝ᵥ (A ⊗ₖ B) *ᵥ vec (diagonal x') := by
  rw [dotProduct_hadamard_mulVec_eq_kronecker, ← map_diagonal_star, star_vec]

end Hadamard

end Kronecker

end Matrix

