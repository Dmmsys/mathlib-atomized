/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Matrix multiplication

This file defines vector and matrix multiplication

## Main definitions
* `dotProduct`: the dot product between two vectors
* `Matrix.mul`: multiplication of two matrices
* `Matrix.mulVec`: multiplication of a matrix with a vector
* `Matrix.vecMul`: multiplication of a vector with a matrix
* `Matrix.vecMulVec`: multiplication of a vector with a vector to get a matrix
* `Matrix.instRing`: square matrices form a ring

## Notation

The scope `Matrix` gives the following notation:

* `⬝ᵥ` for `dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

@[expose] public section

assert_not_exists Algebra Field TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

open Matrix

section DotProduct

variable [Fintype m] [Fintype n]

/-- `dotProduct v w` is the sum of the entrywise products `v i * w i`.

See also `dotProductEquiv`. -/
/-
**dotProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dotProduct [Mul α] [AddCommMonoid α] (v w : m -> α) : α
参数：v w : m -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dotProduct v w` is the sum of the entrywise products `v i * w i`.

See also `dotProductEquiv`.
-/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
@[inherit_doc]
infixl:72 " ⬝ᵥ " => dotProduct

/-
**dotProduct_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_assoc [NonUnitalSemiring α] (u : m -> α) (w : n -> α) (v : Matr
ix m n α) : (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w
参数：u : m -> α；w : n -> α；v : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm
/-
**dotProduct_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : m -> α) : v ⬝ᵥ w = 
w ⬝ᵥ v
参数：v w : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dotProduct, mul_comm]

@[simp]
/-
**dotProduct_pUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit -> α) : v ⬝ᵥ w = v
 ⟨⟩ * w ⟨⟩
参数：v w : PUnit -> α。
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
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dotProduct]

section MulOneClass

variable [MulOneClass α] [AddCommMonoid α]

/-
**dotProduct_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_one (v : n -> α) : v ⬝ᵥ 1 = ∑ i, v i
参数：v : n -> α。
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_one (v : n → α) : v ⬝ᵥ 1 = ∑ i, v i := by simp [(· ⬝ᵥ ·)]
/-
**one_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_dotProduct (v : n -> α) : 1 ⬝ᵥ v = ∑ i, v i
参数：v : n -> α。
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_dotProduct (v : n → α) : 1 ⬝ᵥ v = ∑ i, v i := by simp [(· ⬝ᵥ ·)]

end MulOneClass

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] (u v w : m → α) (x y : n → α)

@[simp]
/-
**dotProduct_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_zero : v ⬝ᵥ 0 = 0
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_zero : v ⬝ᵥ 0 = 0 := by simp [dotProduct]

@[simp]
/-
**dotProduct_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
-/
theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dotProduct_zero v

@[simp]
/-
**zero_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_dotProduct : 0 ⬝ᵥ v = 0
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_dotProduct : 0 ⬝ᵥ v = 0 := by simp [dotProduct]

@[simp]
/-
**zero_dotProduct'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
-/
theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dotProduct v

@[simp]
/-
**add_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
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
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

@[simp]
/-
**dotProduct_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
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
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

@[simp]
/-
**sumElim_dotProduct_sumElim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sumElim_dotProduct_sumElim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ 
y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumElim_dotProduct_sumElim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct]

/-- Permuting a vector on the left of a dot product can be transferred to the right. -/
@[simp]
/-
**comp_equiv_symm_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Permuting a vector on the left of a dot product can be transferred to the right.
-/
theorem comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e :=
  (e.sum_comp _).symm.trans <|
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]

/-- Permuting a vector on the right of a dot product can be transferred to the left. -/
@[simp]
/-
**dotProduct_comp_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x
参数：e : n ≃ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `comp_equiv_symm_dotProduct`：comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘
 e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e

--- 原说明 ---
Permuting a vector on the right of a dot product can be transferred to the left.
-/
theorem dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x := by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

/-- Permuting vectors on both sides of a dot product is a no-op. -/
@[simp]
/-
**comp_equiv_dotProduct_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y
参数：e : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Permuting vectors on both sides of a dot product is a no-op.
-/
theorem comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y := by
  simp [← dotProduct_comp_equiv_symm, Function.comp_def _ e.symm]
/-
**dotProduct_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_sum {ι : Type*} (u : m -> α) (s : Finset ι) (v : ι -> (m -> α))
 : u ⬝ᵥ ∑ i in s, v i = ∑ i in s, u ⬝ᵥ v i
参数：u : m -> α；s : Finset ι；v : ι -> (m -> α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem dotProduct_sum {ι : Type*} (u : m → α) (s : Finset ι) (v : ι → (m → α)) :
    u ⬝ᵥ ∑ i ∈ s, v i = ∑ i ∈ s, u ⬝ᵥ v i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
/-
**sum_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_dotProduct {ι : Type*} (s : Finset ι) (u : ι -> (m -> α)) (v : m -> α)
 : (∑ i in s, u i) ⬝ᵥ v = ∑ i in s, u i ⬝ᵥ v
参数：s : Finset ι；u : ι -> (m -> α)；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
-/
theorem sum_dotProduct {ι : Type*} (s : Finset ι) (u : ι → (m → α)) (v : m → α) :
    (∑ i ∈ s, u i) ⬝ᵥ v = ∑ i ∈ s, u i ⬝ᵥ v := by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m → α)

@[simp]
/-
**diagonal_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i := by
  have : ∀ j ≠ i, diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp


@[simp]
/-
**dotProduct_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i := by
  have : ∀ j ≠ i, v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/-
**dotProduct_diagonal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i := by
  have : ∀ j ≠ i, v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/-
**single_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i
参数：x : α；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
-- Porting note: added `(_ : m → α)`
  have : ∀ j ≠ i, (Pi.single i x : m → α) j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/-
**dotProduct_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x
参数：x : α；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
-- Porting note: added `(_ : m → α)`
  have : ∀ j ≠ i, v j * (Pi.single i x : m → α) j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

end NonUnitalNonAssocSemiringDecidable

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
/-
**one_dotProduct_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_dotProduct_one : (1 : n -> α) ⬝ᵥ 1 = Fintype.card n
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_dotProduct_one : (1 : n → α) ⬝ᵥ 1 = Fintype.card n := by
  simp [dotProduct]
/-
**dotProduct_single_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_single_one [DecidableEq n] (v : n -> α) (i : n) : v ⬝ᵥ Pi.singl
e i 1 = v i
参数：v : n -> α；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_single`：dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i 
x = v i * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem dotProduct_single_one [DecidableEq n] (v : n → α) (i : n) :
    v ⬝ᵥ Pi.single i 1 = v i := by
  rw [dotProduct_single, mul_one]
/-
**single_one_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：single_one_dotProduct [DecidableEq n] (i : n) (v : n -> α) : Pi.single i 1
 ⬝ᵥ v = v i
参数：i : n；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem single_one_dotProduct [DecidableEq n] (i : n) (v : n → α) :
    Pi.single i 1 ⬝ᵥ v = v i := by
  rw [single_dotProduct, one_mul]

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] (u v w : m → α)

@[simp]
/-
**neg_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
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
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by simp [dotProduct]

@[simp]
/-
**dotProduct_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
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
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by simp [dotProduct]
/-
**neg_dotProduct_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_dotProduct_neg : -v ⬝ᵥ -w = v ⬝ᵥ w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_dotProduct`：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
· 使用定理 `dotProduct_neg`：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_dotProduct_neg : -v ⬝ᵥ -w = v ⬝ᵥ w := by
  rw [neg_dotProduct, dotProduct_neg, neg_neg]

@[simp]
/-
**sub_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_dotProduct`：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
· 使用定理 `neg_dotProduct`：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by simp [sub_eq_add_neg]

@[simp]
/-
**dotProduct_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `dotProduct_add`：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
· 使用定理 `dotProduct_neg`：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]

end NonUnitalNonAssocRing

section DistribMulAction

variable [Mul α] [AddCommMonoid α] [DistribSMul R α]

@[simp]
/-
**smul_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m -> α) : x • v ⬝ᵥ w 
= x • (v ⬝ᵥ w)
参数：x : R；v w : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) :
    x • v ⬝ᵥ w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]
/-
**dotProduct_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m -> α) : v ⬝ᵥ x • w 
= x • (v ⬝ᵥ w)
参数：x : R；v w : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) :
    v ⬝ᵥ x • w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

end DistribMulAction

section CommRing
variable [CommRing α] [Nontrivial m] [Nontrivial α]

/-- For any vector `a` in a nontrivial commutative ring with nontrivial index,
there exists a non-zero vector `b` such that `b ⬝ᵥ a = 0`. In other words,
there exists a non-zero orthogonal vector. -/
/-
**exists_ne_zero_dotProduct_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ne_zero_dotProduct_eq_zero (a : m -> α) : exists b != 0, b ⬝ᵥ a = 0
参数：a : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.sum_eq_ite`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠
 a → f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
For any vector `a` in a nontrivial commutative ring with nontrivial index,
there exists a non-zero vector `b` such that `b ⬝ᵥ a = 0`. In other words,
there exists a non-zero orthogonal vector.
-/
theorem exists_ne_zero_dotProduct_eq_zero (a : m → α) : ∃ b ≠ 0, b ⬝ᵥ a = 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j : m, i ≠ j := nontrivial_iff.mp ‹_›
  classical
  use if a i = 0 then Pi.single i 1 else if a j = 0 then Pi.single j 1 else
    fun k => if k = i then a j else if k = j then - a i else 0
  split_ifs with h h2
  · simp [h]
  · simp [h2]
  · refine ⟨Function.ne_iff.mpr ⟨i, by simp [h2]⟩, ?_⟩
    simp [dotProduct, Finset.sum_ite, Finset.sum_eq_ite i, hij.symm, mul_comm (a i)]
/-
**not_injective_dotProduct_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_injective_dotProduct_left (a : m -> α) : ¬ Function.Injective (dotProd
uct a)
参数：a : m -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne_zero_dotProduct_eq_zero`：exists_ne_zero_dotProduct_eq_zero (a 
: m -> α) : exists b != 0, b ⬝ᵥ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma not_injective_dotProduct_left (a : m → α) :
    ¬ Function.Injective (dotProduct a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [dotProduct_comm a b, hba, hb] using @h b 0
/-
**not_injective_dotProduct_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_injective_dotProduct_right (a : m -> α) : ¬ Function.Injective (dotPro
duct · a)
参数：a : m -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne_zero_dotProduct_eq_zero`：exists_ne_zero_dotProduct_eq_zero (a 
: m -> α) : exists b != 0, b ⬝ᵥ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma not_injective_dotProduct_right (a : m → α) :
    ¬ Function.Injective (dotProduct · a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [hba, hb] using @h b 0

end CommRing

end DotProduct

open Matrix

namespace Matrix

/-- `M * N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M * N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype m] [Mul α] [AddCommMonoid α] :
    HMul (Matrix l m α) (Matrix m n α) (Matrix l n α) where
  hMul M N := fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k
/-
**Matrix.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Ma
trix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = ∑ j, M i j * N j k :=
  rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where
  mul M N := M * N
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype n] [DecidableEq n] [MulOne α] [AddCommMonoid α] : MulOne (Matrix n n α) where
/-
**Matrix.mul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : M
atrix m n α} {i k} : (M * N) i k = (M i) ⬝ᵥ fun j => N j k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = (M i) ⬝ᵥ fun j => N j k :=
  rfl
/-
**Matrix.two_mul_expl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：two_mul_expl {R : Type*} [NonUnitalNonAssocSemiring R] (A B : Matrix (Fin 
2) (Fin 2) R) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧ (A * B) 0 1 = A 0 
0 * B 0 1 + A 0 1 * B 1 1 ∧ (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B
) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1
参数：A B : Matrix (Fin 2) (Fin 2) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_fin_eq_sum_range`：∀ {β : Type u_2} [inst : AddCommMonoid β] {
n : ℕ} (c : Fin n → β),   ∑ i, c i = ∑ i ∈ Finset.range n, if h : i < n then c ⟨
i, h⟩ else 0
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem two_mul_expl {R : Type*} [NonUnitalNonAssocSemiring R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
    (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp

section AddCommMonoid

variable [AddCommMonoid α] [Mul α]

@[simp]
/-
**Matrix.smul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α 
α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N)
参数：a : R；M : Matrix m n α；N : Matrix n l α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `smul_dotProduct`：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m 
-> α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
-/
theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N) := by
  ext
  apply smul_dotProduct a

@[simp]
/-
**Matrix.mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Type u_7} {α : Type v}
 [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintype n] [inst_3 : Mono
id R] [inst_4 : DistribMulAction R α] [SMulCommClass R α α] (M : Matrix m n α)  
 (a : R) (N : Matrix n l α), M * a • N = a • (M * N)
参数：M : Matrix m n α；a : R；N : Matrix n l α；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_smul`：dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m 
-> α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w)
-/
protected theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
    (M : Matrix m n α) (a : R) (N : Matrix n l α) : M * (a • N) = a • (M * N) := by
  ext
  apply dotProduct_smul

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

@[simp]
/-
**Matrix.mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n α), M * 0 = 0
参数：M : Matrix m n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
-/
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M * (0 : Matrix n o α) = 0 := by
  ext
  apply dotProduct_zero

@[simp]
/-
**Matrix.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonUni
talNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n α), 0 * M = 0
参数：M : Matrix m n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
-/
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) * M = 0 := by
  ext
  apply zero_dotProduct
/-
**Matrix.mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n α) (M N : Matrix n
 o α), L * (M + N) = L * M + L * N
参数：L : Matrix m n α；M N : Matrix n o α；M + N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_add`：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
-/
protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
    L * (M + N) = L * M + L * N := by
  ext
  apply dotProduct_add
/-
**Matrix.add_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonUni
talNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l m α) (N : Matrix m
 n α), (L + M) * N = L * N + M * N
参数：L M : Matrix l m α；N : Matrix m n α；L + M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `add_dotProduct`：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
-/
protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
    (L + M) * N = L * N + M * N := by
  ext
  apply add_dotProduct
/-
**Matrix.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix 
n n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
-/
instance nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
  { Matrix.addCommMonoid with
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]
/-
**Matrix.diagonal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_mul [Fintype m] [DecidableEq m] (d : m -> α) (M : Matrix m n α) (
i j) : (diagonal d * M) i j = d i * M i j
参数：d : m -> α；M : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `diagonal_dotProduct`：diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v
 i * w i
-/
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) (i j) :
    (diagonal d * M) i j = d i * M i j :=
  diagonal_dotProduct _ _ _

@[simp]
/-
**Matrix.mul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> α) (M : Matrix m n α) (
i j) : (M * diagonal d) i j = M i j * d j
参数：d : n -> α；M : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `dotProduct_diagonal`：dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v
 i * w i
-/
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) (i j) :
    (M * diagonal d) i j = M i j * d j := by
  rw [← diagonal_transpose]
  apply dotProduct_diagonal

@[simp]
/-
**Matrix.diagonal_mul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) : diago
nal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i
参数：d₁ d₂ : n -> α。
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
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]
/-
**Matrix.diagonal_mul_diagonal'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) : diag
onal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i
参数：d₁ d₂ : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
-/
theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _
/-
**Matrix.commute_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：commute_diagonal {α : Type*} [NonUnitalNonAssocCommSemiring α] [Fintype n]
 [DecidableEq n] (d₁ d₂ : n -> α) : Commute (diagonal d₁) (diagonal d₂)
参数：d₁ d₂ : n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commute_diagonal {α : Type*} [NonUnitalNonAssocCommSemiring α]
    [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    Commute (diagonal d₁) (diagonal d₂) := by
  simp_rw [commute_iff_eq, diagonal_mul_diagonal, mul_comm]
/-
**Matrix.smul_eq_diagonal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α
) : a • M = (diagonal fun _ => a) * M
参数：M : Matrix m n α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_mul`：diagonal_mul [Fintype m] [DecidableEq m] (d : m -> 
α) (M : Matrix m n α) (i j) : (diagonal d * M) i j = d i * M i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonal fun _ => a) * M := by
  ext
  simp
/-
**Matrix.op_smul_eq_mul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：op_smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a 
: α) : MulOpposite.op a • M = M * (diagonal fun _ : n => a)
参数：M : Matrix m n α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    MulOpposite.op a • M = M * (diagonal fun _ : n => a) := by
  ext
  simp

/-- Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
/-
**Matrix.addMonoidHomMulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α ->+ Matr
ix l n α where toFun x
参数：M : Matrix l m α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…

--- 原说明 ---
Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices.
-/
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α where
  toFun x := M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _

/-- Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
/-
**Matrix.addMonoidHomMulRight** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α ->+ Mat
rix l n α where toFun x
参数：M : Matrix m n α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…

--- 原说明 ---
Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices
.
-/
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α where
  toFun x := x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _
/-
**Matrix.sum_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [
inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype m] (s : Finset β) (f : β
 → Matrix l m α) (M : Matrix m n α), (∑ a ∈ s, f a) * M = ∑ a ∈ s, f a * M
参数：s : Finset β；f : β → Matrix l m α；M : Matrix m n α；∑ a ∈ s, f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
    (∑ a ∈ s, f a) * M = ∑ a ∈ s, f a * M :=
  map_sum (addMonoidHomMulRight M) f s
/-
**Matrix.mul_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [
inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype m] (s : Finset β) (f : β
 → Matrix m n α) (M : Matrix l m α), M * ∑ a ∈ s, f a = ∑ a ∈ s, M * f a
参数：s : Finset β；f : β → Matrix m n α；M : Matrix l m α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
    (M * ∑ a ∈ s, f a) = ∑ a ∈ s, M * f a :=
  map_sum (addMonoidHomMulLeft M) f s

/-- This instance enables use with `smul_mul_assoc`. -/
/-
**Matrix.Semiring.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Semiring`。
形式化陈述：∀ {n : Type u_3} {R : Type u_7} {α : Type v} [inst : NonUnitalNonAssocSemi
ring α] [inst_1 : Fintype n]   [inst_2 : Monoid R] [inst_3 : DistribMulAction R 
α] [IsScalarTower R α α],   IsScalarTower R (Matrix n n α) (Matrix n n α)
参数：Matrix n n α；Matrix n n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…

--- 原说明 ---
This instance enables use with `smul_mul_assoc`.
-/
instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
    [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩

/-- This instance enables use with `mul_smul_comm`. -/
/-
**Matrix.Semiring.smulCommClass** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Semiring`。
形式化陈述：∀ {n : Type u_3} {R : Type u_7} {α : Type v} [inst : NonUnitalNonAssocSemi
ring α] [inst_1 : Fintype n]   [inst_2 : Monoid R] [inst_3 : DistribMulAction R 
α] [SMulCommClass R α α],   SMulCommClass R (Matrix n n α) (Matrix n n α)
参数：Matrix n n α；Matrix n n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …

--- 原说明 ---
This instance enables use with `mul_smul_comm`.
-/
instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
    [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

@[simp]
/-
**Matrix.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} {β : Type w} [
inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L : Matrix m n α} {M
 : Matrix n o α} [inst_2 : NonUnitalNonAssocSemiring β] {F : Type u_10}   [inst_
3 : FunLike F α β] [NonUnitalRingHomClass F α β] {f : F}, (L * M).map ⇑f = L.map
 ⇑f * M.map ⇑f
参数：L * M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α}
    [NonUnitalNonAssocSemiring β] {F} [FunLike F α β] [NonUnitalRingHomClass F α β] {f : F} :
    (L * M).map f = L.map f * M.map f := by
  ext
  simp [mul_apply, map_sum]

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
/-
**Matrix.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonAssocSemiring α] [
inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n α), 1 * M = M
参数：M : Matrix m n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.diagonal_mul`：diagonal_mul [Fintype m] [DecidableEq m] (d : m -> 
α) (M : Matrix m n α) (i j) : (diagonal d * M) i j = d i * M i j
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
    (1 : Matrix m m α) * M = M := by
  ext
  rw [← diagonal_one, diagonal_mul, one_mul]

@[simp]
/-
**Matrix.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : NonAssocSemiring α] [
inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n α), M * 1 = M
参数：M : Matrix m n α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
    M * (1 : Matrix n n α) = M := by
  ext
  rw [← diagonal_one, mul_diagonal, mul_one]
/-
**Matrix.nonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n 
n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
-/
instance nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.instAddCommMonoidWithOne with
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }
/-
**Matrix.smul_one_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_one_eq_diagonal [DecidableEq m] (a : α) : a • (1 : Matrix m m α) = di
agonal fun _ => a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_one_eq_diagonal [DecidableEq m] (a : α) :
    a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one]
/-
**Matrix.op_smul_one_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：op_smul_one_eq_diagonal [DecidableEq m] (a : α) : MulOpposite.op a • (1 : 
Matrix m m α) = diagonal fun _ => a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_smul_one_eq_diagonal [DecidableEq m] (a : α) :
    MulOpposite.op a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, op_smul_eq_mul, one_mul]

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α] [Fintype m] [Fintype n]

/-
**Matrix.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v}
 [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2 : Fintype n] (L : M
atrix l m α) (M : Matrix m n α) (N : Matrix n o α),   L * M * N = L * (M * N)
参数：L : Matrix l m α；M : Matrix m n α；N : Matrix n o α；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_assoc`：dotProduct_assoc [NonUnitalSemiring α] (u : m -> α) (w
 : n -> α) (v : Matrix m n α) : (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i
 => v …
-/
protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
    L * M * N = L * (M * N) := by
  ext
  apply dotProduct_assoc
/-
**Matrix.nonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：nonUnitalSemiring : NonUnitalSemiring (Matrix n n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
-/
instance nonUnitalSemiring : NonUnitalSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

end NonUnitalSemiring

section Semiring

variable [Semiring α]

/-
**Matrix.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：semiring [Fintype n] [DecidableEq n] : Semiring (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring [Fintype n] [DecidableEq n] : Semiring (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

end Semiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] [Fintype n]

@[simp]
/-
**Matrix.neg_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (N : Matrix n o α),
 -M * N = -(M * N)
参数：M : Matrix m n α；N : Matrix n o α；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `neg_dotProduct`：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
-/
protected theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) : (-M) * N = -(M * N) := by
  ext
  apply neg_dotProduct

@[simp]
/-
**Matrix.mul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (N : Matrix n o α),
 M * -N = -(M * N)
参数：M : Matrix m n α；N : Matrix n o α；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_neg`：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
-/
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M * (-N) = -(M * N) := by
  ext
  apply dotProduct_neg
/-
**Matrix.sub_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocRing α] [inst_1 : Fintype n]   (M M' : Matrix m n α) (N : Matrix n o 
α), (M - M') * N = M * N - M' * N
参数：M M' : Matrix m n α；N : Matrix n o α；M - M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
-/
protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
    (M - M') * N = M * N - M' * N := by
  rw [sub_eq_add_neg, Matrix.add_mul, Matrix.neg_mul, sub_eq_add_neg]
/-
**Matrix.mul_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type v} [inst : NonUni
talNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (N N' : Matrix n o 
α), M * (N - N') = M * N - M * N'
参数：M : Matrix m n α；N N' : Matrix n o α；N - N'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
· 使用定理 `Matrix.mul_neg`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
-/
protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
    M * (N - N') = M * N - M * N' := by
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg, sub_eq_add_neg]
/-
**Matrix.nonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：nonUnitalNonAssocRing : NonUnitalNonAssocRing (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

end NonUnitalNonAssocRing

/-
**Matrix.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instNonUnitalRing [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n 
n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }
/-
**Matrix.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing α] : NonAssocRi
ng (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing α] :
    NonAssocRing (Matrix n n α) :=
  { Matrix.nonAssocSemiring, Matrix.instAddCommGroupWithOne with }
/-
**Matrix.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：instRing [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α) :=
  { Matrix.semiring, Matrix.instAddCommGroupWithOne with }

section Semiring

variable [Semiring α]

@[simp]
/-
**Matrix.mul_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) : (
of fun i j => a * M i j) * N = a • (M * N)
参数：M : Matrix m n α；N : Matrix n o α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
-/
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) * N = a • (M * N) :=
  smul_mul a M N
/-
**Matrix.pow_apply_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：pow_apply_nonneg [Fintype n] [DecidableEq n] [PartialOrder α] [IsOrderedRi
ng α] {A : Matrix n n α} (hA : forall i j, 0 <= A i j) (k : Nat) : forall i j, 0
 <= (A ^ k) i j
参数：hA : forall i j, 0 <= A i j；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma pow_apply_nonneg [Fintype n] [DecidableEq n] [PartialOrder α] [IsOrderedRing α]
    {A : Matrix n n α} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => aesop (add simp one_apply)
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

end Semiring

section CommSemiring

variable [CommSemiring α]

/-
**Matrix.smul_eq_mul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α
) : a • M = M * diagonal fun _ => a
参数：M : Matrix m n α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    a • M = M * diagonal fun _ => a := by
  ext
  simp [mul_comm]

@[simp]
/-
**Matrix.mul_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_mul_right [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) : 
(M * of fun i j => a * N i j) = a • (M * N)
参数：M : Matrix m n α；N : Matrix n o α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem mul_mul_right [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (M * of fun i j => a * N i j) = a • (M * N) :=
  Matrix.mul_smul M a N

end CommSemiring

end Matrix

section IsStablyFiniteRing

/-- A semiring is stably finite if every matrix ring over it is Dedekind-finite. -/
/-
**IsStablyFiniteRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_10) → [MulOne R] → [AddCommMonoid R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semiring is stably finite if every matrix ring over it is Dedekind-finite.
-/
@[mk_iff] class IsStablyFiniteRing (R) [MulOne R] [AddCommMonoid R] : Prop where
  isDedekindFiniteMonoid (n : ℕ) : IsDedekindFiniteMonoid (Matrix (Fin n) (Fin n) R)

attribute [instance] IsStablyFiniteRing.isDedekindFiniteMonoid
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (R) [NonAssocSemiring R] [IsStablyFiniteRing R] :
    IsDedekindFiniteMonoid R :=
  let f : R →* Matrix (Fin 1) (Fin 1) R :=
    ⟨⟨fun r ↦ diagonal fun _ ↦ r, rfl⟩, fun _ _ ↦ (diagonal_mul_diagonal ..).symm⟩
  .of_injective f fun _ _ eq ↦ by simpa [f] using congr($eq 0 0)

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
/-
**IsStablyFiniteRing.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStablyFiniteRing.of_injective [FunLike F R S] [RingHomClass F R S] (f : 
F) (hf : Function.Injective f) [IsStablyFiniteRing S] : IsStablyFiniteRing R whe
re isDedekindFiniteMonoid n
参数：f : F；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsDedekindFiniteMonoid.of_injective`：∀ {M : Type u_4} {N : Type u_5} {F 
: Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [Mo
noidHomClass F M N] (f : …
· 使用定理 `Matrix.map_injective`：map_injective {f : α -> β} (hf : Function.Injectiv
e f) : Function.Injective fun M : Matrix m n α => M.map f
· 使用定理 `IsStablyFiniteRing.isDedekindFiniteMonoid`：∀ {R : Type u_10} {inst : Mul
One R} {inst_1 : AddCommMonoid R} [self : IsStablyFiniteRing R] (n : ℕ),   IsDed
ekindFiniteMonoid (Matrix (Fin …
-/
theorem IsStablyFiniteRing.of_injective [FunLike F R S] [RingHomClass F R S] (f : F)
    (hf : Function.Injective f) [IsStablyFiniteRing S] : IsStablyFiniteRing R where
  isDedekindFiniteMonoid n :=
  let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) R ↦ M.map f,
    Matrix.map_one _ (map_zero f) (map_one f)⟩ fun _ _ ↦ Matrix.map_mul
  .of_injective f <| Matrix.map_injective hf
/-
**RingEquiv.isStablyFiniteRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingEquiv.isStablyFiniteRing_iff [EquivLike F R S] [RingEquivClass F R S] 
(f : F) : IsStablyFiniteRing R ↔ IsStablyFiniteRing S where mp _
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStablyFiniteRing.of_injective`：IsStablyFiniteRing.of_injective [FunLik
e F R S] [RingHomClass F R S] (f : F) (hf : Function.Injective f) [IsStablyFinit
eRing S] : IsStablyFi…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
theorem RingEquiv.isStablyFiniteRing_iff [EquivLike F R S] [RingEquivClass F R S] (f : F) :
    IsStablyFiniteRing R ↔ IsStablyFiniteRing S where
  mp _ := .of_injective _ (RingEquivClass.toRingEquiv f).symm.injective
  mpr _ := .of_injective f (EquivLike.injective f)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SetLike F R] [SubsemiringClass F R] (S : F) [IsStablyFiniteRing R] :
    IsStablyFiniteRing S :=
  .of_injective _ (Subsemiring.subtype_injective <| .ofClass S)

end IsStablyFiniteRing

open Matrix

namespace Matrix

/-- For two vectors `w` and `v`, `vecMulVec w v i j` is defined to be `w i * v j`.
Put another way, `vecMulVec w v` is exactly `replicateCol ι w * replicateRow ι v` for
`Unique ι`; see `vecMulVec_eq`. -/
/-
**Matrix.vecMulVec** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecMulVec [Mul α] (w : m -> α) (v : n -> α) : Matrix m n α
参数：w : m -> α；v : n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two vectors `w` and `v`, `vecMulVec w v i j` is defined to be `w i * v j`.
Put another way, `vecMulVec w v` is exactly `replicateCol ι w * replicateRow ι v
` for
`Unique ι`; see `vecMulVec_eq`.
-/
def vecMulVec [Mul α] (w : m → α) (v : n → α) : Matrix m n α :=
  of fun x y => w x * v y

-- TODO: set as an equation lemma for `vecMulVec`, see https://github.com/leanprover-community/mathlib4/pull/3024
/-
**Matrix.vecMulVec_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_apply [Mul α] (w : m -> α) (v : n -> α) (i j) : vecMulVec w v i 
j = w i * v j
参数：w : m -> α；v : n -> α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vecMulVec_apply [Mul α] (w : m → α) (v : n → α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl
/-
**Matrix.row_vecMulVec** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_vecMulVec [Mul α] (w : m -> α) (v : n -> α) (i : m) : (vecMulVec w v).
row i = w i • v
参数：w : m -> α；v : n -> α；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_vecMulVec [Mul α] (w : m → α) (v : n → α) (i : m) :
    (vecMulVec w v).row i = w i • v := rfl
/-
**Matrix.col_vecMulVec** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_vecMulVec [Mul α] (w : m -> α) (v : n -> α) (j : n) : (vecMulVec w v).
col j = MulOpposite.op (v j) • w
参数：w : m -> α；v : n -> α；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_vecMulVec [Mul α] (w : m → α) (v : n → α) (j : n) :
    (vecMulVec w v).col j = MulOpposite.op (v j) • w := rfl
/-
**Matrix.zero_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : MulZeroClass α] (v : 
n → α), Matrix.vecMulVec 0 v = 0
参数：v : n → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
@[simp] theorem zero_vecMulVec [MulZeroClass α] (v : n → α) : vecMulVec (0 : m → α) v = 0 :=
  ext fun _ _ => zero_mul _
/-
**Matrix.vecMulVec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {α : Type v} [inst : MulZeroClass α] (w : m → α), Matrix.
vecMulVec w 0 = 0
参数：w : m → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] theorem vecMulVec_zero [MulZeroClass α] (w : m → α) : vecMulVec w (0 : m → α) = 0 :=
  ext fun _ _ => mul_zero _
/-
**Matrix.vecMulVec_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_ne_zero [Mul α] [Zero α] [NoZeroDivisors α] {a b : n -> α} (ha :
 a != 0) (hb : b != 0) : vecMulVec a b != 0
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem vecMulVec_ne_zero [Mul α] [Zero α] [NoZeroDivisors α] {a b : n → α}
    (ha : a ≠ 0) (hb : b ≠ 0) : vecMulVec a b ≠ 0 := by
  intro h
  obtain ⟨i, ha⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hb⟩ := Function.ne_iff.mp hb
  exact mul_ne_zero ha hb congr($h i j)
/-
**Matrix.vecMulVec_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : MulZeroClass α] [NoZeroDivisors α] {
a b : n → α},   Matrix.vecMulVec a b = 0 ↔ a = 0 ∨ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem vecMulVec_eq_zero [MulZeroClass α] [NoZeroDivisors α] {a b : n → α} :
    vecMulVec a b = 0 ↔ a = 0 ∨ b = 0 := by
  simp only [← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, funext_iff, Pi.zero_apply,
    forall_or_left, forall_or_right]
/-
**Matrix.add_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_vecMulVec [Mul α] [Add α] [RightDistribClass α] (w₁ w₂ : m -> α) (v : 
n -> α) : vecMulVec (w₁ + w₂) v = vecMulVec w₁ v + vecMulVec w₂ v
参数：w₁ w₂ : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
-/
theorem add_vecMulVec [Mul α] [Add α] [RightDistribClass α] (w₁ w₂ : m → α) (v : n → α) :
    vecMulVec (w₁ + w₂) v = vecMulVec w₁ v + vecMulVec w₂ v :=
  ext fun _ _ => add_mul _ _ _
/-
**Matrix.vecMulVec_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_add [Mul α] [Add α] [LeftDistribClass α] (w : m -> α) (v₁ v₂ : n
 -> α) : vecMulVec w (v₁ + v₂) = vecMulVec w v₁ + vecMulVec w v₂
参数：w : m -> α；v₁ v₂ : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
-/
theorem vecMulVec_add [Mul α] [Add α] [LeftDistribClass α] (w : m → α) (v₁ v₂ : n → α) :
    vecMulVec w (v₁ + v₂) = vecMulVec w v₁ + vecMulVec w v₂ :=
  ext fun _ _ => mul_add _ _ _

@[simp]
/-
**Matrix.neg_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：neg_vecMulVec [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α) : vecMul
Vec (-w) v = -vecMulVec w v
参数：w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem neg_vecMulVec [Mul α] [HasDistribNeg α] (w : m → α) (v : n → α) :
    vecMulVec (-w) v = -vecMulVec w v :=
  ext fun _ _ => neg_mul _ _

@[simp]
/-
**Matrix.vecMulVec_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_neg [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α) : vecMul
Vec w (-v) = -vecMulVec w v
参数：w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem vecMulVec_neg [Mul α] [HasDistribNeg α] (w : m → α) (v : n → α) :
    vecMulVec w (-v) = -vecMulVec w v :=
  ext fun _ _ => mul_neg _ _

@[simp]
/-
**Matrix.smul_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_vecMulVec [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (w : m -> 
α) (v : n -> α) : vecMulVec (r • w) v = r • vecMulVec w v
参数：r : R；w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
theorem smul_vecMulVec [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (w : m → α) (v : n → α) :
    vecMulVec (r • w) v = r • vecMulVec w v :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
/-
**Matrix.vecMulVec_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (w : m -> 
α) (v : n -> α) : vecMulVec w (r • v) = r • vecMulVec w v
参数：r : R；w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
-/
theorem vecMulVec_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (w : m → α) (v : n → α) :
    vecMulVec w (r • v) = r • vecMulVec w v :=
  ext fun _ _ => mul_smul_comm _ _ _
/-
**Matrix.vecMulVec_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_smul' [Semigroup α] (w : m -> α) (r : α) (v : n -> α) : vecMulVe
c w (r • v) = vecMulVec (MulOpposite.op r • w) v
参数：w : m -> α；r : α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem vecMulVec_smul' [Semigroup α] (w : m → α) (r : α) (v : n → α) :
    vecMulVec w (r • v) = vecMulVec (MulOpposite.op r • w) v :=
  ext fun _ _ => mul_assoc _ _ _ |>.symm

@[simp]
/-
**Matrix.transpose_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_vecMulVec [CommMagma α] (w : m -> α) (v : n -> α) : (vecMulVec w
 v)ᵀ = vecMulVec v w
参数：w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem transpose_vecMulVec [CommMagma α] (w : m → α) (v : n → α) :
    (vecMulVec w v)ᵀ = vecMulVec v w :=
  ext fun _ _ => mul_comm _ _

@[simp]
/-
**Matrix.diag_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_vecMulVec [Mul α] (u v : n -> α) : diag (vecMulVec u v) = u * v
参数：u v : n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_vecMulVec [Mul α] (u v : n → α) : diag (vecMulVec u v) = u * v := rfl

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/--
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` and vector `v`,
where `v` is seen as a column vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `A *ᵥ v ⬝ᵥ B *ᵥ w` is parsed as `(A *ᵥ v) ⬝ᵥ (B *ᵥ w)`.
-/
/-
**Matrix.mulVec** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype n] → Matrix m n α → (n → α) → m → α
参数：n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` 
and vector `v`,
where `v` is seen as a column vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotPr
oduct`,
so that `A *ᵥ v ⬝ᵥ B *ᵥ w` is parsed as `(A *ᵥ v) ⬝ᵥ (B *ᵥ w)`.
-/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v

@[inherit_doc]
scoped infixr:73 " *ᵥ " => Matrix.mulVec
/-
**Matrix.mulVec_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mulVec_apply [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m) : (M *ᵥ v
) i = M.row i ⬝ᵥ v
参数：M : Matrix m n α；v : n -> α；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulVec_apply [Fintype n] (M : Matrix m n α) (v : n → α) (i : m) :
    (M *ᵥ v) i = M.row i ⬝ᵥ v := rfl
/-
**Matrix.mulVec_apply_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mulVec_apply_eq_sum [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m) : 
(M *ᵥ v) i = ∑ j : n, M i j * v j
参数：M : Matrix m n α；v : n -> α；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulVec_apply_eq_sum [Fintype n] (M : Matrix m n α) (v : n → α) (i : m) :
    (M *ᵥ v) i = ∑ j : n, M i j * v j := rfl

/--
`v ᵥ* M` (notation for `vecMul v M`) is the vector-matrix product of vector `v` and matrix `M`,
where `v` is seen as a row vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `v ᵥ* A ⬝ᵥ w ᵥ* B` is parsed as `(v ᵥ* A) ⬝ᵥ (w ᵥ* B)`.
-/
/-
**Matrix.vecMul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype m] → (m → α) → Matrix m n α → n → α
参数：m → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`v ᵥ* M` (notation for `vecMul v M`) is the vector-matrix product of vector `v` 
and matrix `M`,
where `v` is seen as a row vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotPr
oduct`,
so that `v ᵥ* A ⬝ᵥ w ᵥ* B` is parsed as `(v ᵥ* A) ⬝ᵥ (w ᵥ* B)`.
-/
def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j

@[inherit_doc]
scoped infixl:73 " ᵥ* " => Matrix.vecMul
/-
**Matrix.vecMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_apply [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n) : (v ᵥ* M
) i = v ⬝ᵥ M.col i
参数：v : m -> α；M : Matrix m n α；i : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vecMul_apply [Fintype m] (v : m → α) (M : Matrix m n α) (i : n) :
    (v ᵥ* M) i = v ⬝ᵥ M.col i := rfl
/-
**Matrix.vecMul_apply_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_apply_eq_sum [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n) : 
(v ᵥ* M) i = ∑ j : m, v j * M j i
参数：v : m -> α；M : Matrix m n α；i : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vecMul_apply_eq_sum [Fintype m] (v : m → α) (M : Matrix m n α) (i : n) :
    (v ᵥ* M) i = ∑ j : m, v j * M j i := rfl

/-- Left multiplication by a matrix, as an `AddMonoidHom` from vectors to vectors. -/
@[simps]
/-
**Matrix.mulVec.addMonoidHomLeft** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.mulVec`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [inst : NonUnitalNonAss
ocSemiring α] → [Fintype n] → (n → α) → Matrix m n α →+ m → α
参数：n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by a matrix, as an `AddMonoidHom` from vectors to vectors.
-/
def mulVec.addMonoidHomLeft [Fintype n] (v : n → α) : Matrix m n α →+ m → α where
  toFun M := M *ᵥ v
  map_zero' := by
    ext
    simp [mulVec]
  map_add' x y := by
    ext m
    apply add_dotProduct

/-- The `i`th row of the multiplication is the same as the `vecMul` with the `i`th row of `A`. -/
/-
**Matrix.mul_apply_eq_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_apply_eq_vecMul [Fintype n] (A : Matrix m n α) (B : Matrix n o α) (i :
 m) : (A * B) i = A i ᵥ* B
参数：A : Matrix m n α；B : Matrix n o α；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th row of the multiplication is the same as the `vecMul` with the `i`th r
ow of `A`.
-/
theorem mul_apply_eq_vecMul [Fintype n] (A : Matrix m n α) (B : Matrix n o α) (i : m) :
    (A * B) i = A i ᵥ* B :=
  rfl
/-
**Matrix.vecMul_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix m n α) : v ᵥ* M = ∑ i, 
v i • M i
参数：v : m -> α；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
-/
theorem vecMul_eq_sum [Fintype m] (v : m → α) (M : Matrix m n α) : v ᵥ* M = ∑ i, v i • M i :=
  (Finset.sum_fn ..).symm
/-
**Matrix.mulVec_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix m n α) : M *ᵥ v = ∑ i, 
MulOpposite.op (v i) • Mᵀ i
参数：v : n -> α；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
-/
theorem mulVec_eq_sum [Fintype n] (v : n → α) (M : Matrix m n α) :
    M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i :=
  (Finset.sum_fn ..).symm
/-
**Matrix.mulVec_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m -> α) (x : m) : (diag
onal v *ᵥ w) x = v x * w x
参数：v w : m -> α；x : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `diagonal_dotProduct`：diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v
 i * w i
-/
theorem mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    (diagonal v *ᵥ w) x = v x * w x :=
  diagonal_dotProduct v w x
/-
**Matrix.vecMul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m -> α) (x : m) : (v ᵥ*
 diagonal w) x = v x * w x
参数：v w : m -> α；x : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_diagonal'`：dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diag
onal w j i) = v i * w i
-/
theorem vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    (v ᵥ* diagonal w) x = v x * w x :=
  dotProduct_diagonal' v w x

/-- Associate the dot product of `mulVec` to the left. -/
/-
**Matrix.dotProduct_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m -> 
R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w
参数：v : m -> R；A : Matrix m n R；w : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…

--- 原说明 ---
Associate the dot product of `mulVec` to the left.
-/
theorem dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m → R)
    (A : Matrix m n R) (w : n → R) : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w := by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
/-
**Matrix.dot_mulVec_eq_sum_sum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：dot_mulVec_eq_sum_sum [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m
 -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ (A *ᵥ w) = ∑ j, ∑ i, v i * A i j *
 w j
参数：v : m -> R；A : Matrix m n R；w : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_eq_sum`：vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix
 m n α) : v ᵥ* M = ∑ i, v i • M i
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dot_mulVec_eq_sum_sum [Fintype n] [Fintype m] [NonUnitalSemiring R]
    (v : m → R) (A : Matrix m n R) (w : n → R) :
    v ⬝ᵥ (A *ᵥ w) = ∑ j, ∑ i, v i * A i j * w j := by
  simp_rw [dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]

@[simp]
/-
**Matrix.mulVec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 = 0
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 = 0 := by
  ext
  simp [mulVec]

@[simp]
/-
**Matrix.zero_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_vecMul [Fintype m] (A : Matrix m n α) : 0 ᵥ* A = 0
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dotProduct`：zero_dotProduct : 0 ⬝ᵥ v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_vecMul [Fintype m] (A : Matrix m n α) : 0 ᵥ* A = 0 := by
  ext
  simp [vecMul]

@[simp]
/-
**Matrix.zero_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_mulVec [Fintype n] (v : n -> α) : (0 : Matrix m n α) *ᵥ v = 0
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dotProduct'`：zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_mulVec [Fintype n] (v : n → α) : (0 : Matrix m n α) *ᵥ v = 0 := by
  ext
  simp [mulVec]

@[simp]
/-
**Matrix.vecMul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_zero [Fintype m] (v : m -> α) : v ᵥ* (0 : Matrix m n α) = 0
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_zero'`：dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_zero [Fintype m] (v : m → α) : v ᵥ* (0 : Matrix m n α) = 0 := by
  ext
  simp [vecMul]
/-
**Matrix.mulVec_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_add [Fintype n] (A : Matrix m n α) (x y : n -> α) : A *ᵥ (x + y) = 
A *ᵥ x + A *ᵥ y
参数：A : Matrix m n α；x y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_add`：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
-/
theorem mulVec_add [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y := by
  ext
  apply dotProduct_add
/-
**Matrix.add_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n -> α) : (A + B) *ᵥ x = 
A *ᵥ x + B *ᵥ x
参数：A B : Matrix m n α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_dotProduct`：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
-/
theorem add_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x := by
  ext
  apply add_dotProduct
/-
**Matrix.vecMul_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_add [Fintype m] (A B : Matrix m n α) (x : m -> α) : x ᵥ* (A + B) = 
x ᵥ* A + x ᵥ* B
参数：A B : Matrix m n α；x : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_add`：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
-/
theorem vecMul_add [Fintype m] (A B : Matrix m n α) (x : m → α) :
    x ᵥ* (A + B) = x ᵥ* A + x ᵥ* B := by
  ext
  apply dotProduct_add
/-
**Matrix.add_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_vecMul [Fintype m] (A : Matrix m n α) (x y : m -> α) : (x + y) ᵥ* A = 
x ᵥ* A + y ᵥ* A
参数：A : Matrix m n α；x y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_dotProduct`：add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
-/
theorem add_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    (x + y) ᵥ* A = x ᵥ* A + y ᵥ* A := by
  ext
  apply add_dotProduct
/-
**Matrix.mulVec_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommClass R α α] (M : Matri
x m n α) (b : R) (v : n -> α) : M *ᵥ (b • v) = b • M *ᵥ v
参数：M : Matrix m n α；b : R；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_smul`：dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m 
-> α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w)
-/
theorem mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommClass R α α]
    (M : Matrix m n α) (b : R) (v : n → α) :
    M *ᵥ (b • v) = b • M *ᵥ v := by
  ext
  exact dotProduct_smul _ _ _
/-
**Matrix.smul_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarTower R α α] (b : R) (M
 : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
参数：b : R；M : Matrix m n α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_dotProduct`：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m 
-> α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
-/
theorem smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (M : Matrix m n α) (v : n → α) :
    (b • M) *ᵥ v = b • M *ᵥ v := by
  ext
  exact smul_dotProduct _ _ _
/-
**Matrix.smul_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_vecMul [Fintype m] [DistribSMul R α] [IsScalarTower R α α] (b : R) (v
 : m -> α) (M : Matrix m n α) : (b • v) ᵥ* M = b • v ᵥ* M
参数：b : R；v : m -> α；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_dotProduct`：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m 
-> α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
-/
theorem smul_vecMul [Fintype m] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (v : m → α) (M : Matrix m n α) :
    (b • v) ᵥ* M = b • v ᵥ* M := by
  ext
  exact smul_dotProduct _ _ _
/-
**Matrix.vecMul_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_smul [Fintype m] [DistribSMul R α] [SMulCommClass R α α] (v : m -> 
α) (b : R) (M : Matrix m n α) : v ᵥ* (b • M) = b • v ᵥ* M
参数：v : m -> α；b : R；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_smul`：dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m 
-> α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w)
-/
theorem vecMul_smul [Fintype m] [DistribSMul R α] [SMulCommClass R α α]
    (v : m → α) (b : R) (M : Matrix m n α) :
    v ᵥ* (b • M) = b • v ᵥ* M := by
  ext
  exact dotProduct_smul _ _ _

@[simp]
/-
**Matrix.mulVec_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M
 : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = MulOpposite.op x • M.col
 j
参数：M : Matrix m n R；j : n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_single`：dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i 
x = v i * x
-/
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M *ᵥ Pi.single j x = MulOpposite.op x • M.col j :=
  funext fun _ => dotProduct_single _ _ _

@[simp]
/-
**Matrix.single_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M
 : Matrix m n R) (i : m) (x : R) : Pi.single i x ᵥ* M = x • M.row i
参数：M : Matrix m n R；i : m；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
-/
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : Pi.single i x ᵥ* M = x • M.row i :=
  funext fun _ => single_dotProduct _ _ _
/-
**Matrix.mulVec_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring R] (M : Ma
trix m n R) (j : n) : M *ᵥ Pi.single j 1 = M.col j
参数：M : Matrix m n R；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring R]
    (M : Matrix m n R) (j : n) :
    M *ᵥ Pi.single j 1 = M.col j := by ext; simp
/-
**Matrix.single_one_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_one_vecMul [Fintype m] [DecidableEq m] [NonAssocSemiring R] (i : m)
 (M : Matrix m n R) : Pi.single i 1 ᵥ* M = M.row i
参数：i : m；M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.single_vecMul`：single_vecMul [Fintype m] [DecidableEq m] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (i : m) (x : R) : Pi.single i x ᵥ* M = 
x • M.row …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_one_vecMul [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (i : m) (M : Matrix m n R) :
    Pi.single i 1 ᵥ* M = M.row i := by ext; simp
/-
**Matrix.diagonal_mulVec_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemir
ing R] (v : n -> R) (j : n) (x : R) : diagonal v *ᵥ Pi.single j x = Pi.single j 
(v j * x)
参数：v : n -> R；j : n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : diagonal v *ᵥ Pi.single j x = Pi.single j (v j * x) := by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i
/-
**Matrix.single_vecMul_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemir
ing R] (v : n -> R) (j : n) (x : R) : (Pi.single j x) ᵥ* (diagonal v) = Pi.singl
e j (x * v j)
参数：v : n -> R；j : n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMul_diagonal`：vecMul_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (v ᵥ* diagonal w) x = v x * w x
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : (Pi.single j x) ᵥ* (diagonal v) = Pi.single j (x * v j) := by
  ext i
  rw [vecMul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

@[simp]
/-
**Matrix.vecMul_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α) (M : Matrix m n α) (N :
 Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
参数：v : m -> α；M : Matrix m n α；N : Matrix n o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_assoc`：dotProduct_assoc [NonUnitalSemiring α] (u : m -> α) (w
 : n -> α) (v : Matrix m n α) : (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i
 => v …
-/
theorem vecMul_vecMul [Fintype n] [Fintype m] (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
    v ᵥ* M ᵥ* N = v ᵥ* (M * N) := by
  ext
  apply dotProduct_assoc

@[simp]
/-
**Matrix.mulVec_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α) (M : Matrix m n α) (N :
 Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
参数：v : o -> α；M : Matrix m n α；N : Matrix n o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dotProduct_assoc`：dotProduct_assoc [NonUnitalSemiring α] (u : m -> α) (w
 : n -> α) (v : Matrix m n α) : (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i
 => v …
-/
theorem mulVec_mulVec [Fintype n] [Fintype o] (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
    M *ᵥ N *ᵥ v = (M * N) *ᵥ v := by
  ext
  symm
  apply dotProduct_assoc
/-
**Matrix.mul_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) : (A * B * C) i
 j = A i ⬝ᵥ B *ᵥ (Cᵀ j)
参数：A B C : Matrix n n α；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A * B * C) i j = A i ⬝ᵥ B *ᵥ (Cᵀ j) := by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]
/-
**Matrix.vecMul_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_vecMulVec [Fintype m] (u v : m -> α) (w : n -> α) : u ᵥ* vecMulVec 
v w = (u ⬝ᵥ v) • w
参数：u v : m -> α；w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_vecMulVec [Fintype m] (u v : m → α) (w : n → α) :
    u ᵥ* vecMulVec v w = (u ⬝ᵥ v) • w := by
  ext i
  simp [vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]
/-
**Matrix.vecMulVec_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_mulVec [Fintype n] (u : m -> α) (v w : n -> α) : vecMulVec u v *
ᵥ w = MulOpposite.op (v ⬝ᵥ w) • u
参数：u : m -> α；v w : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.unop_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → Mᵐᵒᵖ),   MulOpposite.unop (∑ x ∈ s, f x) = ∑ x ∈ s, Mu
lOppo…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMulVec_mulVec [Fintype n] (u : m → α) (v w : n → α) :
    vecMulVec u v *ᵥ w = MulOpposite.op (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]
/-
**Matrix.mul_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_vecMulVec [Fintype m] (M : Matrix l m α) (x : m -> α) (y : n -> α) : M
 * vecMulVec x y = vecMulVec (M *ᵥ x) y
参数：M : Matrix l m α；x : m -> α；y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_vecMulVec [Fintype m] (M : Matrix l m α) (x : m → α) (y : n → α) :
    M * vecMulVec x y = vecMulVec (M *ᵥ x) y := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
/-
**Matrix.vecMulVec_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_mul [Fintype m] (x : l -> α) (y : m -> α) (M : Matrix m n α) : v
ecMulVec x y * M = vecMulVec x (y ᵥ* M)
参数：x : l -> α；y : m -> α；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMulVec_mul [Fintype m] (x : l → α) (y : m → α) (M : Matrix m n α) :
    vecMulVec x y * M = vecMulVec x (y ᵥ* M) := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]
/-
**Matrix.vecMulVec_mul_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_mul_vecMulVec [Fintype m] (u : l -> α) (v w : m -> α) (x : n -> 
α) : vecMulVec u v * vecMulVec w x = vecMulVec u ((v ⬝ᵥ w) • x)
参数：u : l -> α；v w : m -> α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMulVec_mul`：vecMulVec_mul [Fintype m] (x : l -> α) (y : m -> α
) (M : Matrix m n α) : vecMulVec x y * M = vecMulVec x (y ᵥ* M)
· 使用定理 `Matrix.vecMul_vecMulVec`：vecMul_vecMulVec [Fintype m] (u v : m -> α) (w 
: n -> α) : u ᵥ* vecMulVec v w = (u ⬝ᵥ v) • w
-/
theorem vecMulVec_mul_vecMulVec [Fintype m] (u : l → α) (v w : m → α) (x : n → α) :
    vecMulVec u v * vecMulVec w x = vecMulVec u ((v ⬝ᵥ w) • x) := by
  rw [vecMulVec_mul, vecMul_vecMulVec]
/-
**Matrix.mul_right_injective_iff_mulVec_injective** 是 Mathlib 中的一个引理，位于命名空间 `Mat
rix`。
形式化陈述：mul_right_injective_iff_mulVec_injective [Fintype m] [Nonempty n] {A : Mat
rix l m α} : Function.Injective (fun B : Matrix m n α => A * B) ↔ Function.Injec
tive A.mulVec
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
· 使用引理 `Matrix.ext_col`：ext_col {A B : Matrix m n α} (h : forall j, A.col j = B.
col j) : A = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma mul_right_injective_iff_mulVec_injective [Fintype m] [Nonempty n] {A : Matrix l m α} :
    Function.Injective (fun B : Matrix m n α => A * B) ↔ Function.Injective A.mulVec := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_col fun j => ha congr(($hBC).col j)⟩
  inhabit n
  -- `replicateRow` is not available yet
  suffices (of fun i j => v i) = (of fun i j => w i) from
    funext fun i => congrFun₂ this i (default : n)
  exact ha <| ext fun _ _ => congrFun hvw _
/-
**Matrix.mul_left_injective_iff_vecMul_injective** 是 Mathlib 中的一个引理，位于命名空间 `Matr
ix`。
形式化陈述：mul_left_injective_iff_vecMul_injective [Nonempty l] [Fintype m] {A : Matr
ix m n α} : Function.Injective (fun B : Matrix l m α => B * A) ↔ Function.Inject
ive A.vecMul
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
· 使用引理 `Matrix.ext_row`：ext_row {A B : Matrix m n α} (h : forall i, A.row i = B.
row i) : A = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma mul_left_injective_iff_vecMul_injective [Nonempty l] [Fintype m] {A : Matrix m n α} :
    Function.Injective (fun B : Matrix l m α => B * A) ↔ Function.Injective A.vecMul := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_row fun i => ha congr(($hBC).row i)⟩
  inhabit l
  --  `replicateCol` is not available yet
  suffices (of fun i j => v j) = (of fun i j => w j) from
    funext fun j => congrFun₂ this (default : l) j
  exact ha <| ext fun _ _ => congrFun hvw _
/-
**Matrix.isLeftRegular_iff_mulVec_injective** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isLeftRegular_iff_mulVec_injective [Fintype m] {A : Matrix m m α} : IsLeft
Regular A ↔ Function.Injective A.mulVec
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Matrix.mul_right_injective_iff_mulVec_injective`：mul_right_injective_iff
_mulVec_injective [Fintype m] [Nonempty n] {A : Matrix l m α} : Function.Injecti
ve (fun B : Matrix m n α => A * B) ↔ …
-/
lemma isLeftRegular_iff_mulVec_injective [Fintype m] {A : Matrix m m α} :
    IsLeftRegular A ↔ Function.Injective A.mulVec := by
  cases isEmpty_or_nonempty m
  · simp [IsLeftRegular, Function.injective_of_subsingleton]
  exact mul_right_injective_iff_mulVec_injective
/-
**Matrix.isRightRegular_iff_vecMul_injective** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isRightRegular_iff_vecMul_injective [Fintype m] {A : Matrix m m α} : IsRig
htRegular A ↔ Function.Injective A.vecMul
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Matrix.mul_left_injective_iff_vecMul_injective`：mul_left_injective_iff_v
ecMul_injective [Nonempty l] [Fintype m] {A : Matrix m n α} : Function.Injective
 (fun B : Matrix l m α => B * A) ↔ F…
-/
lemma isRightRegular_iff_vecMul_injective [Fintype m] {A : Matrix m m α} :
    IsRightRegular A ↔ Function.Injective A.vecMul := by
  cases isEmpty_or_nonempty m
  · simp [IsRightRegular, Function.injective_of_subsingleton]
  exact mul_left_injective_iff_vecMul_injective

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.mulVec_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_one [Fintype n] (A : Matrix m n α) : A *ᵥ 1 = ∑ j, Aᵀ j
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulVec_one [Fintype n] (A : Matrix m n α) : A *ᵥ 1 = ∑ j, Aᵀ j := by
  ext; simp [mulVec, dotProduct]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.one_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_vecMul [Fintype m] (A : Matrix m n α) : 1 ᵥ* A = ∑ i, A i
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_vecMul [Fintype m] (A : Matrix m n α) : 1 ᵥ* A = ∑ i, A i := by
  ext; simp [vecMul, dotProduct]
/-
**Matrix.ext_of_mulVec_single** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ext_of_mulVec_single [DecidableEq n] [Fintype n] {M N : Matrix m n α} (h :
 forall i, M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1) : M = N
参数：h : forall i, M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_single_one`：mulVec_single_one [Fintype n] [DecidableEq n] 
[NonAssocSemiring R] (M : Matrix m n R) (j : n) : M *ᵥ Pi.single j 1 = M.col j
-/
lemma ext_of_mulVec_single [DecidableEq n] [Fintype n] {M N : Matrix m n α}
    (h : ∀ i, M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1) :
    M = N := by
  ext i j
  simp_rw [mulVec_single_one] at h
  exact congrFun (h j) i
/-
**Matrix.ext_of_single_vecMul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ext_of_single_vecMul [DecidableEq m] [Fintype m] {M N : Matrix m n α} (h :
 forall i, Pi.single i 1 ᵥ* M = Pi.single i 1 ᵥ* N) : M = N
参数：h : forall i, Pi.single i 1 ᵥ* M = Pi.single i 1 ᵥ* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_one_vecMul`：single_one_vecMul [Fintype m] [DecidableEq m] 
[NonAssocSemiring R] (i : m) (M : Matrix m n R) : Pi.single i 1 ᵥ* M = M.row i
-/
lemma ext_of_single_vecMul [DecidableEq m] [Fintype m] {M N : Matrix m n α}
    (h : ∀ i, Pi.single i 1 ᵥ* M = Pi.single i 1 ᵥ* N) :
    M = N := by
  ext i j
  simp_rw [single_one_vecMul] at h
  exact congrFun (h i) j
/-
**Matrix.mulVec_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_injective [Fintype n] : (mulVec : Matrix m n α -> _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
-/
theorem mulVec_injective [Fintype n] : (mulVec : Matrix m n α → _).Injective := by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single j 1) i
/-
**Matrix.ext_iff_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_mulVec [Fintype n] {A B : Matrix m n α} : A = B ↔ forall v, A *ᵥ v
 = B *ᵥ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.mulVec_injective`：mulVec_injective [Fintype n] : (mulVec : Matrix
 m n α -> _).Injective
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem ext_iff_mulVec [Fintype n] {A B : Matrix m n α} : A = B ↔ ∀ v, A *ᵥ v = B *ᵥ v :=
  mulVec_injective.eq_iff.symm.trans funext_iff
/-
**Matrix.vecMul_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_injective [Fintype m] : (·.vecMul : Matrix m n α -> _).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.single_vecMul`：single_vecMul [Fintype m] [DecidableEq m] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (i : m) (x : R) : Pi.single i x ᵥ* M = 
x • M.row …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
-/
theorem vecMul_injective [Fintype m] : (·.vecMul : Matrix m n α → _).Injective := by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single i 1) j
/-
**Matrix.ext_iff_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_vecMul [Fintype m] {A B : Matrix m n α} : A = B ↔ forall v, v ᵥ* A
 = v ᵥ* B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.vecMul_injective`：vecMul_injective [Fintype m] : (·.vecMul : Matr
ix m n α -> _).Injective
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem ext_iff_vecMul [Fintype m] {A B : Matrix m n α} : A = B ↔ ∀ v, v ᵥ* A = v ᵥ* B :=
  vecMul_injective.eq_iff.symm.trans funext_iff

variable [Fintype m] [DecidableEq m]

@[simp]
/-
**Matrix.one_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_mulVec (v : m -> α) : 1 *ᵥ v = v
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_mulVec (v : m → α) : 1 *ᵥ v = v := by
  ext
  rw [← diagonal_one, mulVec_diagonal, one_mul]

@[simp]
/-
**Matrix.vecMul_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_one (v : m -> α) : v ᵥ* 1 = v
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `Matrix.vecMul_diagonal`：vecMul_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (v ᵥ* diagonal w) x = v x * w x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem vecMul_one (v : m → α) : v ᵥ* 1 = v := by
  ext
  rw [← diagonal_one, vecMul_diagonal, mul_one]

@[simp]
/-
**Matrix.diagonal_const_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_const_mulVec (x : α) (v : m -> α) : (diagonal fun _ => x) *ᵥ v = 
x • v
参数：x : α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonal_const_mulVec (x : α) (v : m → α) :
    (diagonal fun _ => x) *ᵥ v = x • v := by
  ext; simp [mulVec_diagonal]

@[simp]
/-
**Matrix.vecMul_diagonal_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_diagonal_const (x : α) (v : m -> α) : v ᵥ* (diagonal fun _ => x) = 
MulOpposite.op x • v
参数：x : α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMul_diagonal`：vecMul_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (v ᵥ* diagonal w) x = v x * w x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_diagonal_const (x : α) (v : m → α) :
    v ᵥ* (diagonal fun _ => x) = MulOpposite.op x • v := by
  ext; simp [vecMul_diagonal]

@[simp]
/-
**Matrix.natCast_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：natCast_mulVec (x : Nat) (v : m -> α) : x *ᵥ v = (x : α) • v
参数：x : Nat；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_const_mulVec`：diagonal_const_mulVec (x : α) (v : m -> α)
 : (diagonal fun _ => x) *ᵥ v = x • v
-/
theorem natCast_mulVec (x : ℕ) (v : m → α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
/-
**Matrix.vecMul_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_natCast (x : Nat) (v : m -> α) : v ᵥ* x = MulOpposite.op (x : α) • 
v
参数：x : Nat；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vecMul_diagonal_const`：vecMul_diagonal_const (x : α) (v : m -> α)
 : v ᵥ* (diagonal fun _ => x) = MulOpposite.op x • v
-/
theorem vecMul_natCast (x : ℕ) (v : m → α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _


@[simp]
/-
**Matrix.ofNat_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofNat_mulVec (x : Nat) [x.AtLeastTwo] (v : m -> α) : ofNat(x) *ᵥ v = (OfNa
t.ofNat x : α) • v
参数：x : Nat；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.natCast_mulVec`：natCast_mulVec (x : Nat) (v : m -> α) : x *ᵥ v = 
(x : α) • v
-/
theorem ofNat_mulVec (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    ofNat(x) *ᵥ v = (OfNat.ofNat x : α) • v :=
  natCast_mulVec _ _

@[simp]
/-
**Matrix.vecMul_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_ofNat (x : Nat) [x.AtLeastTwo] (v : m -> α) : v ᵥ* ofNat(x) = MulOp
posite.op (OfNat.ofNat x : α) • v
参数：x : Nat；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vecMul_natCast`：vecMul_natCast (x : Nat) (v : m -> α) : v ᵥ* x = 
MulOpposite.op (x : α) • v
-/
theorem vecMul_ofNat (x : ℕ) [x.AtLeastTwo] (v : m → α) :
    v ᵥ* ofNat(x) = MulOpposite.op (OfNat.ofNat x : α) • v :=
  vecMul_natCast _ _

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-
**Matrix.neg_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：neg_vecMul [Fintype m] (v : m -> α) (A : Matrix m n α) : (-v) ᵥ* A = -(v ᵥ
* A)
参数：v : m -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_dotProduct`：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
-/
theorem neg_vecMul [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* A = -(v ᵥ* A) := by
  ext
  apply neg_dotProduct
/-
**Matrix.vecMul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α) : v ᵥ* (-A) = -(v ᵥ
* A)
参数：v : m -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_neg`：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
-/
theorem vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : v ᵥ* (-A) = -(v ᵥ* A) := by
  ext
  apply dotProduct_neg
/-
**Matrix.neg_vecMul_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：neg_vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α) : (-v) ᵥ* (-A) 
= v ᵥ* A
参数：v : m -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecMul_neg`：vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α
) : v ᵥ* (-A) = -(v ᵥ* A)
· 使用定理 `Matrix.neg_vecMul`：neg_vecMul [Fintype m] (v : m -> α) (A : Matrix m n α
) : (-v) ᵥ* A = -(v ᵥ* A)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : (-v) ᵥ* (-A) = v ᵥ* A := by
  rw [vecMul_neg, neg_vecMul, neg_neg]
/-
**Matrix.neg_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：neg_mulVec [Fintype n] (v : n -> α) (A : Matrix m n α) : (-A) *ᵥ v = -(A *
ᵥ v)
参数：v : n -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_dotProduct`：neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
-/
theorem neg_mulVec [Fintype n] (v : n → α) (A : Matrix m n α) : (-A) *ᵥ v = -(A *ᵥ v) := by
  ext
  apply neg_dotProduct
/-
**Matrix.mulVec_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_neg [Fintype n] (v : n -> α) (A : Matrix m n α) : A *ᵥ (-v) = -(A *
ᵥ v)
参数：v : n -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_neg`：dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
-/
theorem mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : A *ᵥ (-v) = -(A *ᵥ v) := by
  ext
  apply dotProduct_neg
/-
**Matrix.neg_mulVec_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：neg_mulVec_neg [Fintype n] (v : n -> α) (A : Matrix m n α) : (-A) *ᵥ (-v) 
= A *ᵥ v
参数：v : n -> α；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_neg`：mulVec_neg [Fintype n] (v : n -> α) (A : Matrix m n α
) : A *ᵥ (-v) = -(A *ᵥ v)
· 使用定理 `Matrix.neg_mulVec`：neg_mulVec [Fintype n] (v : n -> α) (A : Matrix m n α
) : (-A) *ᵥ v = -(A *ᵥ v)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : (-A) *ᵥ (-v) = A *ᵥ v := by
  rw [mulVec_neg, neg_mulVec, neg_neg]
/-
**Matrix.mulVec_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n -> α) : A *ᵥ (x - y) = 
A *ᵥ x - A *ᵥ y
参数：A : Matrix m n α；x y : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_sub`：dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w
-/
theorem mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y := by
  ext
  apply dotProduct_sub
/-
**Matrix.sub_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n -> α) : (A - B) *ᵥ x = 
A *ᵥ x - B *ᵥ x
参数：A B : Matrix m n α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `Matrix.neg_mulVec`：neg_mulVec [Fintype n] (v : n -> α) (A : Matrix m n α
) : (-A) *ᵥ v = -(A *ᵥ v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A - B) *ᵥ x = A *ᵥ x - B *ᵥ x := by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]
/-
**Matrix.vecMul_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m -> α) : x ᵥ* (A - B) = 
x ᵥ* A - x ᵥ* B
参数：A B : Matrix m n α；x : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.vecMul_add`：vecMul_add [Fintype m] (A B : Matrix m n α) (x : m ->
 α) : x ᵥ* (A + B) = x ᵥ* A + x ᵥ* B
· 使用定理 `Matrix.vecMul_neg`：vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α
) : v ᵥ* (-A) = -(v ᵥ* A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m → α) :
    x ᵥ* (A - B) = x ᵥ* A - x ᵥ* B := by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]
/-
**Matrix.sub_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sub_vecMul [Fintype m] (A : Matrix m n α) (x y : m -> α) : (x - y) ᵥ* A = 
x ᵥ* A - y ᵥ* A
参数：A : Matrix m n α；x y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_dotProduct`：sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w
-/
theorem sub_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    (x - y) ᵥ* A = x ᵥ* A - y ᵥ* A := by
  ext
  apply sub_dotProduct
/-
**Matrix.sub_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sub_vecMulVec (w₁ w₂ : m -> α) (v : n -> α) : vecMulVec (w₁ - w₂) v = vecM
ulVec w₁ v - vecMulVec w₂ v
参数：w₁ w₂ : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
-/
theorem sub_vecMulVec (w₁ w₂ : m → α) (v : n → α) :
    vecMulVec (w₁ - w₂) v = vecMulVec w₁ v - vecMulVec w₂ v :=
  ext fun _ _ => sub_mul _ _ _
/-
**Matrix.vecMulVec_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMulVec_sub (w : m -> α) (v₁ v₂ : n -> α) : vecMulVec w (v₁ - v₂) = vecM
ulVec w v₁ - vecMulVec w v₂
参数：w : m -> α；v₁ v₂ : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
-/
theorem vecMulVec_sub (w : m → α) (v₁ v₂ : n → α) :
    vecMulVec w (v₁ - v₂) = vecMulVec w v₁ - vecMulVec w v₂ :=
  ext fun _ _ => mul_sub _ _ _

end NonUnitalNonAssocRing

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

/-
**Matrix.mulVec_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m -> α) : Aᵀ *ᵥ x = x
 ᵥ* A
参数：A : Matrix m n α；x : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
-/
theorem mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m → α) : Aᵀ *ᵥ x = x ᵥ* A := by
  ext
  apply dotProduct_comm
/-
**Matrix.vecMul_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n -> α) : x ᵥ* Aᵀ = A
 *ᵥ x
参数：A : Matrix m n α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
-/
theorem vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n → α) : x ᵥ* Aᵀ = A *ᵥ x := by
  ext
  apply dotProduct_comm

/-- Bilinear form identity: `x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x` for commutative semirings. -/
/-
**Matrix.dotProduct_transpose_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_transpose_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (x 
: n -> α) (y : m -> α) : x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x
参数：A : Matrix m n α；x : n -> α；y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x

--- 原说明 ---
Bilinear form identity: `x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x` for commutative semirings.
-/
theorem dotProduct_transpose_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (x : n → α)
    (y : m → α) : x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec, dotProduct_comm, vecMul_transpose]

/-- Bilinear form identity: `(x ᵥ* Aᵀ) ⬝ᵥ y = (y ᵥ* A) ⬝ᵥ x` for commutative semirings. -/
/-
**Matrix.dotProduct_vecMul_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_vecMul_transpose [Fintype m] [Fintype n] (A : Matrix m n α) (x 
: n -> α) (y : m -> α) : (x ᵥ* Aᵀ) ⬝ᵥ y = (y ᵥ* A) ⬝ᵥ x
参数：A : Matrix m n α；x : n -> α；y : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Matrix.dotProduct_transpose_mulVec`：dotProduct_transpose_mulVec [Fintype
 m] [Fintype n] (A : Matrix m n α) (x : n -> α) (y : m -> α) : x ⬝ᵥ Aᵀ *ᵥ y = y 
⬝ᵥ A *ᵥ x

--- 原说明 ---
Bilinear form identity: `(x ᵥ* Aᵀ) ⬝ᵥ y = (y ᵥ* A) ⬝ᵥ x` for commutative semirin
gs.
-/
theorem dotProduct_vecMul_transpose [Fintype m] [Fintype n] (A : Matrix m n α) (x : n → α)
    (y : m → α) : (x ᵥ* Aᵀ) ⬝ᵥ y = (y ᵥ* A) ⬝ᵥ x := by
  simpa [dotProduct_mulVec] using dotProduct_transpose_mulVec (A := A) (x := x) (y := y)
/-
**Matrix.mulVec_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α
) (x : o -> α) : A *ᵥ (x ᵥ* B) = (A * Bᵀ) *ᵥ x
参数：A : Matrix m n α；B : Matrix o n α；x : o -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.mulVec_transpose`：mulVec_transpose [Fintype m] (A : Matrix m n α)
 (x : m -> α) : Aᵀ *ᵥ x = x ᵥ* A
-/
theorem mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o → α) :
    A *ᵥ (x ᵥ* B) = (A * Bᵀ) *ᵥ x := by rw [← mulVec_mulVec, mulVec_transpose]
/-
**Matrix.vecMul_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α
) (x : n -> α) : (A *ᵥ x) ᵥ* B = x ᵥ* (Aᵀ * B)
参数：A : Matrix m n α；B : Matrix m o α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
-/
theorem vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n → α) :
    (A *ᵥ x) ᵥ* B = x ᵥ* (Aᵀ * B) := by rw [← vecMul_vecMul, vecMul_transpose]

end NonUnitalCommSemiring

section Semiring

variable [Semiring R]

/-
**Matrix.mulVec_injective_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：mulVec_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R} 
(ha : IsUnit A) : Function.Injective A.mulVec
参数：ha : IsUnit A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.isLeftRegular_iff_mulVec_injective`：isLeftRegular_iff_mulVec_inje
ctive [Fintype m] {A : Matrix m m α} : IsLeftRegular A ↔ Function.Injective A.mu
lVec
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
-/
lemma mulVec_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.mulVec :=
  isLeftRegular_iff_mulVec_injective.1 ha.isRegular.left
/-
**Matrix.vecMul_injective_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vecMul_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R} 
(ha : IsUnit A) : Function.Injective A.vecMul
参数：ha : IsUnit A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.isRightRegular_iff_vecMul_injective`：isRightRegular_iff_vecMul_in
jective [Fintype m] {A : Matrix m m α} : IsRightRegular A ↔ Function.Injective A
.vecMul
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
-/
lemma vecMul_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.vecMul :=
  isRightRegular_iff_vecMul_injective.1 ha.isRegular.right
/-
**Matrix.pow_row_eq_zero_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：pow_row_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l 
: Nat} {i : n} (h : (M ^ k).row i = 0) (h' : k <= l) : (M ^ l).row i = 0
参数：h : (M ^ k).row i = 0；h' : k <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.single_one_vecMul`：single_one_vecMul [Fintype m] [DecidableEq m] 
[NonAssocSemiring R] (i : m) (M : Matrix m n R) : Pi.single i 1 ᵥ* M = M.row i
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.zero_vecMul`：zero_vecMul [Fintype m] (A : Matrix m n α) : 0 ᵥ* A 
= 0
-/
lemma pow_row_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : ℕ} {i : n}
    (h : (M ^ k).row i = 0) (h' : k ≤ l) :
    (M ^ l).row i = 0 := by
  replace h' : l = k + (l - k) := by lia
  rw [← single_one_vecMul] at h ⊢
  rw [h', pow_add, ← vecMul_vecMul, h, zero_vecMul]
/-
**Matrix.pow_col_eq_zero_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：pow_col_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l 
: Nat} {i : n} (h : (M ^ k).col i = 0) (h' : k <= l) : (M ^ l).col i = 0
参数：h : (M ^ k).col i = 0；h' : k <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_single_one`：mulVec_single_one [Fintype n] [DecidableEq n] 
[NonAssocSemiring R] (M : Matrix m n R) (j : n) : M *ᵥ Pi.single j 1 = M.col j
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.mulVec_zero`：mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 
= 0
-/
lemma pow_col_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : ℕ} {i : n}
    (h : (M ^ k).col i = 0) (h' : k ≤ l) :
    (M ^ l).col i = 0 := by
  replace h' : l = (l - k) + k := by lia
  rw [← mulVec_single_one] at h ⊢
  rw [h', pow_add, ← mulVec_mulVec, h, mulVec_zero]

end Semiring

section NonAssocRing

variable [NonAssocRing α]

variable [Fintype m] [DecidableEq m]

@[simp]
/-
**Matrix.intCast_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：intCast_mulVec (x : Int) (v : m -> α) : x *ᵥ v = (x : α) • v
参数：x : Int；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_const_mulVec`：diagonal_const_mulVec (x : α) (v : m -> α)
 : (diagonal fun _ => x) *ᵥ v = x • v
-/
theorem intCast_mulVec (x : ℤ) (v : m → α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
/-
**Matrix.vecMul_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_intCast (x : Int) (v : m -> α) : v ᵥ* x = MulOpposite.op (x : α) • 
v
参数：x : Int；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vecMul_diagonal_const`：vecMul_diagonal_const (x : α) (v : m -> α)
 : v ᵥ* (diagonal fun _ => x) = MulOpposite.op x • v
-/
theorem vecMul_intCast (x : ℤ) (v : m → α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _

end NonAssocRing

section Transpose

open Matrix

@[simp]
/-
**Matrix.transpose_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_mul [AddCommMonoid α] [CommMagma α] [Fintype n] (M : Matrix m n 
α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
参数：M : Matrix m n α；N : Matrix n l α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
-/
theorem transpose_mul [AddCommMonoid α] [CommMagma α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext
  apply dotProduct_comm

end Transpose

/-
**Matrix.submatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Typ
e*} (M : Matrix m n α) (N : Matrix n p α) (e₁ : l -> m) (e₂ : o -> n) (e₃ : q ->
 p) (he₂ : Function.Bijective e₂) : (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ 
* N.submatrix e₂ e₃
参数：M : Matrix m n α；N : Matrix n p α；e₁ : l -> m；e₂ : o -> n；e₃ : q -> p；he₂ : F
unction.Bijective e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
-/
theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
    (he₂ : Function.Bijective e₂) :
    (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ * N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/

@[simp]
/-
**Matrix.submatrix_mul_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q
 : Type*} (M : Matrix m n α) (N : Matrix n p α) (e₁ : l -> m) (e₂ : o ≃ n) (e₃ :
 q -> p) : M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃
参数：M : Matrix m n α；N : Matrix n p α；e₁ : l -> m；e₂ : o ≃ n；e₃ : q -> p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.submatrix_mul`：submatrix_mul [Fintype n] [Fintype o] [Mul α] [Add
CommMonoid α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e₁ : l -> m) 
(e₂ : o ->…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
`simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, a
nd `Matrix.mul`
for when the mappings are bundled.
-/
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) :
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm
/-
**Matrix.submatrix_mulVec_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring 
α] (M : Matrix m n α) (v : o -> α) (e₁ : l -> m) (e₂ : o ≃ n) : M.submatrix e₁ e
₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁
参数：M : Matrix m n α；v : o -> α；e₁ : l -> m；e₂ : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dotProduct_comp_equiv_symm`：dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝
ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x
-/
theorem submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : o → α) (e₁ : l → m) (e₂ : o ≃ n) :
    M.submatrix e₁ e₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁ :=
  funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

@[simp]
/-
**Matrix.submatrix_id_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_id_mul_left [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p
 : Type*} (M : Matrix m n α) (N : Matrix o p α) (e₁ : l -> m) (e₂ : n ≃ o) : M.s
ubmatrix e₁ id * N.submatrix e₂ id = M.submatrix e₁ e₂.symm * N
参数：M : Matrix m n α；N : Matrix o p α；e₁ : l -> m；e₂ : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submatrix_id_mul_left [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l → m) (e₂ : n ≃ o) :
    M.submatrix e₁ id * N.submatrix e₂ id = M.submatrix e₁ e₂.symm * N := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

@[simp]
/-
**Matrix.submatrix_id_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_id_mul_right [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {
p : Type*} (M : Matrix m n α) (N : Matrix o p α) (e₁ : l -> p) (e₂ : o ≃ n) : M.
submatrix id e₂ * N.submatrix id e₁ = M * N.submatrix e₂.symm e₁
参数：M : Matrix m n α；N : Matrix o p α；e₁ : l -> p；e₂ : o ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submatrix_id_mul_right [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l → p) (e₂ : o ≃ n) :
    M.submatrix id e₂ * N.submatrix id e₁ = M * N.submatrix e₂.symm e₁ := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]
/-
**Matrix.submatrix_vecMul_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_vecMul_equiv [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring 
α] (M : Matrix m n α) (v : l -> α) (e₁ : l ≃ m) (e₂ : o -> n) : v ᵥ* M.submatrix
 e₁ e₂ = ((v ∘ e₁.symm) ᵥ* M) ∘ e₂
参数：M : Matrix m n α；v : l -> α；e₁ : l ≃ m；e₂ : o -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comp_equiv_symm_dotProduct`：comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘
 e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e
-/
theorem submatrix_vecMul_equiv [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : l → α) (e₁ : l ≃ m) (e₂ : o → n) :
    v ᵥ* M.submatrix e₁ e₂ = ((v ∘ e₁.symm) ᵥ* M) ∘ e₂ :=
  funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)
/-
**Matrix.mul_submatrix_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_submatrix_one [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq
 o] (e₁ : n ≃ o) (e₂ : l -> o) (M : Matrix m n α) : M * (1 : Matrix o o α).subma
trix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂)
参数：e₁ : n ≃ o；e₂ : l -> o；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_one`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   (M : Matrix m n
 α),…
-/
theorem mul_submatrix_one [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
    (e₂ : l → o) (M : Matrix m n α) :
    M * (1 : Matrix o o α).submatrix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂) := by
  cases nonempty_fintype o
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [A, Matrix.mul_one, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]
/-
**Matrix.one_submatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：one_submatrix_mul [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq
 o] (e₁ : l -> o) (e₂ : m ≃ o) (M : Matrix m n α) : ((1 : Matrix o o α).submatri
x e₁ e₂) * M = submatrix M (e₂.symm ∘ e₁) id
参数：e₁ : l -> o；e₂ : m ≃ o；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
-/
theorem one_submatrix_mul [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l → o)
    (e₂ : m ≃ o) (M : Matrix m n α) :
    ((1 : Matrix o o α).submatrix e₁ e₂) * M = submatrix M (e₂.symm ∘ e₁) id := by
  cases nonempty_fintype o
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [A, Matrix.one_mul, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]
/-
**Matrix.submatrix_mul_transpose_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α
] [Mul α] (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id 
= M * Mᵀ
参数：e : m ≃ n；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
-/
theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id = M * Mᵀ := by
  rw [submatrix_mul_equiv, submatrix_id_id]

variable (m n R : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [MulOne R] [AddCommMonoid R]
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsStablyFiniteRing R] : IsDedekindFiniteMonoid (Matrix n n R) :=
  let e := Fintype.equivFin n
  let f := MonoidHom.mk ⟨reindex (α := R) e e, submatrix_one_equiv _⟩
    fun _ _ ↦ (submatrix_mul_equiv ..).symm
  .of_injective f (reindex e e).injective

variable {m n R} in
/-- A version of `mul_eq_one_comm` that works for square matrices with rectangular types. -/
/-
**Matrix.mul_eq_one_comm_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_eq_one_comm_of_equiv [IsStablyFiniteRing R] {A : Matrix m n R} {B : Ma
trix n m R} (e : m ≃ n) : A * B = 1 ↔ B * A = 1
参数：e : m ≃ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Matrix.submatrix_one_equiv`：submatrix_one_equiv [Zero α] [One α] [Decida
bleEq m] [DecidableEq l] (e : l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `mul_eq_one_comm`：∀ {M : Type u_2} [inst : MulOne M] [IsDedekindFiniteMon
oid M] {a b : M}, a * b = 1 ↔ b * a = 1
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A version of `mul_eq_one_comm` that works for square matrices with rectangular t
ypes.
-/
theorem mul_eq_one_comm_of_equiv [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
    (e : m ≃ n) : A * B = 1 ↔ B * A = 1 :=
  (reindex e e).injective.eq_iff.symm.trans <| by
    rw [reindex_apply, reindex_apply, submatrix_one_equiv, ← submatrix_mul_equiv _ _ _ (.refl _),
      mul_eq_one_comm, submatrix_mul_equiv, Equiv.coe_refl, submatrix_id_id]
/-
**Matrix.mul_eq_one_comm_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mul_eq_one_comm_of_card_eq [IsStablyFiniteRing R] {A : Matrix m n R} {B : 
Matrix n m R} (eq : Fintype.card m = Fintype.card n) : A * B = 1 ↔ B * A = 1
参数：eq : Fintype.card m = Fintype.card n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_eq_one_comm_of_equiv`：mul_eq_one_comm_of_equiv [IsStablyFinit
eRing R] {A : Matrix m n R} {B : Matrix n m R} (e : m ≃ n) : A * B = 1 ↔ B * A =
 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
-/
theorem mul_eq_one_comm_of_card_eq [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
    (eq : Fintype.card m = Fintype.card n) : A * B = 1 ↔ B * A = 1 :=
  mul_eq_one_comm_of_equiv (Fintype.card_eq.mp eq).some

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

/-
**RingHom.map_matrix_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : 
α ->+* β) : f ((M * N) i j) = (M.map f * N.map f) i j
参数：M : Matrix m n α；N : Matrix n o α；i : m；j : o；f : α ->+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f ((M * N) i j) = (M.map f * N.map f) i j := by
  simp [Matrix.mul_apply, map_sum]
/-
**RingHom.map_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (v
 w : n -> R) : f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w
参数：f : R ->+* S；v w : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (v w : n → R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [dotProduct, map_sum f, f.map_mul, Function.comp]
/-
**RingHom.map_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : M
atrix n m R) (v : n -> R) (i : m) : f ((v ᵥ* M) i) = ((f ∘ v) ᵥ* M.map f) i
参数：f : R ->+* S；M : Matrix n m R；v : n -> R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_dotProduct`：map_dotProduct [NonAssocSemiring R] [NonAssocSem
iring S] (f : R ->+* S) (v w : n -> R) : f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix n m R)
    (v : n → R) (i : m) : f ((v ᵥ* M) i) = ((f ∘ v) ᵥ* M.map f) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]
/-
**RingHom.map_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : M
atrix m n R) (v : n -> R) (i : m) : f ((M *ᵥ v) i) = (M.map f *ᵥ (f ∘ v)) i
参数：f : R ->+* S；M : Matrix m n R；v : n -> R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_dotProduct`：map_dotProduct [NonAssocSemiring R] [NonAssocSem
iring S] (f : R ->+* S) (v w : n -> R) : f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix m n R)
    (v : n → R) (i : m) : f ((M *ᵥ v) i) = (M.map f *ᵥ (f ∘ v)) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

end RingHom

