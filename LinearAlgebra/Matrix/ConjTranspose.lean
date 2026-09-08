/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Basis

/-!
# Matrices over star rings.

## Notation

The scope `Matrix` gives the following notation:

* `ᴴ` for `Matrix.conjTranspose`

-/

@[expose] public section


universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix


/-- The conjugate transpose of a matrix defined in term of `star`. -/
/-
**Matrix.conjTranspose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α
参数：M : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate transpose of a matrix defined in term of `star`.
-/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

@[simp]
/-
**Matrix.conjTranspose_single** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_single [DecidableEq n] [DecidableEq m] [AddMonoid α] [StarAd
dMonoid α] (i : m) (j : n) (a : α) : (single i j a)ᴴ = single j i (star a)
参数：i : m；j : n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.transpose_single`：transpose_single (i : m) (j : n) (a : α) : (sin
gle i j a)ᵀ = single j i a
· 使用引理 `Matrix.map_single`：map_single (i : m) (j : n) (a : α) {β : Type*} [Zero 
β] {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) : (single i j a).map
 f = si…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `starAddEquiv_apply`：∀ {R : Type u} [inst : AddMonoid R] [inst_1 : StarAd
dMonoid R] (a : R), starAddEquiv a = star a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjTranspose_single [DecidableEq n] [DecidableEq m] [AddMonoid α]
    [StarAddMonoid α] (i : m) (j : n) (a : α) :
    (single i j a)ᴴ = single j i (star a) := by
  change (single i j a).transpose.map starAddEquiv = single j i (star a)
  simp

section Diagonal

variable [DecidableEq n]

@[simp]
/-
**Matrix.diagonal_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n -> α) : (dia
gonal v)ᴴ = diagonal (star v)
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} 
[inst : Star α] (M : Matrix m n α), M.conjTranspose = M.transpose.map star
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl
/-
**Matrix.map_diagonal_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_diagonal_star [AddMonoid α] [StarAddMonoid α] (x : n -> α) : (diagonal
 x).map star = diagonal (star x)
参数：x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
theorem map_diagonal_star [AddMonoid α] [StarAddMonoid α] (x : n → α) :
    (diagonal x).map star = diagonal (star x) := diagonal_map (star_zero _)

end Diagonal

section Diag

@[simp]
/-
**Matrix.diag_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：diag_conjTranspose [Star α] (A : Matrix n n α) : diag Aᴴ = star (diag A)
参数：A : Matrix n n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_conjTranspose [Star α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl
/-
**Matrix.diag_map_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : Star α] (A : Matrix n n α), (A.map s
tar).diag = star A.diag
参数：A : Matrix n n α；A.map star。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem diag_map_star [Star α] (A : Matrix n n α) : diag (A.map star) = star (diag A) := rfl

end Diag

section DotProduct

variable [Fintype m] [Fintype n]

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

/-
**Matrix.star_dotProduct_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v)
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
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dotProduct]
/-
**Matrix.star_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v)
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
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dotProduct]
/-
**Matrix.dotProduct_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v)
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
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dotProduct]

end StarRing

end DotProduct

section NonUnitalSemiring

variable [NonUnitalSemiring α]

/-
**Matrix.star_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n -> α) : sta
r (M *ᵥ v) = star v ᵥ* Mᴴ
参数：M : Matrix m n α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.star_dotProduct_star`：star_dotProduct_star : star v ⬝ᵥ star w = s
tar (w ⬝ᵥ v)
-/
theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M *ᵥ v) = star v ᵥ* Mᴴ :=
  funext fun _ => (star_dotProduct_star _ _).symm
/-
**Matrix.star_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m -> α) : sta
r (v ᵥ* M) = Mᴴ *ᵥ star v
参数：M : Matrix m n α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.star_dotProduct_star`：star_dotProduct_star : star v ⬝ᵥ star w = s
tar (w ⬝ᵥ v)
-/
theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (v ᵥ* M) = Mᴴ *ᵥ star v :=
  funext fun _ => (star_dotProduct_star _ _).symm
/-
**Matrix.mulVec_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m ->
 α) : Aᴴ *ᵥ x = star (star x ᵥ* A)
参数：A : Matrix m n α；x : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.star_dotProduct`：star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ 
v)
-/
theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    Aᴴ *ᵥ x = star (star x ᵥ* A) :=
  funext fun _ => star_dotProduct _ _
/-
**Matrix.vecMul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n ->
 α) : x ᵥ* Aᴴ = star (A *ᵥ star x)
参数：A : Matrix m n α；x : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.dotProduct_star`：dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star 
v)
-/
theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    x ᵥ* Aᴴ = star (A *ᵥ star x) :=
  funext fun _ => dotProduct_star _ _

end NonUnitalSemiring

@[simp]
/-
**Matrix.conjTranspose_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_vecMulVec [Mul α] [StarMul α] (w : m -> α) (v : n -> α) : (v
ecMulVec w v)ᴴ = vecMulVec (star v) (star w)
参数：w : m -> α；v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
-/
theorem conjTranspose_vecMulVec [Mul α] [StarMul α] (w : m → α) (v : n → α) :
    (vecMulVec w v)ᴴ = vecMulVec (star v) (star w) :=
  ext fun _ _ => star_mul _ _
/-
**Matrix.map_vecMulVec_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Mul α] [inst_1 : Star
Mul α] (w : m → α) (v : n → α),   (Matrix.vecMulVec w v).map star = (Matrix.vecM
ulVec (star v) (star w)).transpose
参数：w : m → α；v : n → α；Matrix.vecMulVec w v；Matrix.vecMulVec (star v) (star w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_vecMulVec`：conjTranspose_vecMulVec [Mul α] [StarMul
 α] (w : m -> α) (v : n -> α) : (vecMulVec w v)ᴴ = vecMulVec (star v) (star w)
-/
@[simp] theorem map_vecMulVec_star [Mul α] [StarMul α] (w : m → α) (v : n → α) :
    (vecMulVec w v).map star = (vecMulVec (star v) (star w))ᵀ := by
  rw [← conjTranspose_vecMulVec]; rfl

section ConjTranspose

open Matrix

/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
/-
**Matrix.conjTranspose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_apply [Star α] (M : Matrix m n α) (i j) : M.conjTranspose j 
i = star (M i j)
参数：M : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
theorem conjTranspose_apply [Star α] (M : Matrix m n α) (i j) :
    M.conjTranspose j i = star (M i j) :=
  rfl

@[simp]
/-
**Matrix.conjTranspose_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = 
M
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
  Matrix.ext <| by simp

variable (n α) in
/-
**Matrix.conjTranspose_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_involutive [InvolutiveStar α] : (conjTranspose : Matrix n n 
α -> Matrix n n α).Involutive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
-/
theorem conjTranspose_involutive [InvolutiveStar α] :
    (conjTranspose : Matrix n n α → Matrix n n α).Involutive :=
  conjTranspose_conjTranspose
/-
**Matrix.conjTranspose_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_transpose [Star α] (M : Matrix m n α) : Mᴴᵀ = M.map star
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTranspose_transpose [Star α] (M : Matrix m n α) :
    Mᴴᵀ = M.map star :=
  rfl
/-
**Matrix.transpose_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_conjTranspose [Star α] (M : Matrix m n α) : Mᵀᴴ = M.map star
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_conjTranspose [Star α] (M : Matrix m n α) :
    Mᵀᴴ = M.map star :=
  rfl
/-
**Matrix.conjTranspose_transpose_eq_transpose_conjTranspose** 是 Mathlib 中的一个定理，位
于命名空间 `Matrix`。
形式化陈述：conjTranspose_transpose_eq_transpose_conjTranspose [Star α] (M : Matrix m 
n α) : Mᵀᴴ = Mᴴᵀ
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTranspose_transpose_eq_transpose_conjTranspose [Star α] (M : Matrix m n α) :
    Mᵀᴴ = Mᴴᵀ :=
  rfl
/-
**Matrix.conjTranspose_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_injective [InvolutiveStar α] : Function.Injective (conjTrans
pose : Matrix m n α -> Matrix n m α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Matrix.map_injective`：map_injective {f : α -> β} (hf : Function.Injectiv
e f) : Function.Injective fun M : Matrix m n α => M.map f
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `Matrix.transpose_injective`：transpose_injective : Function.Injective (tr
anspose : Matrix m n α -> Matrix n m α)
-/
theorem conjTranspose_injective [InvolutiveStar α] :
    Function.Injective (conjTranspose : Matrix m n α → Matrix n m α) :=
  (map_injective star_injective).comp transpose_injective
/-
**Matrix.conjTranspose_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : InvolutiveStar α] {A 
B : Matrix m n α},   A.conjTranspose = B.conjTranspose ↔ A = B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.conjTranspose_injective`：conjTranspose_injective [InvolutiveStar 
α] : Function.Injective (conjTranspose : Matrix m n α -> Matrix n m α)
-/
@[simp] theorem conjTranspose_inj [InvolutiveStar α] {A B : Matrix m n α} : Aᴴ = Bᴴ ↔ A = B :=
  conjTranspose_injective.eq_iff

@[simp]
/-
**Matrix.conjTranspose_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α] 
{M : Matrix n n α} {v : n -> α} : Mᴴ = diagonal v ↔ M = diagonal (star v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.conjTranspose_involutive`：conjTranspose_involutive [InvolutiveSta
r α] : (conjTranspose : Matrix n n α -> Matrix n n α).Involutive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_conjTranspose`：diagonal_conjTranspose [AddMonoid α] [Sta
rAddMonoid α] (v : n -> α) : (diagonal v)ᴴ = diagonal (star v)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n → α} :
    Mᴴ = diagonal v ↔ M = diagonal (star v) :=
  (conjTranspose_involutive n α).eq_iff.trans <| by rw [diagonal_conjTranspose]
/-
**Matrix.map_star_eq_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : AddMonoid α
] [inst_2 : StarAddMonoid α]   {M : Matrix n n α} {v : n → α}, M.map star = Matr
ix.diagonal v ↔ M = Matrix.diagonal (star v)
参数：star v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.map_involutive`：map_involutive {f : α -> α} (hf : Function.Involu
tive f) : Function.Involutive fun M : Matrix m n α => M.map f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_diagonal_star`：map_diagonal_star [AddMonoid α] [StarAddMonoid
 α] (x : n -> α) : (diagonal x).map star = diagonal (star x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem map_star_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n → α} : M.map star = diagonal v ↔ M = diagonal (star v) :=
  map_involutive star_involutive |>.eq_iff.trans <| by rw [map_diagonal_star]

@[simp]
/-
**Matrix.conjTranspose_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
 Mᴴ = 0 ↔ M = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_inj`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [
inst : InvolutiveStar α] {A B : Matrix m n α},   A.conjTranspose = B.conjTranspo
se ↔ A = B
· 使用定理 `Matrix.conjTranspose_zero`：conjTranspose_zero [AddMonoid α] [StarAddMono
id α] : (0 : Matrix m n α)ᴴ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conjTranspose_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    Mᴴ = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (A := M), conjTranspose_zero]
/-
**Matrix.map_star_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : AddMonoid α] [inst_1 
: StarAddMonoid α] {M : Matrix m n α},   M.map star = 0 ↔ M = 0
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
@[simp] theorem map_star_eq_zero [AddMonoid α] [StarAddMonoid α] {M : Matrix m n α} :
    M.map star = 0 ↔ M = 0 := by simp [← ext_iff]

@[simp]
/-
**Matrix.conjTranspose_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] : (1 :
 Matrix n n α)ᴴ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴ = 1 := by
  simp [conjTranspose]

@[simp]
/-
**Matrix.conjTranspose_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M 
: Matrix n n α} : Mᴴ = 1 ↔ M = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.conjTranspose_involutive`：conjTranspose_involutive [InvolutiveSta
r α] : (conjTranspose : Matrix n n α -> Matrix n n α).Involutive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_one`：conjTranspose_one [DecidableEq n] [NonAssocSem
iring α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 :=
  (conjTranspose_involutive n α).eq_iff.trans <| by rw [conjTranspose_one]
/-
**Matrix.map_star_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : NonAssocSem
iring α] [inst_2 : StarRing α]   {M : Matrix n n α}, M.map star = 1 ↔ M = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.map_involutive`：map_involutive {f : α -> α} (hf : Function.Involu
tive f) : Function.Involutive fun M : Matrix m n α => M.map f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem map_star_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} : M.map star = 1 ↔ M = 1 :=
  map_involutive star_involutive |>.eq_iff.trans <| by simp

@[simp]
/-
**Matrix.conjTranspose_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d
 : Nat) : (d : Matrix n n α)ᴴ = d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_natCast`：transpose_natCast [DecidableEq n] [AddMonoidWi
thOne α] (d : Nat) : (d : Matrix n n α)ᵀ = d
· 使用定理 `Matrix.map_natCast`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : D
ecidableEq n] [inst_1 : AddMonoidWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0
 = 0 → ∀…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_natCast`：star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) :
 star (n : R) = n
-/
theorem conjTranspose_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_natCast, diagonal_natCast]

@[simp]
/-
**Matrix.map_natCast_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_natCast_star [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : Na
t) : (d : Matrix n n α).map star = d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_natCast`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : D
ecidableEq n] [inst_1 : AddMonoidWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0
 = 0 → ∀…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_natCast`：star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) :
 star (n : R) = n
-/
theorem map_natCast_star [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ) :
    (d : Matrix n n α).map star = d := by simp [Matrix.map_natCast, diagonal_natCast]

@[simp]
/-
**Matrix.conjTranspose_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
 {M : Matrix n n α} {d : Nat} : Mᴴ = d ↔ M = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.conjTranspose_involutive`：conjTranspose_involutive [InvolutiveSta
r α] : (conjTranspose : Matrix n n α -> Matrix n n α).Involutive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_natCast`：conjTranspose_natCast [DecidableEq n] [Non
AssocSemiring α] [StarRing α] (d : Nat) : (d : Matrix n n α)ᴴ = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conjTranspose_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} :
    Mᴴ = d ↔ M = d :=
  (conjTranspose_involutive n α).eq_iff.trans <| by rw [conjTranspose_natCast]
/-
**Matrix.map_star_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : NonAssocSem
iring α] [inst_2 : StarRing α]   {M : Matrix n n α} {d : ℕ}, M.map star = ↑d ↔ M
 = ↑d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.map_involutive`：map_involutive {f : α -> α} (hf : Function.Involu
tive f) : Function.Involutive fun M : Matrix m n α => M.map f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_natCast_star`：map_natCast_star [DecidableEq n] [NonAssocSemir
ing α] [StarRing α] (d : Nat) : (d : Matrix n n α).map star = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem map_star_eq_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} : M.map star = d ↔ M = d :=
  (map_involutive star_involutive).eq_iff.trans <| by rw [map_natCast_star]

@[simp]
/-
**Matrix.conjTranspose_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_ofNat [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d :
 Nat) [d.AtLeastTwo] : (ofNat(d) : Matrix n n α)ᴴ = OfNat.ofNat d
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_natCast`：conjTranspose_natCast [DecidableEq n] [Non
AssocSemiring α] [StarRing α] (d : Nat) : (d : Matrix n n α)ᴴ = d
-/
theorem conjTranspose_ofNat [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α)ᴴ = OfNat.ofNat d :=
  conjTranspose_natCast _
/-
**Matrix.map_ofNat_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : NonAssocSem
iring α] [inst_2 : StarRing α] (d : ℕ)   [inst_3 : d.AtLeastTwo], (OfNat.ofNat d
).map star = OfNat.ofNat d
参数：d : ℕ；OfNat.ofNat d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_natCast_star`：map_natCast_star [DecidableEq n] [NonAssocSemir
ing α] [StarRing α] (d : Nat) : (d : Matrix n n α).map star = d
-/
@[simp] theorem map_ofNat_star [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ)
    [d.AtLeastTwo] : (ofNat(d) : Matrix n n α).map star = OfNat.ofNat d := map_natCast_star _

@[simp]
/-
**Matrix.conjTranspose_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α] {M : Matr
ix n n α} {d : Nat} [d.AtLeastTwo] : Mᴴ = ofNat(d) ↔ M = OfNat.ofNat d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_eq_natCast`：conjTranspose_eq_natCast [DecidableEq n
] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α} {d : Nat} : Mᴴ = d ↔ M = 
d
-/
theorem conjTranspose_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α]
    {M : Matrix n n α} {d : ℕ} [d.AtLeastTwo] :
    Mᴴ = ofNat(d) ↔ M = OfNat.ofNat d :=
  conjTranspose_eq_natCast
/-
**Matrix.map_star_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : Semiring α]
 [inst_2 : StarRing α] {M : Matrix n n α}   {d : ℕ} [inst_3 : d.AtLeastTwo], M.m
ap star = OfNat.ofNat d ↔ M = OfNat.ofNat d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_star_eq_natCast`：∀ {n : Type u_3} {α : Type v} [inst : Decida
bleEq n] [inst_1 : NonAssocSemiring α] [inst_2 : StarRing α]   {M : Matrix n n α
} {d : ℕ}, M.map…
-/
@[simp] theorem map_star_eq_ofNat [DecidableEq n] [Semiring α] [StarRing α] {M : Matrix n n α}
    {d : ℕ} [d.AtLeastTwo] : M.map star = ofNat(d) ↔ M = OfNat.ofNat d := map_star_eq_natCast

@[simp]
/-
**Matrix.conjTranspose_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : Int) : (d
 : Matrix n n α)ᴴ = d
参数：d : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_intCast`：transpose_intCast [DecidableEq n] [AddGroupWit
hOne α] (d : Int) : (d : Matrix n n α)ᵀ = d
· 使用定理 `Matrix.map_intCast`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : D
ecidableEq n] [inst_1 : AddGroupWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0 
= 0 → ∀ …
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_intCast`：star_intCast [NonAssocRing R] [StarRing R] (z : Int) : sta
r (z : R) = z
-/
theorem conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : ℤ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [conjTranspose, Matrix.map_intCast, diagonal_intCast]
/-
**Matrix.map_intCast_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : Ring α] [in
st_2 : StarRing α] (d : ℤ), (↑d).map star = ↑d
参数：d : ℤ；↑d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_intCast`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : D
ecidableEq n] [inst_1 : AddGroupWithOne α] [inst_2 : Zero β]   {f : α → β}, f 0 
= 0 → ∀ …
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `star_intCast`：star_intCast [NonAssocRing R] [StarRing R] (z : Int) : sta
r (z : R) = z
-/
@[simp] theorem map_intCast_star [DecidableEq n] [Ring α] [StarRing α] (d : ℤ) :
    (d : Matrix n n α).map star = d := by simp [Matrix.map_intCast, diagonal_intCast]

@[simp]
/-
**Matrix.conjTranspose_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_eq_intCast [DecidableEq n] [Ring α] [StarRing α] {M : Matrix
 n n α} {d : Int} : Mᴴ = d ↔ M = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.conjTranspose_involutive`：conjTranspose_involutive [InvolutiveSta
r α] : (conjTranspose : Matrix n n α -> Matrix n n α).Involutive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_intCast`：conjTranspose_intCast [DecidableEq n] [Rin
g α] [StarRing α] (d : Int) : (d : Matrix n n α)ᴴ = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conjTranspose_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : ℤ} :
    Mᴴ = d ↔ M = d :=
  (conjTranspose_involutive n α).eq_iff.trans <|
    by rw [conjTranspose_intCast]
/-
**Matrix.map_star_eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} {α : Type v} [inst : DecidableEq n] [inst_1 : Ring α] [in
st_2 : StarRing α] {M : Matrix n n α} {d : ℤ},   M.map star = ↑d ↔ M = ↑d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matrix.map_involutive`：map_involutive {f : α -> α} (hf : Function.Involu
tive f) : Function.Involutive fun M : Matrix m n α => M.map f
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_intCast_star`：∀ {n : Type u_3} {α : Type v} [inst : Decidable
Eq n] [inst_1 : Ring α] [inst_2 : StarRing α] (d : ℤ), (↑d).map star = ↑d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem map_star_eq_intCast [DecidableEq n] [Ring α] [StarRing α]
    {M : Matrix n n α} {d : ℤ} : M.map star = d ↔ M = d :=
  (map_involutive star_involutive).eq_iff.trans <| by rw [map_intCast_star]

@[simp]
/-
**Matrix.conjTranspose_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) : (
M + N)ᴴ = Mᴴ + Nᴴ
参数：M N : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) : (M
 - N)ᴴ = Mᴴ - Nᴴ
参数：M N : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
  Matrix.ext <| by simp

/-- Note that `StarModule` is quite a strong requirement; as such we also provide the following
variants which this lemma would not apply to:
* `Matrix.conjTranspose_smul_non_comm`
* `Matrix.conjTranspose_nsmul`
* `Matrix.conjTranspose_zsmul`
* `Matrix.conjTranspose_natCast_smul`
* `Matrix.conjTranspose_intCast_smul`
* `Matrix.conjTranspose_inv_natCast_smul`
* `Matrix.conjTranspose_inv_intCast_smul`
* `Matrix.conjTranspose_ratCast_smul`
-/
@[simp]
/-
**Matrix.conjTranspose_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R) (
M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
参数：c : R；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …

--- 原说明 ---
Note that `StarModule` is quite a strong requirement; as such we also provide th
e following
variants which this lemma would not apply to:
* `Matrix.conjTranspose_smul_non_comm`
* `Matrix.conjTranspose_nsmul`
* `Matrix.conjTranspose_zsmul`
* `Matrix.conjTranspose_natCast_smul`
* `Matrix.conjTranspose_intCast_smul`
* `Matrix.conjTranspose_inv_natCast_smul`
* `Matrix.conjTranspose_inv_intCast_smul`
* `Matrix.conjTranspose_ratCast_smul`
-/
theorem conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ :=
  Matrix.ext fun _ _ => star_smul _ _

@[simp]
/-
**Matrix.conjTranspose_smul_non_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c 
: R) (M : Matrix m n α) (h : forall (r : R) (a : α), star (r • a) = MulOpposite.
op (star r) • star a) : (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ
参数：c : R；M : Matrix m n α；h : forall (r : R) (a : α), star (r • a) = MulOpposite
.op (star r) • star a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : ∀ (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  Matrix.ext <| by simp [h]
/-
**Matrix.conjTranspose_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_smul_self [Mul α] [StarMul α] (c : α) (M : Matrix m n α) : (
c • M)ᴴ = MulOpposite.op (star c) • Mᴴ
参数：c : α；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_smul_non_comm`：conjTranspose_smul_non_comm [Star R]
 [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R) (M : Matrix m n α) (h : forall (r : R
) (a : α), star (r • a) …
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
-/
theorem conjTranspose_smul_self [Mul α] [StarMul α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul
/-
**Matrix.conjTranspose_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : Nat) (M : Matrix 
m n α) : (c • M)ᴴ = c • Mᴴ
参数：c : Nat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_smul`：conjTranspose_smul [Star R] [Star α] [SMul R 
α] [StarModule R α] (c : R) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : ℕ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ := by
  simp
/-
**Matrix.conjTranspose_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : Int) (M : Matrix m
 n α) : (c • M)ᴴ = c • Mᴴ
参数：c : Int；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_smul`：conjTranspose_smul [Star R] [Star α] [SMul R 
α] [StarModule R α] (c : R) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : ℤ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ := by
  simp

@[simp]
/-
**Matrix.conjTranspose_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α
] [Module R α] (c : Nat) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ
参数：c : Nat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_natCast_smul`：star_natCast_smul [Semiring R] [AddCommMonoid M] [Mod
ule R M] [StarAddMonoid M] (n : Nat) (x : M) : star ((n : R) • x) = (n : R) • st
ar x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_ofNat_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] 
[Module R α] (c : Nat) [c.AtLeastTwo] (M : Matrix m n α) : ((ofNat(c) : R) • M)ᴴ
 = (OfNat.ofNat c : R) • Mᴴ
参数：c : Nat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_natCast_smul`：conjTranspose_natCast_smul [Semiring 
R] [AddCommMonoid α] [StarAddMonoid α] [Module R α] (c : Nat) (M : Matrix m n α)
 : ((c : R) • M)ᴴ = (c …
-/
theorem conjTranspose_ofNat_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R) • M)ᴴ = (OfNat.ofNat c : R) • Mᴴ :=
  conjTranspose_natCast_smul c M

@[simp]
/-
**Matrix.conjTranspose_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Mo
dule R α] (c : Int) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ
参数：c : Int；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_intCast_smul`：star_intCast_smul [Ring R] [AddCommGroup M] [Module R
 M] [StarAddMonoid M] (n : Int) (x : M) : star ((n : R) • x) = (n : R) • star x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_inv_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [Sta
rAddMonoid α] [Module R α] (c : Nat) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c 
: R)⁻¹ • Mᴴ
参数：c : Nat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv_natCast_smul`：star_inv_natCast_smul [DivisionSemiring R] [AddCo
mmMonoid M] [Module R M] [StarAddMonoid M] (n : Nat) (x : M) : star ((n⁻¹ : R) •
 x) = (n⁻¹ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_inv_ofNat_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarA
ddMonoid α] [Module R α] (c : Nat) [c.AtLeastTwo] (M : Matrix m n α) : ((ofNat(c
) : R)⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ
参数：c : Nat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_inv_natCast_smul`：conjTranspose_inv_natCast_smul [D
ivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α] (c : Nat) (M
 : Matrix m n α) : ((c : R)…
-/
theorem conjTranspose_inv_ofNat_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) [c.AtLeastTwo] (M : Matrix m n α) :
    ((ofNat(c) : R)⁻¹ • M)ᴴ = (OfNat.ofNat c : R)⁻¹ • Mᴴ :=
  conjTranspose_inv_natCast_smul c M

@[simp]
/-
**Matrix.conjTranspose_inv_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddM
onoid α] [Module R α] (c : Int) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻
¹ • Mᴴ
参数：c : Int；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv_intCast_smul`：star_inv_intCast_smul [DivisionRing R] [AddCommGr
oup M] [Module R M] [StarAddMonoid M] (n : Int) (x : M) : star ((n⁻¹ : R) • x) =
 (n⁻¹ : R) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : ℤ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_ratCast_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoi
d α] [Module R α] (c : Rat) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ
参数：c : Rat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_ratCast_smul`：star_ratCast_smul [DivisionRing R] [AddCommGroup M] [
Module R M] [StarAddMonoid M] (n : Rat) (x : M) : star ((n : R) • x) = (n : R) •
 star x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : ℚ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
/-
**Matrix.conjTranspose_rat_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module Rat α] (
c : Rat) (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ
参数：c : Rat；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_rat_smul`：∀ {R : Type u_1} [inst : AddCommGroup R] [inst_1 : StarAd
dMonoid R] [inst_2 : _root_.Module ℚ R] (q : ℚ) (x : R),   star (q • x) = q • st
ar …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp

@[simp]
/-
**Matrix.conjTranspose_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (
M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ
参数：M : Matrix m n α；N : Matrix n l α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᴴ = Nᴴ * Mᴴ :=
  Matrix.ext <| by simp [mul_apply]

@[simp]
/-
**Matrix.conjTranspose_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)
ᴴ = -Mᴴ
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
  Matrix.ext <| by simp
/-
**Matrix.conjTranspose_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α -> β) (hf : 
Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ
参数：f : α -> β；hf : Function.Semiconj f star star。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α → β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun _ _ => hf _

/-- When `star x = x` on the coefficients (such as the real numbers) `conjTranspose` and `transpose`
are the same operation. -/
@[simp]
/-
**Matrix.conjTranspose_eq_transpose_of_trivial** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix
 m n α) : Aᴴ = Aᵀ
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r

--- 原说明 ---
When `star x = x` on the coefficients (such as the real numbers) `conjTranspose`
 and `transpose`
are the same operation.
-/
theorem conjTranspose_eq_transpose_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) :
    Aᴴ = Aᵀ := Matrix.ext fun _ _ => star_trivial _

variable (m n α)

/-- `Matrix.conjTranspose` as an `AddEquiv` -/
@[simps apply]
/-
**Matrix.conjTransposeAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Ma
trix n m α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_add`：conjTranspose_add [AddMonoid α] [StarAddMonoid
 α] (M N : Matrix m n α) : (M + N)ᴴ = Mᴴ + Nᴴ

--- 原说明 ---
`Matrix.conjTranspose` as an `AddEquiv`
-/
def conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add

@[simp]
/-
**Matrix.conjTransposeAddEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] : (conjTranspos
eAddEquiv m n α).symm = conjTransposeAddEquiv n m α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl

variable {m n α}
/-
**Matrix.conjTranspose_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m
 n α)) : l.sumᴴ = (l.map conjTranspose).sum
参数：l : List (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.sumᴴ = (l.map conjTranspose).sum :=
  map_list_sum (conjTransposeAddEquiv m n α) l
/-
**Matrix.conjTranspose_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α] (s : Multis
et (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum
参数：s : Multiset (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.sumᴴ = (s.map conjTranspose).sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
/-
**Matrix.conjTranspose_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Fin
set ι) (M : ι -> Matrix m n α) : (∑ i in s, M i)ᴴ = ∑ i in s, (M i)ᴴ
参数：s : Finset ι；M : ι -> Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type*} (s : Finset ι)
    (M : ι → Matrix m n α) : (∑ i ∈ s, M i)ᴴ = ∑ i ∈ s, (M i)ᴴ :=
  map_sum (conjTransposeAddEquiv m n α) _ s

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
/-
**Matrix.conjTransposeLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [
StarAddMonoid α] [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m 
α where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)

--- 原说明 ---
`Matrix.conjTranspose` as a `LinearMap`
-/
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α where
  __ := conjTransposeAddEquiv m n α
  map_smul' := conjTranspose_smul

@[simp]
/-
**Matrix.conjTransposeLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid
 α] [StarAddMonoid α] [Module R α] [StarModule R α] : (conjTransposeLinearEquiv 
m n R α).symm = conjTransposeLinearEquiv n m R α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `Matrix n n α` have a star
operation equal to `Matrix.conjTranspose`. -/
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` has a star operation, square matrices `Matrix n n α` have a star
operation equal to `Matrix.conjTranspose`.
-/
instance [Star α] : Star (Matrix n n α) where star := conjTranspose
/-
**Matrix.star_eq_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ
参数：M : Matrix m m α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl

@[simp]
/-
**Matrix.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i)
参数：M : Matrix n n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar α] : InvolutiveStar (Matrix n n α) where
  star_involutive := conjTranspose_conjTranspose

/-- When `α` is a \*-additive monoid, `Matrix.star` is also a \*-additive monoid. -/
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is a \*-additive monoid, `Matrix.star` is also a \*-additive monoid.
-/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  star_add := conjTranspose_add
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β) where
  star_smul := conjTranspose_smul

/-- When `α` is a \*-(semi)ring, `Matrix.star` is also a \*-(semi)ring. -/
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is a \*-(semi)ring, `Matrix.star` is also a \*-(semi)ring.
-/
instance [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (Matrix n n α) where
  star_add := conjTranspose_add
  star_mul := conjTranspose_mul

@[deprecated (since := "2026-04-20")] protected alias star_mul := StarMul.star_mul

end Star

@[simp]
/-
**Matrix.conjTranspose_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_submatrix [Star α] (A : Matrix m n α) (r : l -> m) (c : o ->
 n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r
参数：A : Matrix m n α；r : l -> m；c : o -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r : l → m)
    (c : o → n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r :=
  ext fun _ _ => rfl
/-
**Matrix.conjTranspose_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α
) : (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ
参数：eₘ : m ≃ l；eₙ : n ≃ o；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

variable (m α) in
/-- `Matrix.conjTranspose` as a `StarRingEquiv` to the opposite ring -/
@[simps!]
/-
**Matrix.conjTransposeRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：conjTransposeRingEquiv [NonUnitalNonAssocSemiring α] [StarRing α] [Fintype
 m] : Matrix m m α ≃⋆+* (Matrix m m α)ᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.conjTranspose` as a `StarRingEquiv` to the opposite ring
-/
def conjTransposeRingEquiv [NonUnitalNonAssocSemiring α] [StarRing α] [Fintype m] :
    Matrix m m α ≃⋆+* (Matrix m m α)ᵐᵒᵖ where
  __ := (conjTransposeAddEquiv m m α).trans MulOpposite.opAddEquiv
  map_mul' M N := (congrArg MulOpposite.op <| conjTranspose_mul M N).trans <| MulOpposite.op_mul ..
  map_star' _ := rfl

@[simp]
/-
**Matrix.conjTranspose_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M
 : Matrix m m α) (k : Nat) : (M ^ k)ᴴ = Mᴴ ^ k
参数：M : Matrix m m α；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `StarRingEquiv.instRingEquivClass`：∀ {A : Type u_1} {B : Type u_2} [inst 
: Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B] [inst_4 : Star A]   
[inst_5 : Star B], Rin…
-/
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : ℕ) : (M ^ k)ᴴ = Mᴴ ^ k :=
  MulOpposite.op_injective <| map_pow (conjTransposeRingEquiv m α) M k
/-
**Matrix.conjTranspose_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq
 m] (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod
参数：l : List (Matrix m m α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.unop_map_list_prod`：∀ {R : Type u_2} {S : Type u_3} [inst : Se
miring R] [inst_1 : Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R),   MulOpposite.uno
p (f l.prod) = (Li…
-/
theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l

variable (n α) in
/-- `Matrix.conjTranspose` as a `StarAlgEquiv` to the opposite ring -/
@[simps!]
/-
**Matrix.conjTransposeAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：conjTransposeAlgEquiv [Fintype n] [CommSemiring R] [StarRing R] [TrivialSt
ar R] [Semiring α] [StarRing α] [Algebra R α] [StarModule R α] : Matrix n n α ≃⋆
ₐ[R] (Matrix n n α)ᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.conjTranspose` as a `StarAlgEquiv` to the opposite ring
-/
def conjTransposeAlgEquiv [Fintype n] [CommSemiring R] [StarRing R] [TrivialStar R] [Semiring α]
    [StarRing α] [Algebra R α] [StarModule R α] : Matrix n n α ≃⋆ₐ[R] (Matrix n n α)ᵐᵒᵖ where
  __ := conjTransposeRingEquiv n α
  map_smul' r M := by
    change conjTransposeRingEquiv n α (r • M) = r • conjTransposeRingEquiv n α M
    simp

end Matrix

