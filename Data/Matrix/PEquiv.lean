/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.PEquiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `PEquiv.toMatrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.toMatrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`toMatrix_trans : (f.trans g).toMatrix = f.toMatrix * g.toMatrix`
`toMatrix_symm  : f.symm.toMatrix = f.toMatrixᵀ`
`toMatrix_refl : (PEquiv.refl n).toMatrix = 1`
`toMatrix_bot : ⊥.toMatrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : Fin 1) (i : Fin n)).toMatrix` corresponds to the ith
projection map from R^n to R.

Any injective function `Fin m → Fin n` gives rise to a `PEquiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## Notation

This file uses `ᵀ` for `Matrix.transpose`.
-/

@[expose] public section

assert_not_exists Field

namespace PEquiv

open Matrix

universe u v

variable {k l m n : Type*}
variable {α β : Type*}

open Matrix

/-- `toMatrix` returns a matrix containing ones and zeros. `f.toMatrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
/-
**PEquiv.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α
参数：f : m ≃. n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toMatrix` returns a matrix containing ones and zeros. `f.toMatrix i j` is `1` i
f
  `f i = some j` and `0` otherwise
-/
def toMatrix [DecidableEq n] [Zero α] [One α] (f : m ≃. n) : Matrix m n α :=
  of fun i j => if j ∈ f i then (1 : α) else 0

-- TODO: set as an equation lemma for `toMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**PEquiv.toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_apply [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j) : toMat
rix f i j = if j in f i then (1 : α) else 0
参数：f : m ≃. n；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_apply [DecidableEq n] [Zero α] [One α] (f : m ≃. n) (i j) :
    toMatrix f i j = if j ∈ f i then (1 : α) else 0 :=
  rfl
/-
**PEquiv.toMatrix_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_mul_apply [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f : l
 ≃. m) (i j) (M : Matrix m n α) : (f.toMatrix * M :) i j = Option.casesOn (f i) 
0 fun fi => M fi j
参数：f : l ≃. m；i j；M : Matrix m n α。
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
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem toMatrix_mul_apply [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f : l ≃. m) (i j)
    (M : Matrix m n α) : (f.toMatrix * M :) i j = Option.casesOn (f i) 0 fun fi => M fi j := by
  dsimp [toMatrix, Matrix.mul_apply]
  rcases h : f i with - | fi
  · simp
  · rw [Finset.sum_eq_single fi] <;> simp +contextual [eq_comm]
/-
**PEquiv.mul_toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mul_toMatrix_apply [Fintype m] [NonAssocSemiring α] [DecidableEq n] (M : M
atrix l m α) (f : m ≃. n) (i j) : (M * f.toMatrix :) i j = Option.casesOn (f.sym
m j) 0 (M i)
参数：M : Matrix l m α；f : m ≃. n；i j。
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
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
theorem mul_toMatrix_apply [Fintype m] [NonAssocSemiring α] [DecidableEq n] (M : Matrix l m α)
    (f : m ≃. n) (i j) : (M * f.toMatrix :) i j = Option.casesOn (f.symm j) 0 (M i) := by
  dsimp [Matrix.mul_apply, toMatrix_apply]
  rcases h : f.symm j with - | fj
  · simp [h, ← f.eq_some_iff]
  · rw [Finset.sum_eq_single fj]
    · simp [h, ← f.eq_some_iff]
    · rintro b - n
      simp [h, ← f.eq_some_iff, n.symm]
    · simp
/-
**PEquiv.toMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n
) : (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ
参数：f : m ≃. n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PEquiv.mem_iff_mem`：mem_iff_mem (f : α ≃. β) : forall {a : α} {b : β}, a
 in f.symm b ↔ b in f a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem toMatrix_symm [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃. n) :
    (f.symm.toMatrix : Matrix n m α) = f.toMatrixᵀ := by
  ext
  simp only [transpose, mem_iff_mem f, toMatrix_apply]
  congr

@[simp]
/-
**PEquiv.toMatrix_refl** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_refl [DecidableEq n] [Zero α] [One α] : ((PEquiv.refl n).toMatrix
 : Matrix n n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_refl [DecidableEq n] [Zero α] [One α] :
    ((PEquiv.refl n).toMatrix : Matrix n n α) = 1 := by
  ext
  simp [toMatrix_apply, one_apply]

@[simp]
/-
**PEquiv.toMatrix_toPEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_toPEquiv_apply [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (i) :
 f.toPEquiv.toMatrix i = Pi.single (f i) (1 : α)
参数：f : m ≃ n；i。
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
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_toPEquiv_apply [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (i) :
    f.toPEquiv.toMatrix i = Pi.single (f i) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm]

@[simp]
/-
**PEquiv.transpose_toMatrix_toPEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：transpose_toMatrix_toPEquiv_apply [DecidableEq m] [DecidableEq n] [Zero α]
 [One α] (f : m ≃ n) (j) : f.toPEquiv.toMatrixᵀ j = Pi.single (f.symm j) (1 : α)
参数：f : m ≃ n；j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_toMatrix_toPEquiv_apply
    [DecidableEq m] [DecidableEq n] [Zero α] [One α] (f : m ≃ n) (j) :
    f.toPEquiv.toMatrixᵀ j = Pi.single (f.symm j) (1 : α) := by
  ext
  simp [toMatrix_apply, Pi.single_apply, eq_comm, Equiv.eq_symm_apply]
/-
**PEquiv.toMatrix_toPEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_toPEquiv_mul [Fintype m] [DecidableEq m] [NonAssocSemiring α] (f 
: l ≃ m) (M : Matrix m n α) : f.toPEquiv.toMatrix * M = M.submatrix f id
参数：f : l ≃ m；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.toMatrix_mul_apply`：toMatrix_mul_apply [Fintype m] [DecidableEq m
] [NonAssocSemiring α] (f : l ≃. m) (i j) (M : Matrix m n α) : (f.toMatrix * M :
) i j = Option.…
· 使用定理 `Equiv.toPEquiv_apply`：toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x 
= some (f x)
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem toMatrix_toPEquiv_mul [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] (f : l ≃ m) (M : Matrix m n α) :
    f.toPEquiv.toMatrix * M = M.submatrix f id := by
  ext i j
  rw [toMatrix_mul_apply, Equiv.toPEquiv_apply, submatrix_apply, id]
/-
**PEquiv.mul_toMatrix_toPEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mul_toMatrix_toPEquiv [Fintype m] [DecidableEq n] [NonAssocSemiring α] (M 
: Matrix l m α) (f : m ≃ n) : (M * f.toPEquiv.toMatrix) = M.submatrix id f.symm
参数：M : Matrix l m α；f : m ≃ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.mul_toMatrix_apply`：mul_toMatrix_apply [Fintype m] [NonAssocSemir
ing α] [DecidableEq n] (M : Matrix l m α) (f : m ≃. n) (i j) : (M * f.toMatrix :
) i j = Option.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.toPEquiv_symm`：toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toP
Equiv.symm
· 使用定理 `Equiv.toPEquiv_apply`：toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x 
= some (f x)
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem mul_toMatrix_toPEquiv [Fintype m] [DecidableEq n]
    [NonAssocSemiring α] (M : Matrix l m α) (f : m ≃ n) :
    (M * f.toPEquiv.toMatrix) = M.submatrix id f.symm :=
  Matrix.ext fun i j => by
    rw [PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply,
      Matrix.submatrix_apply, id]
/-
**PEquiv.toMatrix_toPEquiv_mulVec** 是 Mathlib 中的一个引理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_toPEquiv_mulVec [DecidableEq n] [Fintype n] [NonAssocSemiring α] 
(σ : m ≃ n) (a : n -> α) : σ.toPEquiv.toMatrix *ᵥ a = a ∘ σ
参数：σ : m ≃ n；a : n -> α。
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMatrix_toPEquiv_mulVec [DecidableEq n] [Fintype n]
    [NonAssocSemiring α] (σ : m ≃ n) (a : n → α) :
    σ.toPEquiv.toMatrix *ᵥ a = a ∘ σ := by
  ext j
  simp [toMatrix, mulVec, dotProduct]
/-
**PEquiv.vecMul_toMatrix_toPEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PEquiv`。
形式化陈述：vecMul_toMatrix_toPEquiv [DecidableEq n] [Fintype m] [NonAssocSemiring α] 
(σ : m ≃ n) (a : m -> α) : a ᵥ* σ.toPEquiv.toMatrix = a ∘ σ.symm
参数：σ : m ≃ n；a : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vecMul_toMatrix_toPEquiv [DecidableEq n] [Fintype m]
    [NonAssocSemiring α] (σ : m ≃ n) (a : m → α) :
    a ᵥ* σ.toPEquiv.toMatrix = a ∘ σ.symm := by
  classical
  ext j
  simp [toMatrix, ← σ.eq_symm_apply, vecMul, dotProduct]
/-
**PEquiv.toMatrix_trans** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiri
ng α] (f : l ≃. m) (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMa
trix * g.toMatrix
参数：f : l ≃. m；g : m ≃. n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.toMatrix_mul_apply`：toMatrix_mul_apply [Fintype m] [DecidableEq m
] [NonAssocSemiring α] (f : l ≃. m) (i j) (M : Matrix m n α) : (f.toMatrix * M :
) i j = Option.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem toMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring α] (f : l ≃. m)
    (g : m ≃. n) : ((f.trans g).toMatrix : Matrix l n α) = f.toMatrix * g.toMatrix := by
  ext i j
  rw [toMatrix_mul_apply]
  dsimp +instances [toMatrix, PEquiv.trans]
  cases f i <;> simp

@[simp]
/-
**PEquiv.toMatrix_bot** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_bot [DecidableEq n] [Zero α] [One α] : ((⊥ : PEquiv m n).toMatrix
 : Matrix m n α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMatrix_bot [DecidableEq n] [Zero α] [One α] :
    ((⊥ : PEquiv m n).toMatrix : Matrix m n α) = 0 :=
  rfl
/-
**PEquiv.toMatrix_injective** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_injective [DecidableEq n] [MulZeroOneClass α] [Nontrivial α] : Fu
nction.Injective (@toMatrix m n α _ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem toMatrix_injective [DecidableEq n] [MulZeroOneClass α] [Nontrivial α] :
    Function.Injective (@toMatrix m n α _ _ _) := by
  intro f g
  refine not_imp_not.1 ?_
  simp only [Matrix.ext_iff.symm, toMatrix_apply, PEquiv.ext_iff, not_forall, exists_imp]
  intro i hi
  use i
  rcases hf : f i with - | fi
  · rcases hg : g i with - | gi
    · rw [hf, hg] at hi; exact (hi rfl).elim
    · use gi
      simp
  · use fi
    simp [hf.symm, Ne.symm hi]

set_option backward.isDefEq.respectTransparency false in
/-
**PEquiv.toMatrix_swap** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_swap [DecidableEq n] [AddGroupWithOne α] (i j : n) : (Equiv.swap 
i j).toPEquiv.toMatrix = (1 : Matrix n n α) - (single i i).toMatrix - (single j 
j).toMatrix + (single i j).toMatrix + (single j i).toMatrix
参数：i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem toMatrix_swap [DecidableEq n] [AddGroupWithOne α] (i j : n) :
    (Equiv.swap i j).toPEquiv.toMatrix =
      (1 : Matrix n n α) - (single i i).toMatrix - (single j j).toMatrix + (single i j).toMatrix +
        (single j i).toMatrix := by
  ext
  dsimp [toMatrix, single, Equiv.swap_apply_def, Equiv.toPEquiv, Matrix.one_apply]
  split_ifs <;> simp_all

@[simp]
/-
**PEquiv.single_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq
 n] [NonAssocSemiring α] (a : m) (b : n) (c : k) : ((single a b).toMatrix : Matr
ix _ _ α) * (single b c).toMatrix = (single a c).toMatrix
参数：a : m；b : n；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.toMatrix_trans`：toMatrix_trans [Fintype m] [DecidableEq m] [Decid
ableEq n] [NonAssocSemiring α] (f : l ≃. m) (g : m ≃. n) : ((f.trans g).toMatrix
 : Matrix l…
· 使用定理 `PEquiv.single_trans_single`：single_trans_single (a : α) (b : β) (c : γ) 
: (single a b).trans (single b c) = single a c
-/
theorem single_mul_single [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring α] (a : m) (b : n) (c : k) :
    ((single a b).toMatrix : Matrix _ _ α) * (single b c).toMatrix = (single a c).toMatrix := by
  rw [← toMatrix_trans, single_trans_single]
/-
**PEquiv.single_mul_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [Decid
ableEq m] [NonAssocSemiring α] {b₁ b₂ : n} (hb : b₁ != b₂) (a : m) (c : k) : (si
ngle a b₁).toMatrix * (single b₂ c).toMatrix = (0 : Matrix _ _ α)
参数：hb : b₁ != b₂；a : m；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.toMatrix_trans`：toMatrix_trans [Fintype m] [DecidableEq m] [Decid
ableEq n] [NonAssocSemiring α] (f : l ≃. m) (g : m ≃. n) : ((f.trans g).toMatrix
 : Matrix l…
· 使用定理 `PEquiv.single_trans_single_of_ne`：single_trans_single_of_ne {b₁ b₂ : β} 
(h : b₁ != b₂) (a : α) (c : γ) : (single a b₁).trans (single b₂ c) = ⊥
· 使用定理 `PEquiv.toMatrix_bot`：toMatrix_bot [DecidableEq n] [Zero α] [One α] : ((⊥
 : PEquiv m n).toMatrix : Matrix m n α) = 0
-/
theorem single_mul_single_of_ne [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    [NonAssocSemiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
    (single a b₁).toMatrix * (single b₂ c).toMatrix = (0 : Matrix _ _ α) := by
  rw [← toMatrix_trans, single_trans_single_of_ne hb, toMatrix_bot]

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp]
/-
**PEquiv.single_mul_single_right** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [Decidable
Eq k] [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) : 
(single a b).toMatrix * ((single b c).toMatrix * M) = (single a c).toMatrix * M
参数：a : m；b : n；c : k；M : Matrix k l α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `PEquiv.single_mul_single`：single_mul_single [Fintype n] [DecidableEq k] 
[DecidableEq m] [DecidableEq n] [NonAssocSemiring α] (a : m) (b : n) (c : k) : (
(single a b).t…

--- 原说明 ---
Restatement of `single_mul_single`, which will simplify expressions in `simp` no
rmal form,
  when associativity may otherwise need to be carefully applied.
-/
theorem single_mul_single_right [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    [DecidableEq m] [Semiring α] (a : m) (b : n) (c : k) (M : Matrix k l α) :
    (single a b).toMatrix * ((single b c).toMatrix * M) = (single a c).toMatrix * M := by
  rw [← Matrix.mul_assoc, single_mul_single]

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
/-
**PEquiv.toMatrix_toPEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：toMatrix_toPEquiv_eq [DecidableEq n] [Zero α] [One α] (σ : Equiv.Perm n) :
 σ.toPEquiv.toMatrix = (1 : Matrix n n α).submatrix σ id
参数：σ : Equiv.Perm n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b

--- 原说明 ---
We can also define permutation matrices by permuting the rows of the identity ma
trix.
-/
theorem toMatrix_toPEquiv_eq [DecidableEq n] [Zero α] [One α] (σ : Equiv.Perm n) :
    σ.toPEquiv.toMatrix = (1 : Matrix n n α).submatrix σ id :=
  Matrix.ext fun _ _ => if_congr Option.some_inj rfl rfl

@[simp]
/-
**PEquiv.map_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 `PEquiv`。
形式化陈述：map_toMatrix [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β] (f 
: α ->+* β) (σ : m ≃. n) : σ.toMatrix.map f = σ.toMatrix
参数：f : α ->+* β；σ : m ≃. n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_toMatrix [DecidableEq n] [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (σ : m ≃. n) : σ.toMatrix.map f = σ.toMatrix := by
  ext i j
  simp

end PEquiv

