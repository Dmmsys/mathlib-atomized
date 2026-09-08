/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.RowCol
/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.permanent`, and some of its properties.

## Main definitions

* `Matrix.permanent`: the permanent of a square matrix, as a sum over permutations

-/

@[expose] public section

open Equiv Fintype Finset

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommSemiring R]

/-- The permanent of a square matrix defined as a sum over all permutations. This is analogous to
the determinant but without alternating signs. -/
/-
**Matrix.permanent** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：permanent (M : Matrix n n R) : R
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permanent of a square matrix defined as a sum over all permutations. This is
 analogous to
the determinant but without alternating signs.
-/
def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i

@[simp]
/-
**Matrix.permanent_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_diagonal {d : n -> R} : permanent (diagonal d) = ∏ i, d i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
theorem permanent_diagonal {d : n → R} : permanent (diagonal d) = ∏ i, d i := by
  refine (sum_eq_single 1 (fun σ _ hσ ↦ ?_) (fun h ↦ (h <| mem_univ _).elim)).trans ?_
  · match not_forall.mp (mt Equiv.ext hσ) with
    | ⟨x, hx⟩ => exact Finset.prod_eq_zero (mem_univ x) (if_neg hx)
  · simp only [Perm.one_apply, diagonal_apply_eq]

@[simp]
/-
**Matrix.permanent_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_zero [Nonempty n] : permanent (0 : Matrix n n R) = 0
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
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permanent_zero [Nonempty n] : permanent (0 : Matrix n n R) = 0 := by simp [permanent]

@[simp]
/-
**Matrix.permanent_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_one : permanent (1 : Matrix n n R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_one`：diagonal_one : (diagonal fun _ => 1 : Matrix n n α)
 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.permanent_diagonal`：permanent_diagonal {d : n -> R} : permanent (
diagonal d) = ∏ i, d i
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permanent_one : permanent (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one]; simp [-diagonal_one]
/-
**Matrix.permanent_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_isEmpty [IsEmpty n] {A : Matrix n n R} : permanent A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permanent_isEmpty [IsEmpty n] {A : Matrix n n R} : permanent A = 1 := by simp [permanent]
/-
**Matrix.permanent_eq_one_of_card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : per
manent A = 1
参数：h : card n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.permanent_isEmpty`：permanent_isEmpty [IsEmpty n] {A : Matrix n n 
R} : permanent A = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
-/
theorem permanent_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : permanent A = 1 :=
  haveI : IsEmpty n := card_eq_zero_iff.mp h
  permanent_isEmpty

/-- If `n` has only one element, the permanent of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
/-
**Matrix.permanent_unique** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : M
atrix n n R) : permanent A = A default default
参数：A : Matrix n n R。
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
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `n` has only one element, the permanent of an `n` by `n` matrix is just that 
element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly.
-/
theorem permanent_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    permanent A = A default default := by simp [permanent, univ_unique]
/-
**Matrix.permanent_eq_elem_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k :
 n) : permanent A = A k k
参数：A : Matrix n n R；k : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Matrix.permanent_unique`：permanent_unique {n : Type*} [Unique n] [Decida
bleEq n] [Fintype n] (A : Matrix n n R) : permanent A = A default default
-/
theorem permanent_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    permanent A = A k k := by
  have := uniqueOfSubsingleton k
  convert! permanent_unique A
/-
**Matrix.permanent_eq_elem_of_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : 
n) : permanent A = A k k
参数：h : card n = 1；k : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.permanent_eq_elem_of_subsingleton`：permanent_eq_elem_of_subsingle
ton [Subsingleton n] (A : Matrix n n R) (k : n) : permanent A = A k k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton : car
d α <= 1 ↔ Subsingleton α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem permanent_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : n) :
    permanent A = A k k :=
  haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  permanent_eq_elem_of_subsingleton _ _

/-- Transposing a matrix preserves the permanent. -/
@[simp]
/-
**Matrix.permanent_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_transpose (M : Matrix n n R) : Mᵀ.permanent = M.permanent
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transposing a matrix preserves the permanent.
-/
theorem permanent_transpose (M : Matrix n n R) : Mᵀ.permanent = M.permanent := by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

/-- Permuting the columns does not change the permanent. -/
/-
**Matrix.permanent_permute_cols** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_permute_cols (σ : Perm n) (M : Matrix n n R) : (M.submatrix σ id
).permanent = M.permanent
参数：σ : Perm n；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Group.mulLeft_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Func
tion.Bijective fun x => a * x

--- 原说明 ---
Permuting the columns does not change the permanent.
-/
theorem permanent_permute_cols (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).permanent = M.permanent :=
  (Group.mulLeft_bijective σ).sum_comp fun τ ↦ ∏ i : n, M (τ i) i

/-- Permuting the rows does not change the permanent. -/
/-
**Matrix.permanent_permute_rows** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_permute_rows (σ : Perm n) (M : Matrix n n R) : (M.submatrix id σ
).permanent = M.permanent
参数：σ : Perm n；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.permanent_transpose`：permanent_transpose (M : Matrix n n R) : Mᵀ.
permanent = M.permanent
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.permanent_permute_cols`：permanent_permute_cols (σ : Perm n) (M : 
Matrix n n R) : (M.submatrix σ id).permanent = M.permanent

--- 原说明 ---
Permuting the rows does not change the permanent.
-/
theorem permanent_permute_rows (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).permanent = M.permanent := by
  rw [← permanent_transpose, transpose_submatrix, permanent_permute_cols, permanent_transpose]

@[simp]
/-
**Matrix.permanent_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_smul (M : Matrix n n R) (c : R) : permanent (c • M) = c ^ Fintyp
e.card n * permanent M
参数：M : Matrix n n R；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_pow_card`：prod_mul_pow_card {b : M} : (∏ a in s, f a) * 
b ^ #s = ∏ a in s, f a * b
-/
theorem permanent_smul (M : Matrix n n R) (c : R) :
    permanent (c • M) = c ^ Fintype.card n * permanent M := by
  simp only [permanent, smul_apply, smul_eq_mul, Finset.mul_sum]
  congr
  ext
  rw [mul_comm]
  conv in ∏ _, c * _ => simp [mul_comm c];
  exact prod_mul_pow_card.symm

@[simp]
/-
**Matrix.permanent_updateCol_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_updateCol_smul (M : Matrix n n R) (j : n) (c : R) (u : n -> R) :
 permanent (updateCol M j <| c • u) = c * permanent (updateCol M j u)
参数：M : Matrix n n R；j : n；c : R；u : n -> R。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permanent_updateCol_smul (M : Matrix n n R) (j : n) (c : R) (u : n → R) :
    permanent (updateCol M j <| c • u) = c * permanent (updateCol M j u) := by
  simp only [permanent, ← mul_prod_erase _ _ (mem_univ j), updateCol_self, Pi.smul_apply,
    smul_eq_mul, mul_sum, ← mul_assoc]
  congr 1 with p
  rw [Finset.prod_congr rfl (fun i hi ↦ ?_)]
  simp only [ne_eq, ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

@[simp]
/-
**Matrix.permanent_updateRow_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：permanent_updateRow_smul (M : Matrix n n R) (j : n) (c : R) (u : n -> R) :
 permanent (updateRow M j <| c • u) = c * permanent (updateRow M j u)
参数：M : Matrix n n R；j : n；c : R；u : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.permanent_transpose`：permanent_transpose (M : Matrix n n R) : Mᵀ.
permanent = M.permanent
· 使用定理 `Matrix.updateCol_transpose`：updateCol_transpose [DecidableEq m] : update
Col Mᵀ i b = (updateRow M i b)ᵀ
· 使用定理 `Matrix.permanent_updateCol_smul`：permanent_updateCol_smul (M : Matrix n 
n R) (j : n) (c : R) (u : n -> R) : permanent (updateCol M j <| c • u) = c * per
manent (updateCol M j…
-/
theorem permanent_updateRow_smul (M : Matrix n n R) (j : n) (c : R) (u : n → R) :
    permanent (updateRow M j <| c • u) = c * permanent (updateRow M j u) := by
  rw [← permanent_transpose, ← updateCol_transpose, permanent_updateCol_smul,
    updateCol_transpose, permanent_transpose]

end Matrix

