/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Wen Yang
-/
module

public import Mathlib.Data.Fintype.Parity
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `SpecialLinearGroup n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `SpecialLinearGroup n R` and the embedding into the general linear group
`GeneralLinearGroup R (n → R)`.

## Main definitions

* `Matrix.SpecialLinearGroup` is the type of matrices with determinant 1
* `Matrix.SpecialLinearGroup.group` gives the group structure (under multiplication)
* `Matrix.SpecialLinearGroup.toGL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = Fin m`, in the scope `MatrixGroups`.

## Implementation notes
The inverse operation in the `SpecialLinearGroup` is defined to be the adjugate
matrix, so that `SpecialLinearGroup n R` has a group structure for all `CommRing R`.

We define the elements of `SpecialLinearGroup` to be matrices, since we need to
compute their determinant. This is in contrast with `GeneralLinearGroup R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `Matrix.SpecialLinearGroup.hasCoeToFun` for convenience, but do not state any
lemmas about it, and use `Matrix.SpecialLinearGroup.coeFn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

* https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

@[expose] public section


namespace Matrix

universe u v

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- `SpecialLinearGroup n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
/-
**Matrix.SpecialLinearGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：SpecialLinearGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SpecialLinearGroup n R` is the group of `n` by `n` `R`-matrices with determinan
t equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }

end

@[inherit_doc]
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

/-- If `R` and `n` have decidable equality then so does `SL(n, R)`. -/
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` and `n` have decidable equality then so does `SL(n, R)`.
-/
instance [DecidableEq R] : DecidableEq (SpecialLinearGroup n R) := Subtype.instDecidableEq
/-
**Matrix.SpecialLinearGroup.hasCoeToMatrix** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.Spe
cialLinearGroup`。
形式化陈述：hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

/-- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : Matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup n R) : Matrix n n R)

section CoeFnInstance

/-- This instance is here for convenience, but is literally the same as the coercion from
`hasCoeToMatrix`. -/
/-
**Matrix.SpecialLinearGroup.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.Special
LinearGroup`。
形式化陈述：instCoeFun : CoeFun (SpecialLinearGroup n R) fun _ => n -> n -> R where co
e A
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is here for convenience, but is literally the same as the coercion
 from
`hasCoeToMatrix`.
-/
instance instCoeFun : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe A := ↑ₘA

end CoeFnInstance

/-
**Matrix.SpecialLinearGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ forall i j, A i j = B i j
参数：A B : SpecialLinearGroup n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
/-
**Matrix.SpecialLinearGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLinearG
roup`。
形式化陈述：ext (A B : SpecialLinearGroup n R) : (forall i j, A i j = B i j) -> A = B
参数：A B : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.SpecialLinearGroup.ext_iff`：ext_iff (A B : SpecialLinearGroup n R
) : A = B ↔ forall i j, A i j = B i j
-/
theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, A i j = B i j) → A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr
/-
**Matrix.SpecialLinearGroup.subsingleton_of_subsingleton** 是 Mathlib 中的一个实例，位于命名
空间 `Matrix.SpecialLinearGroup`。
形式化陈述：subsingleton_of_subsingleton [Subsingleton n] : Subsingleton (SpecialLinea
rGroup n R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Matrix.det_eq_elem_of_subsingleton`：det_eq_elem_of_subsingleton [Subsing
leton n] (A : Matrix n n R) (k : n) : det A = A k k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance subsingleton_of_subsingleton [Subsingleton n] : Subsingleton (SpecialLinearGroup n R) := by
  refine ⟨fun ⟨A, hA⟩ ⟨B, hB⟩ ↦ ?_⟩
  ext i j
  rcases isEmpty_or_nonempty n with hn | hn; · exfalso; exact IsEmpty.false i
  rw [det_eq_elem_of_subsingleton _ i] at hA hB
  simp only [Subsingleton.elim j i, hA, hB]
/-
**Matrix.SpecialLinearGroup.hasInv** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：hasInv : Inv (SpecialLinearGroup n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩
/-
**Matrix.SpecialLinearGroup.hasMul** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：hasMul : Mul (SpecialLinearGroup n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩
/-
**Matrix.SpecialLinearGroup.hasOne** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：hasOne : One (SpecialLinearGroup n R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
-/
instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (SpecialLinearGroup n R) ℕ where
  pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.prop.symm ▸ one_pow _⟩
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype R] [DecidableEq R] : Fintype (SpecialLinearGroup n R) := Subtype.fintype _
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite R] : Finite (SpecialLinearGroup n R) := Subtype.finite

/-- The transpose of a matrix in `SL(n, R)` -/
/-
**Matrix.SpecialLinearGroup.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R
参数：A : SpecialLinearGroup n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of a matrix in `SL(n, R)`
-/
def transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R :=
  ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

/-
**Matrix.SpecialLinearGroup.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup 
n R) = A
参数：A : Matrix n n R；h : det A = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：coe_inv : ↑ₘ(A⁻¹) = adjugate A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：coe_one : (1 : SpecialLinearGroup n R) = (1 : Matrix n n R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : (1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.det_coe** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：det_coe : det ↑ₘA = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem det_coe : det ↑ₘA = 1 :=
  A.2

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：coe_pow (m : Nat) : ↑ₘ(A ^ m) = ↑ₘA ^ m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_transpose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spec
ialLinearGroup`。
形式化陈述：coe_transpose (A : SpecialLinearGroup n R) : ↑ₘAᵀ = (↑ₘA)ᵀ
参数：A : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_transpose (A : SpecialLinearGroup n R) : ↑ₘAᵀ = (↑ₘA)ᵀ :=
  rfl
/-
**Matrix.SpecialLinearGroup.det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg != 0
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num
/-
**Matrix.SpecialLinearGroup.row_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : g i != 0
参数：g : SpecialLinearGroup n R；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : S
pecialLinearGroup n R) : det ↑ₘg != 0
· 使用定理 `Matrix.det_eq_zero_of_row_eq_zero`：det_eq_zero_of_row_eq_zero {A : Matri
x n n R} (i : n) (h : forall j, A i j = 0) : det A = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : g i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]

end CoeLemmas

/-
**Matrix.SpecialLinearGroup.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：monoid : Monoid (SpecialLinearGroup n R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.coe_one`：coe_one : (1 : SpecialLinearGroup n R
) = (1 : Matrix n n R)
· 使用定理 `Matrix.SpecialLinearGroup.coe_mul`：coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB
· 使用定理 `Matrix.SpecialLinearGroup.coe_pow`：coe_pow (m : Nat) : ↑ₘ(A ^ m) = ↑ₘA ^
 m
-/
instance monoid : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
/-
**Matrix.SpecialLinearGroup.toLin'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：toLin'_equiv : SpecialLinearGroup n R ≃* _root_.SpecialLinearGroup R (n ->
 R) where toFun A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Matrix.toLin' A` that produces linear equivalences.
-/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R where
  toFun A :=
    LinearEquiv.ofLinearMap (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul ↑ₘA ↑ₘB
/-
**Matrix.SpecialLinearGroup.toLin'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R]   (A : Matrix.SpecialLinearGroup n R) (v : n → R), (Matrix.S
pecialLinearGroup.toLin' A) v = (Matrix.toLin' ↑A) v
参数：A : Matrix.SpecialLinearGroup n R；v : n → R；Matrix.SpecialLinearGroup.toLin' 
A；Matrix.toLin' ↑A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl
/-
**Matrix.SpecialLinearGroup.toLin'_to_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.SpecialLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R]   (A : Matrix.SpecialLinearGroup n R), ↑(Matrix.SpecialLinea
rGroup.toLin' A) = Matrix.toLin' ↑A
参数：A : Matrix.SpecialLinearGroup n R；Matrix.SpecialLinearGroup.toLin' A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl
/-
**Matrix.SpecialLinearGroup.toLin'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
SpecialLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R]   (A : Matrix.SpecialLinearGroup n R) (v : n → R), (Matrix.S
pecialLinearGroup.toLin' A).symm v = (Matrix.toLin' ↑A⁻¹) v
参数：A : Matrix.SpecialLinearGroup n R；v : n → R；Matrix.SpecialLinearGroup.toLin' 
A；Matrix.toLin' ↑A⁻¹。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl
/-
**Matrix.SpecialLinearGroup.toLin'_symm_to_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix.SpecialLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R]   (A : Matrix.SpecialLinearGroup n R), ↑(Matrix.SpecialLinea
rGroup.toLin' A).symm = Matrix.toLin' ↑A⁻¹
参数：A : Matrix.SpecialLinearGroup n R；Matrix.SpecialLinearGroup.toLin' A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl
/-
**Matrix.SpecialLinearGroup.toLin'_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [i
nst_2 : CommRing R],   Function.Injective ⇑Matrix.SpecialLinearGroup.toLin'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
-/
theorem toLin'_injective :
    Function.Injective ↑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun _ _ h =>
  Subtype.coe_injective <| Matrix.toLin'.injective <| LinearEquiv.toLinearMap_injective.eq_iff.mpr h

variable {S : Type*} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`SpecialLinearGroup n R` to `SpecialLinearGroup n S`. -/
@[simps]
/-
**Matrix.SpecialLinearGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLinearG
roup`。
形式化陈述：map (f : R ->+* S) : SpecialLinearGroup n R ->* SpecialLinearGroup n S whe
re toFun g
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism from `R` to `S` induces a group homomorphism from
`SpecialLinearGroup n R` to `SpecialLinearGroup n S`.
-/
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S where
  toFun g :=
    ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul ↑ₘx ↑ₘy

section center

open Subgroup

@[simp]
/-
**Matrix.SpecialLinearGroup.center_eq_bot_of_subsingleton** 是 Mathlib 中的一个定理，位于命
名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：center_eq_bot_of_subsingleton [Subsingleton n] : center (SpecialLinearGrou
p n R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem center_eq_bot_of_subsingleton [Subsingleton n] :
    center (SpecialLinearGroup n R) = ⊥ :=
  eq_bot_iff.mpr fun x _ ↦ by rw [mem_bot, Subsingleton.elim x 1]
/-
**Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center** 是 Mathlib 中的一个定理，位于命名
空间 `Matrix.SpecialLinearGroup`。
形式化陈述：scalar_eq_self_of_mem_center {A : SpecialLinearGroup n R} (hA : A in cente
r (SpecialLinearGroup n R)) (i : n) : scalar n (A i i) = A
参数：hA : A in center (SpecialLinearGroup n R)；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mem_range_scalar_of_commute_transvectionStruct`：∀ {n : Type u_1} 
{R : Type u₂} [inst : DecidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n] 
{M : Matrix n n R},   (∀ (t : Matrix.Transv…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.TransvectionStruct.det`：∀ {n : Type u_1} {R : Type u₂} [inst : De
cidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n]   (t : Matrix.Transvecti
onStruct n R), t.to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
theorem scalar_eq_self_of_mem_center
    {A : SpecialLinearGroup n R} (hA : A ∈ center (SpecialLinearGroup n R)) (i : n) :
    scalar n (A i i) = A := by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t ↦
    Subtype.ext_iff.mp <| Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]
/-
**Matrix.SpecialLinearGroup.scalar_eq_coe_self_center** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix.SpecialLinearGroup`。
形式化陈述：scalar_eq_coe_self_center (A : center (SpecialLinearGroup n R)) (i : n) : 
scalar n ((A : Matrix n n R) i i) = A
参数：A : center (SpecialLinearGroup n R)；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center`：scalar_eq_self_o
f_mem_center {A : SpecialLinearGroup n R} (hA : A in center (SpecialLinearGroup 
n R)) (i : n) : scalar n (A i i) = A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem scalar_eq_coe_self_center
    (A : center (SpecialLinearGroup n R)) (i : n) :
    scalar n ((A : Matrix n n R) i i) = A :=
  scalar_eq_self_of_mem_center A.property i

/-- The center of a special linear group of degree `n` is the subgroup of scalar matrices, for which
the scalars are the `n`-th roots of unity. -/
/-
**Matrix.SpecialLinearGroup.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Spe
cialLinearGroup`。
形式化陈述：mem_center_iff {A : SpecialLinearGroup n R} : A in center (SpecialLinearGr
oup n R) ↔ exists (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.SpecialLinearGroup.center_eq_bot_of_subsingleton`：center_eq_bot_o
f_subsingleton [Subsingleton n] : center (SpecialLinearGroup n R) = ⊥
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center`：scalar_eq_self_o
f_mem_center {A : SpecialLinearGroup n R} (hA : A in center (SpecialLinearGroup 
n R)) (i : n) : scalar n (A i i) = A
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Matrix.scalar_commute`：scalar_commute (r : α) (hr : forall r', Commute r
 r') (M : Matrix n n α) : Commute (scalar n r) M
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
The center of a special linear group of degree `n` is the subgroup of scalar mat
rices, for which
the scalars are the `n`-th roots of unity.
-/
theorem mem_center_iff {A : SpecialLinearGroup n R} :
    A ∈ center (SpecialLinearGroup n R) ↔ ∃ (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h ↦ ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ ↦ Subgroup.mem_center_iff.mpr fun B ↦ ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    simpa using! this
  · exact scalar_eq_self_of_mem_center h i
  · suffices ↑ₘ(B * A) = ↑ₘ(A * B) from Subtype.val_injective this
    simpa only [coe_mul, ← hr] using! (scalar_commute (n := n) r (Commute.all r) B).symm

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity. -/
@[simps]
/-
**Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'** 是 Mathlib 中的一个定义，位于命名空间
 `Matrix.SpecialLinearGroup`。
形式化陈述：center_equiv_rootsOfUnity' (i : n) : center (SpecialLinearGroup n R) ≃* ro
otsOfUnity (Fintype.card n) R where toFun A
参数：i : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of groups, from the center of the special linear group to the roo
ts of unity.
-/
def center_equiv_rootsOfUnity' (i : n) :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n) R where
  toFun A :=
    haveI : Nonempty n := ⟨i⟩
    rootsOfUnity.mkOfPowEq (↑ₘA i i) <| by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
    Subgroup.mem_center_iff.mpr fun B ↦ Subtype.val_injective <| by simp [coe_mul]⟩
  left_inv A := by
    refine SetCoe.ext <| SetCoe.ext ?_
    obtain ⟨r, _, hr⟩ := mem_center_iff.mp A.property
    simpa [← hr, Submonoid.smul_def, Units.smul_def] using! smul_one_eq_diagonal r
  right_inv a := by
    obtain ⟨⟨a, _⟩, ha⟩ := a
    exact SetCoe.ext <| Units.ext <| by simp
  map_mul' A B := by
    dsimp
    ext
    simp only [rootsOfUnity.val_mkOfPowEq_coe, Subgroup.coe_mul, Units.val_mul]
    rw [← scalar_eq_coe_self_center A i, ← scalar_eq_coe_self_center B i]
    simp

open scoped Classical in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity.

See also `center_equiv_rootsOfUnity'`. -/
/-
**Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 
`Matrix.SpecialLinearGroup`。
形式化陈述：center_equiv_rootsOfUnity : center (SpecialLinearGroup n R) ≃* rootsOfUnit
y (max (Fintype.card n) 1) R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α

--- 原说明 ---
An equivalence of groups, from the center of the special linear group to the roo
ts of unity.

See also `center_equiv_rootsOfUnity'`.
-/
noncomputable def center_equiv_rootsOfUnity :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (max (Fintype.card n) 1) R :=
  (isEmpty_or_nonempty n).by_cases
  (fun hn ↦ by
    rw [center_eq_bot_of_subsingleton, Fintype.card_eq_zero, max_eq_right_of_lt zero_lt_one,
      rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ ↦
    (max_eq_left (NeZero.one_le : 1 ≤ Fintype.card n)).symm ▸
      center_equiv_rootsOfUnity' (Classical.arbitrary n))
/-
**Matrix.SpecialLinearGroup.eq_scalar_center_equiv_rootsOfUnity** 是 Mathlib 中的一个
定理，位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：eq_scalar_center_equiv_rootsOfUnity (A : center (SpecialLinearGroup n R)) 
: A = scalar n ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity A : Rˣ) : R
)
参数：A : center (SpecialLinearGroup n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'_apply`：∀ {n : Type 
u} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R
] (i : n)   (A : ↥(Subgroup.center (Matrix.Speci…
· 使用定理 `rootsOfUnity.val_mkOfPowEq_coe`：∀ {M : Type u_1} [inst : CommMonoid M] (
ζ : M) {n : ℕ} [inst_1 : NeZero n] (h : ζ ^ n = 1),   ↑↑(rootsOfUnity.mkOfPowEq 
ζ h) = ζ
· 使用定理 `Matrix.SpecialLinearGroup.scalar_eq_coe_self_center`：scalar_eq_coe_self_
center (A : center (SpecialLinearGroup n R)) (i : n) : scalar n ((A : Matrix n n
 R) i i) = A
-/
theorem eq_scalar_center_equiv_rootsOfUnity
    (A : center (SpecialLinearGroup n R)) :
    A = scalar n ((Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity A : Rˣ) : R) := by
  unfold center_equiv_rootsOfUnity Or.by_cases
  split_ifs with h
  · subsingleton
  dsimp only
  generalize_proofs _ eq
  generalize max (Fintype.card n) 1 = c at eq
  subst eq
  rw [center_equiv_rootsOfUnity'_apply, rootsOfUnity.val_mkOfPowEq_coe,
    scalar_eq_coe_self_center]

end center

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`.
-/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩
/-
**Matrix.SpecialLinearGroup.coe_matrix_coe** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Spe
cialLinearGroup`。
形式化陈述：coe_matrix_coe (g : SpecialLinearGroup n Int) : ↑(g : SpecialLinearGroup n
 R) = (↑g : Matrix n n Int).map (Int.castRingHom R)
参数：g : SpecialLinearGroup n Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
-/
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g
/-
**Matrix.SpecialLinearGroup.map_intCast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Mat
rix.SpecialLinearGroup`。
形式化陈述：map_intCast_injective [CharZero R] : Function.Injective ((↑) : SpecialLine
arGroup n Int -> SpecialLinearGroup n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
-/
lemma map_intCast_injective [CharZero R] :
    Function.Injective ((↑) : SpecialLinearGroup n ℤ → SpecialLinearGroup n R) := fun g h ↦ by
  simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

@[simp]
/-
**Matrix.SpecialLinearGroup.map_intCast_inj** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Sp
ecialLinearGroup`。
形式化陈述：map_intCast_inj [CharZero R] {x y : SpecialLinearGroup n Int} : (x : Speci
alLinearGroup n R) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Matrix.SpecialLinearGroup.map_intCast_injective`：map_intCast_injective [
CharZero R] : Function.Injective ((↑) : SpecialLinearGroup n Int -> SpecialLinea
rGroup n R)
-/
lemma map_intCast_inj [CharZero R] {x y : SpecialLinearGroup n ℤ} :
    (x : SpecialLinearGroup n R) = y ↔ x = y :=
  map_intCast_injective.eq_iff

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
/-
**Matrix.SpecialLinearGroup.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：instNeg : Neg (SpecialLinearGroup n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal operation of negation on special linear group on even cardinality `n` giv
en by negating
each element.
-/
instance instNeg : Neg (SpecialLinearGroup n R) :=
  ⟨fun g => ⟨-g, by
    simpa [(@Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe]
      using det_smul (↑ₘg) (-1)⟩⟩

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R)
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
/-
**Matrix.SpecialLinearGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.SpecialLinearGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
/-
**Matrix.SpecialLinearGroup.coe_int_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Specia
lLinearGroup`。
形式化陈述：coe_int_neg (g : SpecialLinearGroup n Int) : ↑(-g) = (-↑g : SpecialLinearG
roup n R)
参数：g : SpecialLinearGroup n Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
-/
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

end Neg

section SpecialCases

open scoped MatrixGroups

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.SpecialLinearGroup.SL2_inv_expl_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：SL2_inv_expl_det (A : SL(2, R)) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, 
A.1 0 0]] = 1
参数：A : SL(2, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem SL2_inv_expl_det (A : SL(2, R)) :
    det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 := by
  simpa [-det_coe, Matrix.det_fin_two, mul_comm] using A.2
/-
**Matrix.SpecialLinearGroup.SL2_inv_expl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：SL2_inv_expl (A : SL(2, R)) : A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A
.1 0 0]], SL2_inv_expl_det A⟩
参数：A : SL(2, R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.SpecialLinearGroup.SL2_inv_expl_det`：SL2_inv_expl_det (A : SL(2, 
R)) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1
· 使用定理 `Matrix.adjugate_fin_two`：adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α)
 : adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.coe_inv`：coe_inv : ↑ₘ(A⁻¹) = adjugate A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ := by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [coe_inv, this]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.SpecialLinearGroup.fin_two_induction** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
SpecialLinearGroup`。
形式化陈述：fin_two_induction (P : SL(2, R) -> Prop) (h : forall (a b c d : R) (hdet :
 a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩) (g : SL(2, R))
 : P g
参数：P : SL(2, R) -> Prop；h : forall (a b c d : R) (hdet : a * d - b * c = 1), P ⟨
!![a, b; c, d], by rwa [det_fin_two_of]⟩；g : SL(2, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem fin_two_induction (P : SL(2, R) → Prop)
    (h : ∀ (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩)
    (g : SL(2, R)) : P g := by
  obtain ⟨m, hm⟩ := g
  convert! h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext i j; fin_cases i <;> fin_cases j <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero** 是 M
athlib 中的一个定理，位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type*} [Field R] (g : 
SL(2, R)) (hg : g 1 0 = 0) : exists (a b : R) (h : a != 0), g = (⟨!![a, b; 0, a⁻
¹], by simp [h]⟩ : SL(2, R))
参数：g : SL(2, R)；hg : g 1 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.SpecialLinearGroup.fin_two_induction`：fin_two_induction (P : SL(2
, R) -> Prop) (h : forall (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; 
c, d], by rwa [det_fin_two_of]⟩) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `left_ne_zero_of_mul_eq_one`：left_ne_zero_of_mul_eq_one (h : a * b = 1) :
 a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_inv_of_mul_eq_one_right`：eq_inv_of_mul_eq_one_right (h : a * b = 1) :
 b = a⁻¹
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type*} [Field R] (g : SL(2, R))
    (hg : g 1 0 = 0) :
    ∃ (a b : R) (h : a ≠ 0), g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, R)) := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d h_det =>
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, mul_zero, sub_zero] at h_det
  refine ⟨a, b, left_ne_zero_of_mul_eq_one had, ?_⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]
/-
**Matrix.SpecialLinearGroup.isCoprime_row** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spec
ialLinearGroup`。
形式化陈述：isCoprime_row (A : SL(2, R)) (i : Fin 2) : IsCoprime (A i 0) (A i 1)
参数：A : SL(2, R)；i : Fin 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 33 条，此处仅展示前 30 条）
-/
lemma isCoprime_row (A : SL(2, R)) (i : Fin 2) : IsCoprime (A i 0) (A i 1) := by
  refine match i with
  | 0 => ⟨A 1 1, -(A 1 0), ?_⟩
  | 1 => ⟨-(A 0 1), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring
/-
**Matrix.SpecialLinearGroup.isCoprime_col** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spec
ialLinearGroup`。
形式化陈述：isCoprime_col (A : SL(2, R)) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j)
参数：A : SL(2, R)；j : Fin 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 33 条，此处仅展示前 30 条）
-/
lemma isCoprime_col (A : SL(2, R)) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j) := by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

end SpecialCases

end SpecialLinearGroup

end Matrix

namespace IsCoprime

open Matrix MatrixGroups SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` having those
entries as its left or right column. -/
/-
**IsCoprime.exists_SL2_col** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：exists_SL2_col {a b : R} (hab : IsCoprime a b) (j : Fin 2) : exists g : SL
(2, R), g 0 j = a ∧ g 1 j = b
参数：hab : IsCoprime a b；j : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` h
aving those
entries as its left or right column.
-/
lemma exists_SL2_col {a b : R} (hab : IsCoprime a b) (j : Fin 2) :
    ∃ g : SL(2, R), g 0 j = a ∧ g 1 j = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match j with
  | 0 => ⟨⟨!![a, -v; b, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, a; -u, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/-- Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` having those
entries as its top or bottom row. -/
/-
**IsCoprime.exists_SL2_row** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：exists_SL2_row {a b : R} (hab : IsCoprime a b) (i : Fin 2) : exists g : SL
(2, R), g i 0 = a ∧ g i 1 = b
参数：hab : IsCoprime a b；i : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` h
aving those
entries as its top or bottom row.
-/
lemma exists_SL2_row {a b : R} (hab : IsCoprime a b) (i : Fin 2) :
    ∃ g : SL(2, R), g i 0 = a ∧ g i 1 = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match i with
  | 0 => ⟨⟨!![a, b; -v, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, -u; a, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/-- A vector with coprime entries, right-multiplied by a matrix in `SL(2, R)`, has
coprime entries. -/
/-
**IsCoprime.vecMulSL** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：vecMulSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) : I
sCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1)
参数：hab : IsCoprime (v 0) (v 1)；A : SL(2, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `IsCoprime.exists_SL2_row`：exists_SL2_row {a b : R} (hab : IsCoprime a b)
 (i : Fin 2) : exists g : SL(2, R), g i 0 = a ∧ g i 1 = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.SpecialLinearGroup.isCoprime_row`：isCoprime_row (A : SL(2, R)) (i
 : Fin 2) : IsCoprime (A i 0) (A i 1)

--- 原说明 ---
A vector with coprime entries, right-multiplied by a matrix in `SL(2, R)`, has
coprime entries.
-/
lemma vecMulSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1) := by
  obtain ⟨g, hg⟩ := hab.exists_SL2_row 0
  have : v = g 0 := funext fun t ↦ by { fin_cases t <;> tauto }
  simpa only [this] using! isCoprime_row (g * A) 0

/-- A vector with coprime entries, left-multiplied by a matrix in `SL(2, R)`, has
coprime entries. -/
/-
**IsCoprime.mulVecSL** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：mulVecSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) : I
sCoprime ((A.1 *ᵥ v) 0) ((A.1 *ᵥ v) 1)
参数：hab : IsCoprime (v 0) (v 1)；A : SL(2, R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `IsCoprime.vecMulSL`：vecMulSL {v : Fin 2 -> R} (hab : IsCoprime (v 0) (v 
1)) (A : SL(2, R)) : IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1)

--- 原说明 ---
A vector with coprime entries, left-multiplied by a matrix in `SL(2, R)`, has
coprime entries.
-/
lemma mulVecSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((A.1 *ᵥ v) 0) ((A.1 *ᵥ v) 1) := by
  simpa only [← vecMul_transpose] using! hab.vecMulSL A.transpose

end IsCoprime

namespace Matrix

section Action

variable {F : Type*} [CommRing F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction (Matrix.SpecialLinearGroup ι F) (ι → F) where
  smul m v := m.1 • v
  smul_zero _ := smul_zero (M := Matrix ι ι F) _
  smul_add _ := smul_add (M := Matrix ι ι F) _
  one_smul _ := one_smul (M := Matrix ι ι F) _
  mul_smul _ _ _ := SemigroupAction.mul_smul (α := Matrix ι ι F) _ _ _
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass (Matrix.SpecialLinearGroup ι F) F (ι → F) where
  smul_comm m k v := show m.1 • k • v = k • m.1 • v from smul_comm _ _ _
/-
**Matrix.SpecialLinearGroup.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLi
nearGroup`。
形式化陈述：∀ {F : Type u_1} [inst : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq 
ι] [inst_2 : Fintype ι]   (m : Matrix.SpecialLinearGroup ι F) (v : ι → F), m • v
 = ↑m • v
参数：m : Matrix.SpecialLinearGroup ι F；v : ι → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma SpecialLinearGroup.smul_def
    (m : Matrix.SpecialLinearGroup ι F) (v : ι → F) :
    m • v = m.1 • v := rfl

end Action

section transvection

variable {ι F : Type*} [DecidableEq ι] [Fintype ι] [CommRing F]

/-- The transvection `1 + b · E_{i,j}` (the identity plus `b` in position `(i, j)`)
as an element of `SL ι F`, when `i ≠ j`. -/
/-
**Matrix.SpecialLinearGroup.transvection** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：{ι : Type u_1} →   {F : Type u_2} →     [inst : DecidableEq ι] →       [in
st_1 : Fintype ι] → [inst_2 : CommRing F] → {i j : ι} → i ≠ j → F → Matrix.Speci
alLinearGroup ι F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_transvection_of_ne`：det_transvection_of_ne (h : i != j) (c : 
R) : det (transvection i j c) = 1

--- 原说明 ---
The transvection `1 + b · E_{i,j}` (the identity plus `b` in position `(i, j)`)
as an element of `SL ι F`, when `i ≠ j`.
-/
def SpecialLinearGroup.transvection {i j : ι} (hij : i ≠ j) (b : F) :
    Matrix.SpecialLinearGroup ι F :=
  ⟨Matrix.transvection i j b, Matrix.det_transvection_of_ne i j hij b⟩

namespace SpecialLinearGroup

/-
**Matrix.SpecialLinearGroup.transvection_coe** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：transvection_coe {i j : ι} (hij : i != j) (b : F) : (transvection hij b) =
 (1 : Matrix ι ι F) + single i j b
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transvection_coe {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b) = (1 : Matrix ι ι F) + single i j b := rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.transvection_coeff_zero** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix.SpecialLinearGroup`。
形式化陈述：transvection_coeff_zero {i j : ι} (hij : i != j) : transvection hij (0 : F
) = 1
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transvection_coeff_zero {i j : ι} (hij : i ≠ j) :
    transvection hij (0 : F) = 1 := by ext; simp [transvection_coe]

/-- The transvection `transvection i j hij b` acts on `e_i = Pi.single i 1` as the identity. -/
/-
**Matrix.SpecialLinearGroup.transvection_smul_single_fst** 是 Mathlib 中的一个引理，位于命名
空间 `Matrix.SpecialLinearGroup`。
形式化陈述：transvection_smul_single_fst {i j : ι} (hij : i != j) (b : F) : (transvect
ion hij b) • (Pi.single i 1 : ι -> F) = Pi.single i 1
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用引理 `Matrix.single_mulVec_eq`：single_mulVec_eq [Fintype n] [NonAssocSemiring 
α] (i j : n) (b : α) (w : n -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i 
(1 : α)
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The transvection `transvection i j hij b` acts on `e_i = Pi.single i 1` as the i
dentity.
-/
lemma transvection_smul_single_fst {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b) • (Pi.single i 1 : ι → F) = Pi.single i 1 := by
  simp [SpecialLinearGroup.smul_def, -mulVec_single, transvection_coe,
    add_mulVec, single_mulVec_eq, hij]

@[deprecated transvection_smul_single_fst (since := "2026-06-22")]
/-
**Matrix.SpecialLinearGroup.transvection_mulVec_single_self** 是 Mathlib 中的一个引理，位
于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：transvection_mulVec_single_self {i j : ι} (hij : i != j) (b : F) : (transv
ection hij b).1 *ᵥ (Pi.single i (1 : F)) = Pi.single i 1
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.SpecialLinearGroup.transvection_coe`：transvection_coe {i j : ι} (
hij : i != j) (b : F) : (transvection hij b) = (1 : Matrix ι ι F) + single i j b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用引理 `Matrix.single_mulVec_eq`：single_mulVec_eq [Fintype n] [NonAssocSemiring 
α] (i j : n) (b : α) (w : n -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i 
(1 : α)
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transvection_mulVec_single_self {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b).1 *ᵥ (Pi.single i (1 : F)) = Pi.single i 1 := by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq, hij]

/-- The transvection `transvection i j hij b` acts on `e_j = Pi.single j 1` by adding `b·e_i`. -/
/-
**Matrix.SpecialLinearGroup.transvection_smul_single_snd** 是 Mathlib 中的一个引理，位于命名
空间 `Matrix.SpecialLinearGroup`。
形式化陈述：transvection_smul_single_snd {i j : ι} (hij : i != j) (b : F) : (transvect
ion hij b) • (Pi.single j 1 : ι -> F) = Pi.single j 1 + b • Pi.single i 1
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用引理 `Matrix.single_mulVec_eq`：single_mulVec_eq [Fintype n] [NonAssocSemiring 
α] (i j : n) (b : α) (w : n -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i 
(1 : α)
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The transvection `transvection i j hij b` acts on `e_j = Pi.single j 1` by addin
g `b·e_i`.
-/
lemma transvection_smul_single_snd {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b) • (Pi.single j 1 : ι → F) = Pi.single j 1 + b • Pi.single i 1 := by
  simp [SpecialLinearGroup.smul_def, transvection_coe, -mulVec_single,
    add_mulVec, single_mulVec_eq]

@[deprecated transvection_smul_single_snd (since := "2026-06-22")]
/-
**Matrix.SpecialLinearGroup.transvection_mulVec_single_other** 是 Mathlib 中的一个引理，
位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：transvection_mulVec_single_other {i j : ι} (hij : i != j) (b : F) : (trans
vection hij b).1 *ᵥ (Pi.single j (1 : F)) = Pi.single j 1 + b • Pi.single i 1
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.SpecialLinearGroup.transvection_coe`：transvection_coe {i j : ι} (
hij : i != j) (b : F) : (transvection hij b) = (1 : Matrix ι ι F) + single i j b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用引理 `Matrix.single_mulVec_eq`：single_mulVec_eq [Fintype n] [NonAssocSemiring 
α] (i j : n) (b : α) (w : n -> α) : single i j b *ᵥ w = (b * w j) • Pi.single i 
(1 : α)
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transvection_mulVec_single_other {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b).1 *ᵥ (Pi.single j (1 : F)) = Pi.single j 1 + b • Pi.single i 1 := by
  rw [transvection_coe]
  simp [-mulVec_single, add_mulVec, single_mulVec_eq]

/-- Inverse of a transvection: `transvection i j hij b * transvection i j hij (-b) = 1`. -/
/-
**Matrix.SpecialLinearGroup.transvection_mul_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matr
ix.SpecialLinearGroup`。
形式化陈述：transvection_mul_neg {i j : ι} (hij : i != j) (b : F) : transvection hij b
 * transvection hij (-b) = 1
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.single_mul_single_of_ne`：single_mul_single_of_ne (i : l) (j k : m
) {l : n} (h : j != k) (d : α) : single i j c * single k l d = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Inverse of a transvection: `transvection i j hij b * transvection i j hij (-b) =
 1`.
-/
lemma transvection_mul_neg {i j : ι} (hij : i ≠ j) (b : F) :
    transvection hij b * transvection hij (-b) = 1 := Subtype.ext <| by
  simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]
/-
**Matrix.SpecialLinearGroup.transvection_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：transvection_inv {i j : ι} (hij : i != j) (b : F) : (transvection hij b)⁻¹
 = transvection hij (-b)
参数：hij : i != j；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_left`：inv_eq_of_mul_eq_one_left (h : a * b = 1) : b
⁻¹ = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.SpecialLinearGroup.transvection_mul_neg`：transvection_mul_neg {i 
j : ι} (hij : i != j) (b : F) : transvection hij b * transvection hij (-b) = 1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma transvection_inv {i j : ι} (hij : i ≠ j) (b : F) :
    (transvection hij b)⁻¹ = transvection hij (-b) :=
  inv_eq_of_mul_eq_one_left (by rw [← transvection_mul_neg hij (-b), neg_neg])
/-
**Matrix.SpecialLinearGroup.transvection_add** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.S
pecialLinearGroup`。
形式化陈述：transvection_add {i j : ι} (hij : i != j) (b₁ b₂ : F) : transvection hij (
b₁ + b₂) = transvection hij b₁ * transvection hij b₂
参数：hij : i != j；b₁ b₂ : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_add`：single_add [AddZeroClass α] (i : m) (j : n) (a b : α)
 : single i j (a + b) = single i j a + single i j b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.single_mul_single_of_ne`：single_mul_single_of_ne (i : l) (j k : m
) {l : n} (h : j != k) (d : α) : single i j c * single k l d = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transvection_add {i j : ι} (hij : i ≠ j) (b₁ b₂ : F) :
    transvection hij (b₁ + b₂) = transvection hij b₁ * transvection hij b₂ :=
  Subtype.ext <| by simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_add, add_assoc]
/-
**Matrix.SpecialLinearGroup.transvection_mem_center_iff** 是 Mathlib 中的一个引理，位于命名空
间 `Matrix.SpecialLinearGroup`。
形式化陈述：transvection_mem_center_iff {i j : ι} (hij : i != j) (b : F) : transvectio
n hij b in Subgroup.center (SpecialLinearGroup ι F) ↔ b = 0
参数：hij : i != j；b : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.SpecialLinearGroup.mem_center_iff`：mem_center_iff {A : SpecialLin
earGroup n R} : A in center (SpecialLinearGroup n R) ↔ exists (r : R), r ^ (Fint
ype.card n) = 1 ∧ scalar n r =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.SpecialLinearGroup.transvection.congr_simp`：∀ {ι : Type u_1} {F :
 Type u_2} [inst : DecidableEq ι] [inst_1 : Fintype ι] [inst_2 : CommRing F] {i 
i_1 : ι}   (e_i : i = i_1) {j j_1 : ι} …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma transvection_mem_center_iff {i j : ι} (hij : i ≠ j) (b : F) :
    transvection hij b ∈ Subgroup.center (SpecialLinearGroup ι F) ↔ b = 0 := by
  refine ⟨fun h ↦ ?_, fun hb ↦ ?_⟩
  · obtain ⟨r, _, hr⟩ := mem_center_iff.1 h
    simpa [transvection_coe, hij] using congr($hr i j).symm
  · simp only [hb, mem_center_iff, scalar_apply, transvection_coe, single_zero,
      add_zero, diagonal_eq_one]
    exact ⟨1, one_pow _, rfl⟩

end SpecialLinearGroup

namespace TransvectionStruct

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Any transvection structure can be converted to a special linear matrix. -/
/-
**Matrix.TransvectionStruct.toSpecialLinearGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matr
ix.TransvectionStruct`。
形式化陈述：toSpecialLinearGroup (t : TransvectionStruct ι F) : SpecialLinearGroup ι F
参数：t : TransvectionStruct ι F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.TransvectionStruct.hij`：∀ {n : Type u_1} {R : Type u₂} (self : Ma
trix.TransvectionStruct n R), self.i ≠ self.j

--- 原说明 ---
Any transvection structure can be converted to a special linear matrix.
-/
def toSpecialLinearGroup (t : TransvectionStruct ι F) :
    SpecialLinearGroup ι F :=
  SpecialLinearGroup.transvection t.hij t.c
/-
**Matrix.TransvectionStruct.toSpecialLinearGroup_def** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix.TransvectionStruct`。
形式化陈述：toSpecialLinearGroup_def (t : TransvectionStruct ι F) : t.toSpecialLinearG
roup = SpecialLinearGroup.transvection t.hij t.c
参数：t : TransvectionStruct ι F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecialLinearGroup_def (t : TransvectionStruct ι F) :
    t.toSpecialLinearGroup = SpecialLinearGroup.transvection t.hij t.c := rfl

@[simp]
/-
**Matrix.TransvectionStruct.toSpecialLinearGroup_coe** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix.TransvectionStruct`。
形式化陈述：toSpecialLinearGroup_coe (t : TransvectionStruct ι F) : (t.toSpecialLinear
Group : Matrix ι ι F) = t.toMatrix
参数：t : TransvectionStruct ι F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecialLinearGroup_coe (t : TransvectionStruct ι F) :
    (t.toSpecialLinearGroup : Matrix ι ι F) = t.toMatrix := rfl

@[simp]
/-
**Matrix.TransvectionStruct.toSpecialLinearGroup_mk** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix.TransvectionStruct`。
形式化陈述：toSpecialLinearGroup_mk {i j : ι} (hij : i != j) (c : F) : (TransvectionSt
ruct.mk i j hij c).toSpecialLinearGroup = SpecialLinearGroup.transvection hij c
参数：hij : i != j；c : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSpecialLinearGroup_mk {i j : ι} (hij : i ≠ j) (c : F) :
    (TransvectionStruct.mk i j hij c).toSpecialLinearGroup =
      SpecialLinearGroup.transvection hij c := rfl

end TransvectionStruct

end transvection

section SL2

variable {F : Type*} [Field F]

open MatrixGroups

namespace SpecialLinearGroup

/-- An element in SLₙ(F) induced by a diagonal matrix `1` on any other entries and `a`, `a⁻¹` on
  positition `i` and `j` respectively where `i ≠ j`. -/
/-
**Matrix.SpecialLinearGroup.diag2n** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.SpecialLine
arGroup`。
形式化陈述：diag2n {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j) (a
 : F) (ha : a != 0) : SpecialLinearGroup ι F
参数：hij : i != j；a : F；ha : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element in SLₙ(F) induced by a diagonal matrix `1` on any other entries and `
a`, `a⁻¹` on
  positition `i` and `j` respectively where `i ≠ j`.
-/
noncomputable def diag2n {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (a : F)
    (ha : a ≠ 0) : SpecialLinearGroup ι F :=
  ⟨diagonal (fun k ↦ if k = i then a else if k = j then a⁻¹ else 1), by
    simp [Finset.prod_ite, hij.symm, Finset.card_eq_one (s := {x : ι | x = i}).2 ⟨i, by grind⟩,
      mul_inv_cancel₀ ha]⟩
/-
**Matrix.SpecialLinearGroup.diag2n_coe** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Special
LinearGroup`。
形式化陈述：diag2n_coe {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i != j
) (a : F) (ha : a != 0) : (diag2n hij a ha).1 = diagonal (fun k => if k = i then
 a else if k = j then a⁻¹ else 1)
参数：hij : i != j；a : F；ha : a != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diag2n_coe {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (a : F)
    (ha : a ≠ 0) : (diag2n hij a ha).1 = diagonal (fun k ↦
      if k = i then a else if k = j then a⁻¹ else 1) := rfl

/-- An element in SL₂(F) induced by a diagonal matrix with `a`, `a⁻¹` on
  positition `0` and `1` respectively. -/
/-
**Matrix.SpecialLinearGroup.diag2** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：diag2 (a : F) (ha : a != 0) : SL(2, F)
参数：a : F；ha : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element in SL₂(F) induced by a diagonal matrix with `a`, `a⁻¹` on
  positition `0` and `1` respectively.
-/
noncomputable abbrev diag2 (a : F) (ha : a ≠ 0) : SL(2, F) :=
  diag2n zero_ne_one a ha
/-
**Matrix.SpecialLinearGroup.diag2_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：diag2_def {a : F} (ha : a != 0) : diag2 a ha = diag2n zero_ne_one a ha
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diag2_def {a : F} (ha : a ≠ 0) : diag2 a ha = diag2n zero_ne_one a ha := rfl
/-
**Matrix.SpecialLinearGroup.diag2_coe** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：diag2_coe (a : F) (ha : a != 0) : (diag2 a ha).1 = diagonal (fun i => matc
h i with | 0 => a|1 => a⁻¹)
参数：a : F；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma diag2_coe (a : F) (ha : a ≠ 0) :
    (diag2 a ha).1 = diagonal (fun i ↦ match i with | 0 => a|1 => a⁻¹) := by simp [diag2n_coe]
/-
**Matrix.SpecialLinearGroup.diag2_coe'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Special
LinearGroup`。
形式化陈述：diag2_coe' {a : F} (ha : a != 0) : (diag2 a ha).1 = !![a, 0; 0, a⁻¹]
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma diag2_coe' {a : F} (ha : a ≠ 0) :
    (diag2 a ha).1 = !![a, 0; 0, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2n_coe]
/-
**Matrix.SpecialLinearGroup.diag2_smul_single_i** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diag2_smul_single_i₁ {a : F} (ha : a ≠ 0) :
    diag2 a ha • (Pi.single 0 1 : Fin 2 → F) = a • Pi.single 0 (1 : F) := by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]
/-
**Matrix.SpecialLinearGroup.diag2_smul_single_i** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.SpecialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diag2_smul_single_i₂ {a : F} (ha : a ≠ 0) :
    diag2 a ha • (Pi.single 1 1 : Fin 2 → F) = a⁻¹ • Pi.single 1 (1 : F) := by
  ext k; fin_cases k <;> simp [Matrix.SpecialLinearGroup.smul_def, diag2_coe]
/-
**Matrix.SpecialLinearGroup.diag2_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spec
ialLinearGroup`。
形式化陈述：diag2_mul_inv (a : F) (ha : a != 0) : diag2 a ha * diag2 a⁻¹ (inv_ne_zero 
ha) = 1
参数：a : F；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Matrix.SpecialLinearGroup.diag2_coe`：diag2_coe (a : F) (ha : a != 0) : (
diag2 a ha).1 = diagonal (fun i => match i with | 0 => a|1 => a⁻¹)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma diag2_mul_inv (a : F) (ha : a ≠ 0) :
    diag2 a ha * diag2 a⁻¹ (inv_ne_zero ha) = 1 := Subtype.ext <| by
  simp [diag2_coe, funext_iff, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]
/-
**Matrix.SpecialLinearGroup.diag2_inv** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：diag2_inv (a : F) (ha : a != 0) : (diag2 a ha)⁻¹ = diag2 a⁻¹ (inv_ne_zero 
ha)
参数：a : F；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `Matrix.SpecialLinearGroup.diag2_mul_inv`：diag2_mul_inv (a : F) (ha : a !
= 0) : diag2 a ha * diag2 a⁻¹ (inv_ne_zero ha) = 1
-/
lemma diag2_inv (a : F) (ha : a ≠ 0) :
    (diag2 a ha)⁻¹ = diag2 a⁻¹ (inv_ne_zero ha) := by
  apply inv_eq_of_mul_eq_one_right
  exact diag2_mul_inv a ha

section induction

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- the coercion to `Matrix ι ι R` as a monoid homomorphism -/
/-
**Matrix.SpecialLinearGroup.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：coeMonoidHom : SpecialLinearGroup ι R ->* Matrix ι ι R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the coercion to `Matrix ι ι R` as a monoid homomorphism
-/
def coeMonoidHom : SpecialLinearGroup ι R →* Matrix ι ι R where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**Matrix.SpecialLinearGroup.coeMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
.SpecialLinearGroup`。
形式化陈述：coeMonoidHom_apply (g : SpecialLinearGroup ι R) : coeMonoidHom g = (g : Ma
trix ι ι R)
参数：g : SpecialLinearGroup ι R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeMonoidHom_apply (g : SpecialLinearGroup ι R) : coeMonoidHom g = (g : Matrix ι ι R) := rfl
/-
**Matrix.SpecialLinearGroup.coeMonoidHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.SpecialLinearGroup`。
形式化陈述：coeMonoidHom_injective : Function.Injective (coeMonoidHom : SpecialLinearG
roup ι R -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma coeMonoidHom_injective : Function.Injective (coeMonoidHom : SpecialLinearGroup ι R → _) :=
  Subtype.val_injective
/-
**Matrix.SpecialLinearGroup.diag_decompose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Spe
cialLinearGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma diag_decompose (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    Finset.prod {i | i ≠ i₀} (fun i k ↦ if k = i then D i else
      if k = i₀ then (D i)⁻¹ else 1 : ι → ι → F) = D := by
  rw [det_diagonal, show Finset.univ = insert i₀ ({i | i ≠ i₀} : Finset ι) by grind,
    Finset.prod_insert (by grind), mul_eq_one_iff_eq_inv₀ (by grind),
    ← Finset.prod_inv_distrib] at hD
  ext x
  by_cases hx : x = i₀
  · simpa [hx, hD, -Finset.prod_inv_distrib] using Finset.prod_congr rfl (by grind)
  · simp [hx]
/-
**Matrix.SpecialLinearGroup.diagonal_neZero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Sp
ecialLinearGroup`。
形式化陈述：diagonal_neZero (D : ι -> F) (hD : det (diagonal D) = 1) (j : ι) : D j != 
0
参数：D : ι -> F；hD : det (diagonal D) = 1；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
-/
lemma diagonal_neZero (D : ι → F) (hD : det (diagonal D) = 1) (j : ι) :
    D j ≠ 0 := fun h ↦ by
  rw [det_diagonal, show Finset.univ = insert j ({i | i ≠ j} : Finset ι) by grind,
    Finset.prod_insert (by grind), h, zero_mul] at hD
  exact zero_ne_one hD

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.SpecialLinearGroup.diag_commute** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Speci
alLinearGroup`。
形式化陈述：diag_commute (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1) : (({i | i 
!= i₀} : Finset ι) : Set ι).Pairwise (Function.onFun Commute fun i => if hi : i 
!= i₀ then diag2n hi (D i) (diagonal_neZero D hD i) else 1)
参数：i₀ : ι；D : ι -> F；hD : det (diagonal D) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用引理 `Matrix.SpecialLinearGroup.diagonal_neZero`：diagonal_neZero (D : ι -> F) 
(hD : det (diagonal D) = 1) (j : ι) : D j != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] [h : Decidable
 p] (x : ¬p → α) (y : ¬¬p → α),   dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `dite_mul`：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) * c = if h : P then a h * c else b h * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diag_commute (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    (({i | i ≠ i₀} : Finset ι) : Set ι).Pairwise (Function.onFun Commute fun i ↦
      if hi : i ≠ i₀ then diag2n hi (D i) (diagonal_neZero D hD i) else 1) := by
  intro i1 hi1 i2 hi2 hi12
  ext i j
  simp [apply_dite, diag2n_coe]
  split_ifs <;> simp [diagonal_apply]; grind

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.SpecialLinearGroup.diag_eq_diag2n_prod** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.SpecialLinearGroup`。
形式化陈述：diag_eq_diag2n_prod (i₀ : ι) (D : ι -> F) (hD : det (diagonal D) = 1) : (⟨
diagonal D, hD⟩ : SpecialLinearGroup ι F) = Finset.noncommProd {i : ι | i != i₀}
 (fun i => if hi : i != i₀ then diag2n hi (D i) (diagonal_neZero D hD i) else 1)
 (diag_commute i₀ D hD)
参数：i₀ : ι；D : ι -> F；hD : det (diagonal D) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.SpecialLinearGroup.coeMonoidHom_injective`：coeMonoidHom_injective
 : Function.Injective (coeMonoidHom : SpecialLinearGroup ι R -> _)
· 使用引理 `Matrix.SpecialLinearGroup.diagonal_neZero`：diagonal_neZero (D : ι -> F) 
(hD : det (diagonal D) = 1) (j : ι) : D j != 0
· 使用引理 `Matrix.SpecialLinearGroup.diag_commute`：diag_commute (i₀ : ι) (D : ι -> 
F) (hD : det (diagonal D) = 1) : (({i | i != i₀} : Finset ι) : Set ι).Pairwise (
Function.onFun Commute fun i…
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Set.Pairwise.of_refl`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [S
td.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_noncommProd`：map_noncommProd [MonoidHomClass F β γ] (s : Fins
et α) (f : α -> β) (comm) (g : F) : g (s.noncommProd f comm) = s.noncommProd (fu
n i => g (f …
· 使用定理 `Finset.noncommProd_congr`：noncommProd_congr {s₁ s₂ : Finset α} {f g : α 
-> β} (h₁ : s₁ = s₂) (h₂ : forall x in s₂, f x = g x) (comm) : noncommProd s₁ f 
comm = noncomm…
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.noncommProd_eq_prod`：noncommProd_eq_prod {β : Type*} [CommMonoid 
β] (s : Finset α) (f : α -> β) : (noncommProd s f fun _ _ _ _ _ => Commute.all _
 _) = s.prod f
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup.0.Matrix.Specia
lLinearGroup.diag_decompose`：∀ {F : Type u_1} [inst : Field F] {ι : Type u_2} [i
nst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i₀ : ι) (D : ι → F),   (Matrix.diag
onal D).d…
-/
lemma diag_eq_diag2n_prod (i₀ : ι) (D : ι → F) (hD : det (diagonal D) = 1) :
    (⟨diagonal D, hD⟩ : SpecialLinearGroup ι F) =
      Finset.noncommProd {i : ι | i ≠ i₀} (fun i ↦ if hi : i ≠ i₀ then
      diag2n hi (D i) (diagonal_neZero D hD i) else 1) (diag_commute i₀ D hD) := by
  set g : ι → ι → F := fun i k ↦ if k = i then D i else if k = i₀ then (D i)⁻¹ else 1 with hg_def
  apply coeMonoidHom_injective
  rw [Finset.map_noncommProd]
  simp_rw [coeMonoidHom_apply, apply_dite, coe_one]
  rw [Finset.noncommProd_congr (s₂ := {i | i ≠ i₀}) rfl (fun i hi ↦
      (dif_pos (Finset.mem_filter.1 hi).2 : _ = (diag2n (Finset.mem_filter.1 hi).2 _ _).1))]
  convert_to! _ = Finset.noncommProd {i | i ≠ i₀} (fun x ↦ diagonal (g x)) _
  simp_rw [← diagonalRingHom_apply]
  rw [← Finset.map_noncommProd _ _ (fun _ _ _ _ _ ↦ Commute.all _ _), Finset.noncommProd_eq_prod]
  rw [diag_decompose i₀ D hD]

set_option backward.isDefEq.respectTransparency.types false in
/-- The `SpecialLinearGroup` analogue of
  `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`:
  every element of `SL(ι, F)` is a product of transvections,
  a diagonal matrix of determinant `1`, and transvections. -/
/-
**Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec*
* 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：exists_list_transvec_mul_diagonal_mul_list_transvec (M : SpecialLinearGrou
p ι F) : exists (L L' : List (TransvectionStruct ι F)) (D : ι -> F) (hD : det (d
iagonal D) = 1), M = (L.map TransvectionStruct.toSpecialLinearGroup).prod * ⟨dia
gonal D, hD⟩ * (L'.map TransvectionStruct.toSpecialLinearGroup).prod
参数：M : SpecialLinearGroup ι F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`：exists
_list_transvec_mul_diagonal_mul_list_transvec (M : Matrix n n 𝕜) : exists (L L' 
: List (TransvectionStruct n 𝕜)) (D : n -> 𝕜), M = (L.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.TransvectionStruct.det_toMatrix_prod`：det_toMatrix_prod [Fintype 
n] (L : List (TransvectionStruct n R)) : det (L.map toMatrix).prod = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `SpecialLinearGroup` analogue of
  `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`:
  every element of `SL(ι, F)` is a product of transvections,
  a diagonal matrix of determinant `1`, and transvections.
-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec (M : SpecialLinearGroup ι F) :
    ∃ (L L' : List (TransvectionStruct ι F)) (D : ι → F) (hD : det (diagonal D) = 1),
      M = (L.map TransvectionStruct.toSpecialLinearGroup).prod * ⟨diagonal D, hD⟩ *
        (L'.map TransvectionStruct.toSpecialLinearGroup).prod := by
  obtain ⟨L, L', D, hM⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.1
  refine ⟨L, L', D, by simpa [hM] using M.2, Subtype.ext <| ?_⟩
  simp_rw [coe_mul, ← coeMonoidHom_apply, map_list_prod, List.map_map, Function.comp_def,
    coeMonoidHom_apply, TransvectionStruct.toSpecialLinearGroup_coe, hM]
/-
**Matrix.SpecialLinearGroup.diagonal_transvection_induction'** 是 Mathlib 中的一个定理，
位于命名空间 `Matrix.SpecialLinearGroup`。
形式化陈述：diagonal_transvection_induction' [Nontrivial ι] (P : SpecialLinearGroup ι 
F -> Prop) (M : SpecialLinearGroup ι F) (hdiag : forall (i j : ι) (hij : i != j)
 {c : F} (hc : c != 0), P (diag2n hij c hc)) (htransvec : forall (i j : ι) (hij 
: i != j) (a : F), P (transvection hij a)) (hmul : forall A B, P A -> P B -> P (
A * B)) : P M
参数：P : SpecialLinearGroup ι F -> Prop；M : SpecialLinearGroup ι F；hdiag : forall 
(i j : ι) (hij : i != j) {c : F} (hc : c != 0), P (diag2n hij c hc)；htransvec : 
forall (i j : ι) (hij : i != j) (a : F), P (transvection hij a)；hmul : forall A 
B, P A -> P B -> P (A * B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用引理 `Matrix.SpecialLinearGroup.transvection_coeff_zero`：transvection_coeff_ze
ro {i j : ι} (hij : i != j) : transvection hij (0 : F) = 1
· 使用引理 `Matrix.SpecialLinearGroup.diagonal_neZero`：diagonal_neZero (D : ι -> F) 
(hD : det (diagonal D) = 1) (j : ι) : D j != 0
· 使用引理 `Matrix.SpecialLinearGroup.diag_commute`：diag_commute (i₀ : ι) (D : ι -> 
F) (hD : det (diagonal D) = 1) : (({i | i != i₀} : Finset ι) : Set ι).Pairwise (
Function.onFun Commute fun i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.SpecialLinearGroup.diag_eq_diag2n_prod`：diag_eq_diag2n_prod (i₀ :
 ι) (D : ι -> F) (hD : det (diagonal D) = 1) : (⟨diagonal D, hD⟩ : SpecialLinear
Group ι F) = Finset.noncommProd {i …
· 使用引理 `Finset.noncommProd_induction`：noncommProd_induction (s : Finset α) (f : 
α -> β) (comm) (p : β -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit
 : p 1) (base : fo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Matrix.TransvectionStruct.hij`：∀ {n : Type u_1} {R : Type u₂} (self : Ma
trix.TransvectionStruct n R), self.i ≠ self.j
· 使用引理 `Matrix.TransvectionStruct.toSpecialLinearGroup_def`：toSpecialLinearGroup
_def (t : TransvectionStruct ι F) : t.toSpecialLinearGroup = SpecialLinearGroup.
transvection t.hij t.c
· 使用定理 `Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_tra
nsvec`：exists_list_transvec_mul_diagonal_mul_list_transvec (M : SpecialLinearGro
up ι F) : exists (L L' : List (TransvectionStruct ι F)) (D : ι -> F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem diagonal_transvection_induction' [Nontrivial ι] (P : SpecialLinearGroup ι F → Prop)
    (M : SpecialLinearGroup ι F)
    (hdiag : ∀ (i j : ι) (hij : i ≠ j) {c : F} (hc : c ≠ 0), P (diag2n hij c hc))
    (htransvec : ∀ (i j : ι) (hij : i ≠ j) (a : F), P (transvection hij a))
    (hmul : ∀ A B, P A → P B → P (A * B)) : P M := by
  obtain ⟨i₀, j₀, hij₀⟩ := exists_pair_ne ι
  have hP1 : P 1 := transvection_coeff_zero (F := F) hij₀ ▸ htransvec i₀ j₀ hij₀ 0
  have hdiagonal (D : ι → F) (hD : det (diagonal D) = 1) : P ⟨diagonal D, hD⟩ := by
    rw [diag_eq_diag2n_prod i₀ D hD]
    refine Finset.noncommProd_induction _ _ _ P hmul hP1 fun i hi => ?_
    simp [(Finset.mem_filter.1 hi).2, hdiag]
  have hlist (L : List (TransvectionStruct ι F)) :
      P (L.map TransvectionStruct.toSpecialLinearGroup).prod := by
    induction L with
    | nil => simpa using hP1
    | cons t L ih =>
      rw [List.map_cons, List.prod_cons, t.toSpecialLinearGroup_def]
      exact hmul _ _ (htransvec t.i t.j t.hij t.c) ih
  obtain ⟨L, L', D, hD, hM⟩ := exists_list_transvec_mul_diagonal_mul_list_transvec M
  exact hM ▸ hmul _ _ (hmul _ _ (hlist L) (hdiagonal D hD)) (hlist L')

end induction

end SpecialLinearGroup

open Matrix.SpecialLinearGroup
open scoped commutatorElement

/-
**Matrix.commutator_diag2_transvection** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：commutator_diag2_transvection (a : F) (ha : a != 0) (b c : F) (hc : c = b 
* (a ^ 2 - 1)) : ⁅diag2 a ha, SpecialLinearGroup.transvection zero_ne_one b⁆ = (
SpecialLinearGroup.transvection zero_ne_one c : SL(2, F))
参数：a : F；ha : a != 0；b c : F；hc : c = b * (a ^ 2 - 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `Matrix.SpecialLinearGroup.diag2_inv`：diag2_inv (a : F) (ha : a != 0) : (
diag2 a ha)⁻¹ = diag2 a⁻¹ (inv_ne_zero ha)
· 使用引理 `Matrix.SpecialLinearGroup.transvection_inv`：transvection_inv {i j : ι} (
hij : i != j) (b : F) : (transvection hij b)⁻¹ = transvection hij (-b)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.SpecialLinearGroup.diag2_coe`：diag2_coe (a : F) (ha : a != 0) : (
diag2 a ha).1 = diagonal (fun i => match i with | 0 => a|1 => a⁻¹)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
（共 55 条，此处仅展示前 30 条）
-/
lemma commutator_diag2_transvection (a : F) (ha : a ≠ 0) (b c : F)
    (hc : c = b * (a ^ 2 - 1)) : ⁅diag2 a ha, SpecialLinearGroup.transvection zero_ne_one b⁆ =
    (SpecialLinearGroup.transvection zero_ne_one c : SL(2, F)) := by
  rw [commutatorElement_def, diag2_inv a ha, SpecialLinearGroup.transvection_inv zero_ne_one b]
  refine Subtype.ext <| Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j
  <;> simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, mul_add, add_mul,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, mul_comm a b, mul_assoc b a a, ← pow_two,
    mul_sub_one, ← sub_eq_add_neg]

/-- For any `c : F`, given `a ≠ 0` and `a² ≠ 1`, the transvection `transvection i₁ i₂ hij c` is
a commutator in `SL ι F`, hence lies in `commutator (SL ι F)`. -/
/-
**Matrix.transvection_mem_commutator** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transvection_mem_commutator {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j
 : Fin 2} (h : i != j) (c : F) : SpecialLinearGroup.transvection h c in commutat
or SL(2, F)
参数：ha : a != 0；hasq : a ^ 2 != 1；h : i != j；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.transvection_mem_commutator₀`：transvection_mem_commutator₀ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection ze
ro_ne_one c in commutator…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Matrix.transvection_mem_commutator₁`：transvection_mem_commutator₁ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection on
e_ne_zero c in commutator…

--- 原说明 ---
For any `c : F`, given `a ≠ 0` and `a² ≠ 1`, the transvection `transvection i₁ i
₂ hij c` is
a commutator in `SL ι F`, hence lies in `commutator (SL ι F)`.
-/
lemma transvection_mem_commutator₀ {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) (c : F) :
    SpecialLinearGroup.transvection zero_ne_one c ∈ commutator SL(2, F) := by
  rw [← commutator_diag2_transvection a ha (c / (a ^ 2 - 1)) c
    (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
/-
**Matrix.transvection_mem_commutator** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transvection_mem_commutator {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j
 : Fin 2} (h : i != j) (c : F) : SpecialLinearGroup.transvection h c in commutat
or SL(2, F)
参数：ha : a != 0；hasq : a ^ 2 != 1；h : i != j；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.transvection_mem_commutator₀`：transvection_mem_commutator₀ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection ze
ro_ne_one c in commutator…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Matrix.transvection_mem_commutator₁`：transvection_mem_commutator₁ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection on
e_ne_zero c in commutator…
-/
lemma transvection_mem_commutator₁ {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) (c : F) :
    SpecialLinearGroup.transvection one_ne_zero c ∈ commutator SL(2, F) := by
  have (b c' : F) (hc : c' = b * (a ^ 2 - 1)) :
      ⁅diag2 a⁻¹ (inv_ne_zero ha), SpecialLinearGroup.transvection one_ne_zero b⁆ =
      (SpecialLinearGroup.transvection one_ne_zero c' : SL(2, F)) := by
    rw [commutatorElement_def, diag2_inv a⁻¹ (inv_ne_zero ha),
      SpecialLinearGroup.transvection_inv one_ne_zero b]
    refine Subtype.ext <| Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
    simp [hc, SpecialLinearGroup.transvection_coe, diag2_coe, inv_inv, mul_add, add_mul,
      mul_inv_cancel₀ ha, inv_mul_cancel₀ ha, mul_comm a b, mul_assoc b a a, ← pow_two,
      mul_sub_one, ← sub_eq_add_neg]
  rw [← this (c / (a ^ 2 - 1)) c (div_mul_cancel₀ c (sub_ne_zero_of_ne hasq)).symm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
/-
**Matrix.transvection_mem_commutator** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transvection_mem_commutator {a : F} (ha : a != 0) (hasq : a ^ 2 != 1) {i j
 : Fin 2} (h : i != j) (c : F) : SpecialLinearGroup.transvection h c in commutat
or SL(2, F)
参数：ha : a != 0；hasq : a ^ 2 != 1；h : i != j；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.transvection_mem_commutator₀`：transvection_mem_commutator₀ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection ze
ro_ne_one c in commutator…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Matrix.transvection_mem_commutator₁`：transvection_mem_commutator₁ {a : F
} (ha : a != 0) (hasq : a ^ 2 != 1) (c : F) : SpecialLinearGroup.transvection on
e_ne_zero c in commutator…
-/
lemma transvection_mem_commutator {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) {i j : Fin 2} (h : i ≠ j)
    (c : F) : SpecialLinearGroup.transvection h c ∈ commutator SL(2, F) := by
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₀ ha hasq c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact transvection_mem_commutator₁ ha hasq c
/-
**Matrix.diag2_decompose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：diag2_decompose (a : F) (ha : a != 0) : diag2 a ha = SpecialLinearGroup.tr
ansvection zero_ne_one a * SpecialLinearGroup.transvection one_ne_zero (- a⁻¹) *
 SpecialLinearGroup.transvection zero_ne_one a * SpecialLinearGroup.transvection
 zero_ne_one (-1) * SpecialLinearGroup.transvection one_ne_zero 1 * SpecialLinea
rGroup.transvection zero_ne_one (-1)
参数：a : F；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Matrix.SpecialLinearGroup.diag2_coe'`：diag2_coe' {a : F} (ha : a != 0) :
 (diag2 a ha).1 = !![a, 0; 0, a⁻¹]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.single_mul_single_same`：single_mul_single_same (i : l) (j : m) (k
 : n) (d : α) : single i j c * single j k d = single i k (c * d)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Matrix.single_mul_single_of_ne`：single_mul_single_of_ne (i : l) (j k : m
) {l : n} (h : j != k) (d : α) : single i j c * single k l d = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 46 条，此处仅展示前 30 条）
-/
lemma diag2_decompose (a : F) (ha : a ≠ 0) :
    diag2 a ha = SpecialLinearGroup.transvection zero_ne_one a *
      SpecialLinearGroup.transvection one_ne_zero (- a⁻¹) *
      SpecialLinearGroup.transvection zero_ne_one a *
      SpecialLinearGroup.transvection zero_ne_one (-1) *
      SpecialLinearGroup.transvection one_ne_zero 1 *
      SpecialLinearGroup.transvection zero_ne_one (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [diag2_coe', transvection_coe, mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]
/-
**Matrix.SL2.transvection_induction** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SL2`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] (P : Matrix.SpecialLinearGroup (Fin 2) F
 → Prop),   (∀ (i j : Fin 2) (h : i ≠ j) (c : F), P (Matrix.SpecialLinearGroup.t
ransvection h c)) →     (∀ (A B : Matrix.SpecialLinearGroup (Fin 2) F), P A → P 
B → P (A * B)) →       ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F), P A
参数：P : Matrix.SpecialLinearGroup (Fin 2) F → Prop；∀ (i j : Fin 2) (h : i ≠ j) (c
 : F), P (Matrix.SpecialLinearGroup.transvection h c)；∀ (A B : Matrix.SpecialLin
earGroup (Fin 2) F), P A → P B → P (A * B)；A : Matrix.SpecialLinearGroup (Fin 2)
 F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.diagonal_transvection_induction'`：diagonal_tra
nsvection_induction' [Nontrivial ι] (P : SpecialLinearGroup ι F -> Prop) (M : Sp
ecialLinearGroup ι F) (hdiag : forall (i j : ι) …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.diag2_decompose`：diag2_decompose (a : F) (ha : a != 0) : diag2 a 
ha = SpecialLinearGroup.transvection zero_ne_one a * SpecialLinearGroup.transvec
tion one_ne_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem SL2.transvection_induction (P : SL(2, F) → Prop)
    (htransvec : ∀ (i j : Fin 2) (h : i ≠ j) c, P (SpecialLinearGroup.transvection h c))
    (hmul : ∀ A B, P A → P B → P (A * B)) (A : SL(2, F)) : P A := by
  refine diagonal_transvection_induction' P _ (fun i j hij c hc ↦ ?_) htransvec hmul
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    change P (diag2 c hc)
    rw [diag2_decompose c hc]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_goals exact htransvec _ _ _ _
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    rw [show diag2n hij c hc = diag2 c⁻¹ (inv_ne_zero hc) by
      ext; simp [diag2n_coe, diagonal_apply]; grind, diag2_decompose c⁻¹ (inv_ne_zero hc)]
    refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
    all_goals exact htransvec _ _ _ _
/-
**Matrix.SL2.commutator_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.SL2`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {a : F}, a ≠ 0 → a ^ 2 ≠ 1 → commutator 
(Matrix.SpecialLinearGroup (Fin 2) F) = ⊤
参数：Matrix.SpecialLinearGroup (Fin 2) F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Matrix.SL2.transvection_induction`：∀ {F : Type u_1} [inst : Field F] (P 
: Matrix.SpecialLinearGroup (Fin 2) F → Prop),   (∀ (i j : Fin 2) (h : i ≠ j) (c
 : F), P (Matrix.Specia…
· 使用引理 `Matrix.transvection_mem_commutator`：transvection_mem_commutator {a : F} 
(ha : a != 0) (hasq : a ^ 2 != 1) {i j : Fin 2} (h : i != j) (c : F) : SpecialLi
nearGroup.transvection h…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma SL2.commutator_eq_top {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    commutator SL(2, F) = ⊤ :=
  le_antisymm le_top (fun A _ ↦ SL2.transvection_induction _
    (fun _ _ ↦ transvection_mem_commutator ha hasq) (fun _ _ ↦ mul_mem) A)

end SL2

end Matrix

namespace ModularGroup

open MatrixGroups

open Matrix Matrix.SpecialLinearGroup

/-- The matrix `S = [[0, -1], [1, 0]]` as an element of `SL(2, ℤ)`.

This element acts naturally on the Euclidean plane as a rotation about the origin by `π / 2`.

This element also acts naturally on the hyperbolic plane as rotation about `i` by `π`. It
represents the Mobiüs transformation `z ↦ -1/z` and is an involutive elliptic isometry. -/
/-
**ModularGroup.S** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：S : SL(2, Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix `S = [[0, -1], [1, 0]]` as an element of `SL(2, ℤ)`.

This element acts naturally on the Euclidean plane as a rotation about the origi
n by `π / 2`.

This element also acts naturally on the hyperbolic plane as rotation about `i` b
y `π`. It
represents the Mobiüs transformation `z ↦ -1/z` and is an involutive elliptic is
ometry.
-/
def S : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The matrix `T = [[1, 1], [0, 1]]` as an element of `SL(2, ℤ)`. -/
/-
**ModularGroup.T** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：T : SL(2, Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix `T = [[1, 1], [0, 1]]` as an element of `SL(2, ℤ)`.
-/
def T : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
/-
**ModularGroup.coe_S** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_S : ↑S = !![0, -1; 1, 0]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_S : ↑S = !![0, -1; 1, 0] :=
  rfl
/-
**ModularGroup.S_inv** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：S_inv : S⁻¹ = -S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma S_inv : S⁻¹ = -S := by decide

@[simp]
/-
**ModularGroup.coe_T** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_T : ↑T = (!![1, 1; 0, 1] : Matrix _ _ Int)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_T : ↑T = (!![1, 1; 0, 1] : Matrix _ _ ℤ) :=
  rfl
/-
**ModularGroup.coe_T_inv** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_T_inv : ↑(T⁻¹) = !![1, -1; 0, 1]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.adjugate_fin_two`：adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α)
 : adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_T_inv : ↑(T⁻¹) = !![1, -1; 0, 1] := by simp [coe_inv, coe_T, adjugate_fin_two]
/-
**ModularGroup.coe_T_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 1]
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Matrix.SpecialLinearGroup.coe_one`：coe_one : (1 : SpecialLinearGroup n R
) = (1 : Matrix n n R)
· 使用定理 `Matrix.one_fin_two`：one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1,
 0; 0, 1]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Matrix.mul_fin_two`：mul_fin_two [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a
₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) : !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] = !![a
₁₁ * b₁₁…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `ModularGroup.coe_T_inv`：coe_T_inv : ↑(T⁻¹) = !![1, -1; 0, 1]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 45 条，此处仅展示前 30 条）
-/
theorem coe_T_zpow (n : ℤ) : (T ^ n).1 = !![1, n; 0, 1] := by
  induction n with
  | zero => rw [zpow_zero, coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one, mul_one, add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    congrm !![?_, ?_; _, _] <;> ring

@[simp]
/-
**ModularGroup.T_pow_mul_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：T_pow_mul_apply_one (n : Int) (g : SL(2, Int)) : (T ^ n * g) 1 = g 1
参数：n : Int；g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem T_pow_mul_apply_one (n : ℤ) (g : SL(2, ℤ)) : (T ^ n * g) 1 = g 1 := by
  ext j
  simp [coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp]
/-
**ModularGroup.T_mul_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：T_mul_apply_one (g : SL(2, Int)) : (T * g) 1 = g 1
参数：g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ModularGroup.T_pow_mul_apply_one`：T_pow_mul_apply_one (n : Int) (g : SL(
2, Int)) : (T ^ n * g) 1 = g 1
-/
theorem T_mul_apply_one (g : SL(2, ℤ)) : (T * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one 1 g

@[simp]
/-
**ModularGroup.T_inv_mul_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：T_inv_mul_apply_one (g : SL(2, Int)) : (T⁻¹ * g) 1 = g 1
参数：g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.adjugate_fin_two_of`：adjugate_fin_two_of (a b c d : α) : adjugate
 !![a, b; c, d] = !![d, -b; -c, a]
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `ModularGroup.T_pow_mul_apply_one`：T_pow_mul_apply_one (n : Int) (g : SL(
2, Int)) : (T ^ n * g) 1 = g 1
-/
theorem T_inv_mul_apply_one (g : SL(2, ℤ)) : (T⁻¹ * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one (-1) g
/-
**ModularGroup.S_mul_S_eq** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：S_mul_S_eq : (S : Matrix (Fin 2) (Fin 2) Int) * S = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.vecMul_cons`：vecMul_cons (v : Fin n.succ -> α) (w : o' -> α) (B :
 Fin n -> o' -> α) : v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.neg_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Neg α] (x : α) (v : Fi
n n → α), -Matrix.vecCons x v = Matrix.vecCons (-x) (-v)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Matrix.neg_empty`：∀ {α : Type u_1} [inst : Neg α] (v : Fin 0 → α), -v = 
![]
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.eta_fin_two`：eta_fin_two (A : Matrix (Fin 2) (Fin 2) α) : A = !![
A 0 0, A 0 1; A 1 0, A 1 1]
-/
lemma S_mul_S_eq : (S : Matrix (Fin 2) (Fin 2) ℤ) * S = -1 := by
  simp only [S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))
/-
**ModularGroup.T_S_rel** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：T_S_rel : S • S • S • T • S • T • S = T⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma T_S_rel : S • S • S • T • S • T • S = T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end ModularGroup

