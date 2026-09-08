/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `Matrix.det`, and its essential properties.

## Main definitions

- `Matrix.det`: the determinant of a square matrix, as a sum over permutations
- `Matrix.detRowAlternating`: the determinant, as an `AlternatingMap` in the rows of the matrix

## Main results

- `det_mul`: the determinant of `A * B` is the product of determinants
- `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
- `det_block_diagonal`: the determinant of a block diagonal matrix is a product
  of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`MathlibTest/matrix.lean` for some examples.

-/

@[expose] public section


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- `det` is an `AlternatingMap` in the rows of the matrix. -/
/-
**Matrix.detRowAlternating** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detRowAlternating : (n -> R) [⋀^n]->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`det` is an `AlternatingMap` in the rows of the matrix.
-/
def detRowAlternating : (n → R) [⋀^n]→ₗ[R] R :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)

/-- The determinant of a matrix given by the Leibniz formula. -/
@[wikidata Q178546]
/-
**Matrix.det** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：det (M : Matrix n n R) : R
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a matrix given by the Leibniz formula.
-/
def det (M : Matrix n n R) : R :=
  detRowAlternating M
/-
**Matrix.det_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏
 i, M (σ i) i
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.alternatization_apply`：alternatization_apply (m : Multili
nearMap R (fun _ : ι => M) N') (v : ι -> M) : alternatization m v = ∑ σ : Perm ι
, Equiv.Perm.sign σ • m.do…
-/
theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below
/-
**Matrix.det_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
  simp [det_apply, Units.smul_def]
/-
**Matrix.det_eq_detp_sub_detp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_detp_sub_detp (M : Matrix n n R) : M.det = M.detp 1 - M.detp (-1)
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用引理 `Equiv.Perm.ofSign_disjoint`：ofSign_disjoint : _root_.Disjoint (ofSign 1 
: Finset (Perm α)) (ofSign (-1))
· 使用引理 `Equiv.Perm.ofSign_disjUnion`：ofSign_disjUnion : (ofSign 1).disjUnion (of
Sign (-1)) ofSign_disjoint = (univ : Finset (Perm α))
· 使用定理 `Finset.sum_disjUnion`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} (h : Disjoint s₁ s₂),   ∑ x ∈ s₁.disjUnion
 s₂ h, f x…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Equiv.Perm.mem_ofSign`：mem_ofSign {s : Intˣ} {σ : Perm α} : σ in ofSign 
s ↔ σ.sign = s
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
-/
theorem det_eq_detp_sub_detp (M : Matrix n n R) : M.det = M.detp 1 - M.detp (-1) := by
  rw [det_apply, ← Equiv.sum_comp (Equiv.inv (Perm n)), ← ofSign_disjUnion, sum_disjUnion]
  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ ↦ ?_) (sum_congr rfl fun σ hσ ↦ ?_) <;>
    rw [mem_ofSign.mp hσ, ← Equiv.prod_comp σ] <;> simp

@[simp]
/-
**Matrix.det_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i, d i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i := by
  rw [det_apply']
  refine (Finset.sum_eq_single 1 ?_ ?_).trans ?_
  · rintro σ - h2
    obtain ⟨x, h3⟩ := not_forall.1 (mt Equiv.ext h2)
    convert! mul_zero (ε σ)
    apply Finset.prod_eq_zero (mem_univ x)
    exact if_neg h3
  · simp
  · simp
/-
**Matrix.det_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintype n] {R : Type v} 
[inst_2 : CommRing R] [Nonempty n],   Matrix.det 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
-/
@[simp] theorem det_zero [Nonempty n] : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_zero

@[simp]
/-
**Matrix.det_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_one : det (1 : Matrix n n R) = 1
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
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one]; simp [-diagonal_one]
/-
**Matrix.det_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by simp [det_apply]

@[simp]
/-
**Matrix.coe_det_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_det_isEmpty [IsEmpty n] : (det : Matrix n n R -> R) = Function.const _
 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
-/
theorem coe_det_isEmpty [IsEmpty n] : (det : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact det_isEmpty
/-
**Matrix.det_eq_one_of_card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : d
et A = 1
参数：h : Fintype.card n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
-/
theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 :=
  haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  det_isEmpty

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
/-
**Matrix.det_unique** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix 
n n R) : det A = A default default
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
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
· 使用定理 `Equiv.Perm.sign_one`：sign_one : sign (1 : Perm α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `n` has only one element, the determinant of an `n` by `n` matrix is just tha
t element.
Although `Unique` implies `DecidableEq` and `Fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly.
-/
theorem det_unique {n : Type*} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    det A = A default default := by simp [det_apply, univ_unique]
/-
**Matrix.det_eq_elem_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) : 
det A = A k k
参数：A : Matrix n n R；k : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
-/
theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) :
    det A = A k k := by
  have := uniqueOfSubsingleton k
  convert! det_unique A
/-
**Matrix.det_eq_elem_of_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k 
: n) : det A = A k k
参数：h : Fintype.card n = 1；k : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_eq_elem_of_subsingleton`：det_eq_elem_of_subsingleton [Subsing
leton n] (A : Matrix n n R) (k : n) : det A = A k k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton : car
d α <= 1 ↔ Subsingleton α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    det A = A k k :=
  haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _
/-
**Matrix.det_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_aux {M N : Matrix n n R} {p : n -> n} (H : ¬Bijective p) : (∑ σ : 
Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0
参数：H : ¬Bijective p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), Fu
nction.Injective f = ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_bijective`：injective_iff_bijective {f : α -> α} : I
njective f ↔ Bijective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.sum_involution`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M} (g : (a : ι) → a ∈ s → ι),   (∀ (a : ι) (ha :
 a ∈ s), f …
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.swap_apply_self`：swap_apply_self (i j a : α) : swap i j (swap i j 
a) = a
· 使用定理 `Equiv.apply_swap_eq_self`：apply_swap_eq_self {v : α -> β} {i j : α} (hv 
: v i = v j) (k : α) : v (swap i j k) = v k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `Equiv.Perm.sign_swap`：sign_swap {x y : α} (h : x != y) : sign (swap x y)
 = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.mul_swap_eq_iff`：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α}
 {σ : Equiv.Perm α}, σ * Equiv.swap i j = σ ↔ i = j
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
（共 31 条，此处仅展示前 30 条）
-/
theorem det_mul_aux {M N : Matrix n n R} {p : n → n} (H : ¬Bijective p) :
    (∑ σ : Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [← Finite.injective_iff_bijective, Injective] at H
    push Not at H
    exact H
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij])
        simp [this, sign_swap hij, -sign_swap', prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij) (fun _ _ => mem_univ _) fun σ _ =>
      mul_swap_involutive i j σ

@[simp]
/-
**Matrix.det_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul (M N : Matrix n n R) : det (M * N) = det M * det N
参数：M N : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.prod_univ_sum`：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : fo
rall i, Finset (κ i)) (f : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in
 piFinset …
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Matrix.det_mul_aux`：det_mul_aux {M N : Matrix n n R} {p : n -> n} (H : ¬
Bijective p) : (∑ σ : Perm n, ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.coe_fn_injective`：coe_fn_injective : @Function.Injective (α ≃ β) (
α -> β) (fun e => e)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
（共 38 条，此处仅展示前 30 条）
-/
theorem det_mul (M N : Matrix n n R) : det (M * N) = det M * det N :=
  calc
    det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : n → n with Bijective p, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      refine (sum_subset (filter_subset _ _) fun f _ hbij ↦ det_mul_aux ?_).symm
      simpa only [mem_filter_univ] using hbij
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      sum_bij (fun p h ↦ Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ ↦ mem_univ _)
        (fun _ _ _ _ h ↦ by injection h)
        (fun b _ ↦ ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩) fun _ _ ↦ rfl
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      (sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp
          have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                rw [mul_comm, sign_mul (τ * σ⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε τ := by simp only [inv_mul_cancel_right]
          simp_rw [Equiv.coe_mulRight, h]
          simp only [this])
    _ = det M * det N := by
      simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The determinant of a matrix, as a monoid homomorphism. -/
/-
**Matrix.detMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：detMonoidHom : Matrix n n R ->* R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N

--- 原说明 ---
The determinant of a matrix, as a monoid homomorphism.
-/
def detMonoidHom : Matrix n n R →* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul

@[simp]
/-
**Matrix.coe_detMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：coe_detMonoidHom : (detMonoidHom : Matrix n n R -> R) = det
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_detMonoidHom : (detMonoidHom : Matrix n n R → R) = det :=
  rfl

/-- On square matrices, `mul_comm` applies under `det`. -/
/-
**Matrix.det_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_comm (M N : Matrix m m R) : det (M * N) = det (N * M)
参数：M N : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
On square matrices, `mul_comm` applies under `det`.
-/
theorem det_mul_comm (M N : Matrix m m R) : det (M * N) = det (N * M) := by
  rw [det_mul, det_mul, mul_comm]

/-- On square matrices, `mul_left_comm` applies under `det`. -/
/-
**Matrix.det_mul_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_left_comm (M N P : Matrix m m R) : det (M * (N * P)) = det (N * (M
 * P))
参数：M N P : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_mul_comm`：det_mul_comm (M N : Matrix m m R) : det (M * N) = d
et (N * M)

--- 原说明 ---
On square matrices, `mul_left_comm` applies under `det`.
-/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M * (N * P)) = det (N * (M * P)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, det_mul, det_mul_comm M N, ← det_mul]

/-- On square matrices, `mul_right_comm` applies under `det`. -/
/-
**Matrix.det_mul_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_right_comm (M N P : Matrix m m R) : det (M * N * P) = det (M * P *
 N)
参数：M N P : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_mul_comm`：det_mul_comm (M N : Matrix m m R) : det (M * N) = d
et (N * M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
On square matrices, `mul_right_comm` applies under `det`.
-/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M * N * P) = det (M * P * N) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, det_mul, det_mul_comm N P, ← det_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed
/-
**Matrix.det_units_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) : det (M.val * N *
 M⁻¹.val) = det N
参数：M : (Matrix m m R)ˣ；N : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul_right_comm`：det_mul_right_comm (M N P : Matrix m m R) : d
et (M * N * P) = det (M * P * N)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (M.val * N * M⁻¹.val) = det N := by
  rw [det_mul_right_comm, Units.mul_inv, one_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed
/-
**Matrix.det_units_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) : det (M⁻¹.val * 
N * ↑M.val) = det N
参数：M : (Matrix m m R)ˣ；N : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_units_conj`：det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix 
m m R) : det (M.val * N * M⁻¹.val) = det N
-/
theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (M⁻¹.val * N * ↑M.val) = det N :=
  det_units_conj M⁻¹ N

/-- Transposing a matrix preserves the determinant. -/
@[simp]
/-
**Matrix.det_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Transposing a matrix preserves the determinant.
-/
theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det := by
  rw [det_apply', det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp

/-- Permuting the columns changes the sign of the determinant. -/
/-
**Matrix.det_permute** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_permute (σ : Perm n) (M : Matrix n n R) : (M.submatrix σ id).det = Per
m.sign σ * M.det
参数：σ : Perm n；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlternatingMap.map_perm`：map_perm [DecidableEq ι] [Fintype ι] (v : ι -> 
M) (σ : Equiv.Perm ι) : g (v ∘ σ) = Equiv.Perm.sign σ • g v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Permuting the columns changes the sign of the determinant.
-/
theorem det_permute (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).det = Perm.sign σ * M.det :=
  ((detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def, det])

/-- Permuting the rows changes the sign of the determinant. -/
/-
**Matrix.det_permute'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_permute' (σ : Perm n) (M : Matrix n n R) : (M.submatrix id σ).det = Pe
rm.sign σ * M.det
参数：σ : Perm n；M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.det_permute`：det_permute (σ : Perm n) (M : Matrix n n R) : (M.sub
matrix σ id).det = Perm.sign σ * M.det

--- 原说明 ---
Permuting the rows changes the sign of the determinant.
-/
theorem det_permute' (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).det = Perm.sign σ * M.det := by
  rw [← det_transpose, transpose_submatrix, det_permute, det_transpose]

/-- Permuting rows and columns with the same equivalence does not change the determinant. -/
@[simp]
/-
**Matrix.det_submatrix_equiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) : det (A.submatrix
 e e) = det A
参数：e : n ≃ m；A : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `Equiv.Perm.sign_permCongr`：sign_permCongr (e : α ≃ β) (p : Perm α) : sig
n (e.permCongr p) = sign p
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.permCongr_apply`：∀ {α' : Type u_1} {β' : Type u_2} (e : α' ≃ β') (
p : Equiv.Perm α') (x : β'), (e.permCongr p) x = e (p (e.symm x))
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)

--- 原说明 ---
Permuting rows and columns with the same equivalence does not change the determi
nant.
-/
theorem det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) :
    det (A.submatrix e e) = det A := by
  rw [det_apply', det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_permCongr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, submatrix_apply]

/-- Permuting rows and columns with two equivalences does not change the absolute value of the
determinant. -/
@[simp]
/-
**Matrix.abs_det_submatrix_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：abs_det_submatrix_equiv_equiv {R : Type*} [CommRing R] [LinearOrder R] [Is
StrictOrderedRing R] (e₁ e₂ : n ≃ m) (A : Matrix m m R) : |(A.submatrix e₁ e₂).d
et| = |A.det|
参数：e₁ e₂ : n ≃ m；A : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `Matrix.det_permute'`：det_permute' (σ : Perm n) (M : Matrix n n R) : (M.s
ubmatrix id σ).det = Perm.sign σ * M.det
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `abs_unit_intCast`：abs_unit_intCast [IsOrderedRing α] (a : Intˣ) : |((a :
 Int) : α)| = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Permuting rows and columns with two equivalences does not change the absolute va
lue of the
determinant.
-/
theorem abs_det_submatrix_equiv_equiv {R : Type*}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : n ≃ m) (A : Matrix m m R) :
    |(A.submatrix e₁ e₂).det| = |A.det| := by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change |((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det| = |A.det|
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul, abs_unit_intCast, one_mul]

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`; this one is unsuitable because
`Matrix.reindex_apply` unfolds `reindex` first.
-/
/-
**Matrix.det_reindex_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = de
t A
参数：e : m ≃ n；A : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_submatrix_equiv_self`：det_submatrix_equiv_self (e : n ≃ m) (A
 : Matrix m m R) : det (A.submatrix e e) = det A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`; this one i
s unsuitable because
`Matrix.reindex_apply` unfolds `reindex` first.
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_submatrix_equiv_self e.symm A
/-
**Matrix.det_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：det_reindex (e e' : m ≃ n) (M : Matrix m m R) : (M.reindex e e').det = sig
n (e'.trans e.symm) * M.det
参数：e e' : m ≃ n；M : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `Matrix.det_permute`：det_permute (σ : Perm n) (M : Matrix n n R) : (M.sub
matrix σ id).det = Perm.sign σ * M.det
-/
lemma det_reindex (e e' : m ≃ n) (M : Matrix m m R) :
    (M.reindex e e').det = sign (e'.trans e.symm) * M.det := by
  trans ((M.reindex (e.trans e'.symm) (.refl _)).reindex e' e').det
  · congr 1; ext; simp
  · simp_rw [det_reindex_self, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, det_permute]
    rfl

/-- Reindexing both indices along equivalences preserves the absolute of the determinant.

For the `simp` version of this lemma, see `abs_det_submatrix_equiv_equiv`;
this one is unsuitable because `Matrix.reindex_apply` unfolds `reindex` first.
-/
/-
**Matrix.abs_det_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：abs_det_reindex {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (e₁ e₂ : m ≃ n) (A : Matrix m m R) : |det (reindex e₁ e₂ A)| = |det A|
参数：e₁ e₂ : m ≃ n；A : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.abs_det_submatrix_equiv_equiv`：abs_det_submatrix_equiv_equiv {R :
 Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (e₁ e₂ : n ≃ m) (A 
: Matrix m m R) : |(A.subm…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reindexing both indices along equivalences preserves the absolute of the determi
nant.

For the `simp` version of this lemma, see `abs_det_submatrix_equiv_equiv`;
this one is unsuitable because `Matrix.reindex_apply` unfolds `reindex` first.
-/
theorem abs_det_reindex {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    |det (reindex e₁ e₂ A)| = |det A| :=
  abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A
/-
**Matrix.det_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * d
et A
参数：A : Matrix n n R；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.smul_eq_diagonal_mul`：smul_eq_diagonal_mul [Fintype m] [Decidable
Eq m] (M : Matrix m n α) (a : α) : a • M = (diagonal fun _ => a) * M
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
  calc
    det (c • A) = det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp

@[simp]
/-
**Matrix.det_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_smul_of_tower {α} [Monoid α] [MulAction α R] [IsScalarTower α R R] [SM
ulCommClass α R R] (c : α) (A : Matrix n n R) : det (c • A) = c ^ Fintype.card n
 • det A
参数：c : α；A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem det_smul_of_tower {α} [Monoid α] [MulAction α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : α) (A : Matrix n n R) :
    det (c • A) = c ^ Fintype.card n • det A := by
  rw [← smul_one_smul R c A, det_smul, smul_pow, one_pow, smul_mul_assoc, one_mul]
/-
**Matrix.det_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.card n * det A
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
-/
theorem det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.card n * det A := by
  rw [← det_smul, neg_one_smul]

/-- A variant of `Matrix.det_neg` with scalar multiplication by `Units ℤ` instead of multiplication
by `R`. -/
/-
**Matrix.det_neg_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_neg_eq_smul (A : Matrix n n R) : det (-A) = (-1 : Units Int) ^ Fintype
.card n • det A
参数：A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_smul_of_tower`：det_smul_of_tower {α} [Monoid α] [MulAction α 
R] [IsScalarTower α R R] [SMulCommClass α R R] (c : α) (A : Matrix n n R) : det 
(c • A) = c ^ …
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
A variant of `Matrix.det_neg` with scalar multiplication by `Units ℤ` instead of
 multiplication
by `R`.
-/
theorem det_neg_eq_smul (A : Matrix n n R) :
    det (-A) = (-1 : Units ℤ) ^ Fintype.card n • det A := by
  rw [← det_smul_of_tower, Units.neg_smul, one_smul]

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
/-
**Matrix.det_mul_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_row (v : n -> R) (A : Matrix n n R) : det (of fun i j => v j * A i
 j) = (∏ i, v i) * det A
参数：v : n -> R；A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i

--- 原说明 ---
Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s.
-/
theorem det_mul_row (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v j * A i j) = (∏ i, v i) * det A :=
  calc
    det (of fun i j => v j * A i j) = det (A * diagonal v) :=
      congr_arg det <| by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
/-
**Matrix.det_mul_column** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mul_column (v : n -> R) (A : Matrix n n R) : det (of fun i j => v i * 
A i j) = (∏ i, v i) * det A
参数：v : n -> R；A : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m

--- 原说明 ---
Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s.
-/
theorem det_mul_column (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v i * A i j) = (∏ i, v i) * det A :=
  MultilinearMap.map_smul_univ _ v A

@[simp]
/-
**Matrix.det_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det M ^ n
参数：M : Matrix m m R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem det_pow (M : Matrix m m R) (n : ℕ) : det (M ^ n) = det M ^ n :=
  (detMonoidHom : Matrix m m R →* R).map_pow M n

section HomMap

variable {S : Type w} [CommRing S]

/-
**Matrix._root_.RingHom.map_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingHom.map_det (f : R →+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) := by
  simp [Matrix.det_apply', map_sum f, map_prod f]
/-
**Matrix._root_.RingEquiv.map_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingEquiv.map_det (f : R ≃+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
/-
**Matrix._root_.AlgHom.map_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
/-
**Matrix._root_.AlgEquiv.map_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgEquiv.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T]
    (f : S ≃ₐ[R] T) (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toAlgHom.map_det _

@[norm_cast]
/-
**Matrix._root_.Int.cast_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Int.cast_det (M : Matrix n n ℤ) :
    (M.det : R) = (M.map fun x ↦ (x : R)).det :=
  Int.castRingHom R |>.map_det M

@[norm_cast]
/-
**Matrix._root_.Rat.cast_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Rat.cast_det {F : Type*} [Field F] [CharZero F] (M : Matrix n n ℚ) :
    (M.det : F) = (M.map fun x ↦ (x : F)).det :=
  Rat.castHom F |>.map_det M

end HomMap

@[simp]
/-
**Matrix.det_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_conjTranspose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M)
参数：M : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem det_conjTranspose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
  ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


/-
**Matrix.det_eq_zero_of_row_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : forall j, A i j
 = 0) : det A = 0
参数：i : n；h : forall j, A i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_coord_zero`：map_coord_zero {m : ι -> M} (i : ι) (h : 
m i = 0) : f m = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/
theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_coord_zero i (funext h)
/-
**Matrix.det_eq_zero_of_column_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : forall i, A 
i j = 0) : det A = 0
参数：j : n；h : forall i, A i j = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_eq_zero_of_row_eq_zero`：det_eq_zero_of_row_eq_zero {A : Matri
x n n R} (i : n) (h : forall j, A i j = 0) : det A = 0
-/
theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) :
    det A = 0 := by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h

variable {M : Matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
/-
**Matrix.det_zero_of_row_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_zero_of_row_eq (i_ne_j : i != j) (hij : M i = M j) : M.det = 0
参数：i_ne_j : i != j；hij : M i = M j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0

--- 原说明 ---
If a matrix has a repeated row, the determinant will be zero.
-/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

/-- If a matrix has a repeated column, the determinant will be zero. -/
/-
**Matrix.det_zero_of_column_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_zero_of_column_eq (i_ne_j : i != j) (hij : forall k, M k i = M k j) : 
M.det = 0
参数：i_ne_j : i != j；hij : forall k, M k i = M k j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If a matrix has a repeated column, the determinant will be zero.
-/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 := by
  rw [← det_transpose, det_zero_of_row_eq i_ne_j]
  exact funext hij

/-- If we repeat a row of a matrix, we get a matrix of determinant zero. -/
/-
**Matrix.det_updateRow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_eq_zero (h : i != j) : (M.updateRow j (M i)).det = 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If we repeat a row of a matrix, we get a matrix of determinant zero.
-/
theorem det_updateRow_eq_zero (h : i ≠ j) :
    (M.updateRow j (M i)).det = 0 := det_zero_of_row_eq h (by simp [h])

/-- If we repeat a column of a matrix, we get a matrix of determinant zero. -/
/-
**Matrix.det_updateCol_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_eq_zero (h : i != j) : (M.updateCol j (fun k => M k i)).det 
= 0
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_zero_of_column_eq`：det_zero_of_column_eq (i_ne_j : i != j) (h
ij : forall k, M k i = M k j) : M.det = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateCol_ne`：updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' !=
 j) : updateCol M j c i j' = M i j'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateCol_self`：updateCol_self [DecidableEq n] : updateCol M j c 
i j = c i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If we repeat a column of a matrix, we get a matrix of determinant zero.
-/
theorem det_updateCol_eq_zero (h : i ≠ j) :
    (M.updateCol j (fun k ↦ M k i)).det = 0 := det_zero_of_column_eq h (by simp [h])

end DetZero

/-
**Matrix.det_updateRow_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_add (M : Matrix n n R) (j : n) (u v : n -> R) : det (updateR
ow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v)
参数：M : Matrix n n R；j : n；u v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_update_add`：map_update_add [DecidableEq ι] (i : ι) (x
 y : M) : f (update v i (x + y)) = f (update v i x) + f (update v i y)
-/
theorem det_updateRow_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_add M j u v
/-
**Matrix.det_updateCol_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_add (M : Matrix n n R) (j : n) (u v : n -> R) : det (updateC
ol M j <| u + v) = det (updateCol M j u) + det (updateCol M j v)
参数：M : Matrix n n R；j : n；u v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.det_updateRow_add`：det_updateRow_add (M : Matrix n n R) (j : n) (
u v : n -> R) : det (updateRow M j <| u + v) = det (updateRow M j u) + det (upda
teRow M j v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_updateCol_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateCol M j <| u + v) = det (updateCol M j u) + det (updateCol M j v) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_add]
  simp [updateRow_transpose, det_transpose]
/-
**Matrix.det_updateRow_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n -> R) : det (
updateRow M j <| s • u) = s * det (updateRow M j u)
参数：M : Matrix n n R；j : n；s : R；u : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_update_smul`：map_update_smul [DecidableEq ι] (i : ι) 
(r : R) (x : M) : f (update v i (r • x)) = r • f (update v i x)
-/
theorem det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_smul M j s u
/-
**Matrix.det_updateCol_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_smul (M : Matrix n n R) (j : n) (s : R) (u : n -> R) : det (
updateCol M j <| s • u) = s * det (updateCol M j u)
参数：M : Matrix n n R；j : n；s : R；u : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.det_updateRow_smul`：det_updateRow_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateRow M j <| s • u) = s * det (updateRow M j u)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_updateCol_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateCol M j <| s • u) = s * det (updateCol M j u) := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_smul]
  simp [updateRow_transpose, det_transpose]
/-
**Matrix.det_updateRow_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n -> R) : 
det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u)
参数：M : Matrix n n R；j : n；s : R；u : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_smul_left`：map_update_smul_left [DecidableEq ι
] [Fintype ι] (m : forall i, M₁ i) (i : ι) (c : R) (x : M₁ i) : f (update (c • m
) i x) = c ^ (Fintype.car…
-/
theorem det_updateRow_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul_left _ M j s u
/-
**Matrix.det_updateCol_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n -> R) : 
det (updateCol (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateCol M j u)
参数：M : Matrix n n R；j : n；s : R；u : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `Matrix.det_updateRow_smul_left`：det_updateRow_smul_left (M : Matrix n n 
R) (j : n) (s : R) (u : n -> R) : det (updateRow (s • M) j u) = s ^ (Fintype.car
d n - 1) * det (upda…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_updateCol_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateCol (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateCol M j u) := by
  rw [← det_transpose, ← updateRow_transpose, transpose_smul, det_updateRow_smul_left]
  simp [updateRow_transpose, det_transpose]
/-
**Matrix.det_updateRow_sum_aux** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ 
s) (c : n -> R) (a : R) : (M.updateRow j (a • M j + ∑ k in s, (c k) • M k)).det 
= a • M.det
参数：M : Matrix n n R；s : Finset n；hj : j ∉ s；c : n -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Matrix.det_updateRow_smul`：det_updateRow_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateRow M j <| s • u) = s * det (updateRow M j u)
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Matrix.det_updateRow_add`：det_updateRow_add (M : Matrix n n R) (j : n) (
u v : n -> R) : det (updateRow M j <| u + v) = det (updateRow M j u) + det (upda
teRow M j v)
· 使用定理 `Matrix.det_updateRow_eq_zero`：det_updateRow_eq_zero (h : i != j) : (M.up
dateRow j (M i)).det = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n → R)
    (a : R) :
    (M.updateRow j (a • M j + ∑ k ∈ s, (c k) • M k)).det = a • M.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, det_updateRow_smul, updateRow_eq_self]
  | insert k _ hk h_ind =>
      have h : k ≠ j := fun h ↦ (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk, add_comm ((c k) • M k), ← add_assoc, det_updateRow_add,
        det_updateRow_smul, det_updateRow_eq_zero h, mul_zero, add_zero, h_ind]
      exact fun h ↦ hj (Finset.mem_insert_of_mem h)

/-- If we replace a row of a matrix by a linear combination of its rows, then the determinant is
multiplied by the coefficient of that row. -/
/-
**Matrix.det_updateRow_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_sum (A : Matrix n n R) (j : n) (c : n -> R) : (A.updateRow j
 (∑ k, (c k) • A k)).det = (c j) • A.det
参数：A : Matrix n n R；j : n；c : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Matrix.det_updateRow_sum_aux`：det_updateRow_sum_aux (M : Matrix n n R) {
j : n} (s : Finset n) (hj : j ∉ s) (c : n -> R) (a : R) : (M.updateRow j (a • M 
j + ∑ k in s, (c k…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a

--- 原说明 ---
If we replace a row of a matrix by a linear combination of its rows, then the de
terminant is
multiplied by the coefficient of that row.
-/
theorem det_updateRow_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det := by
  convert! det_updateRow_sum_aux A (Finset.univ.erase j) (Finset.univ.notMem_erase j) c (c j)
  rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]

/-- If we replace a column of a matrix by a linear combination of its columns, then the determinant
is multiplied by the coefficient of that column. -/
/-
**Matrix.det_updateCol_sum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_sum (A : Matrix n n R) (j : n) (c : n -> R) : (A.updateCol j
 (fun k => ∑ i, (c i) • A k i)).det = (c j) • A.det
参数：A : Matrix n n R；j : n；c : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.det_updateRow_sum`：det_updateRow_sum (A : Matrix n n R) (j : n) (
c : n -> R) : (A.updateRow j (∑ k, (c k) • A k)).det = (c j) • A.det

--- 原说明 ---
If we replace a column of a matrix by a linear combination of its columns, then 
the determinant
is multiplied by the coefficient of that column.
-/
theorem det_updateCol_sum (A : Matrix n n R) (j : n) (c : n → R) :
    (A.updateCol j (fun k ↦ ∑ i, (c i) • A k i)).det = (c j) • A.det := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  convert! det_updateRow_sum A.transpose j c
  simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply, transpose_apply]

section DetEq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/


/-
**Matrix.det_eq_of_eq_mul_det_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det
 C = 1) (hA : A = B * C) : det A = det B
参数：C : Matrix n n R；hC : det C = 1；hA : A = B * C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/
theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = B * C) : det A = det B :=
  calc
    det A = det (B * C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]
/-
**Matrix.det_eq_of_eq_det_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det
 C = 1) (hA : A = C * B) : det A = det B
参数：C : Matrix n n R；hC : det C = 1；hA : A = C * B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = C * B) : det A = det B :=
  calc
    det A = det (C * B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]
/-
**Matrix.det_updateRow_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_add_self (A : Matrix n n R) {i j : n} (hij : i != j) : det (
updateRow A i (A i + A j)) = det A
参数：A : Matrix n n R；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_updateRow_add`：det_updateRow_add (M : Matrix n n R) (j : n) (
u v : n -> R) : det (updateRow M j <| u + v) = det (updateRow M j u) + det (upda
teRow M j v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_updateRow_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateRow A i (A i + A j)) = det A := by
  simp [det_updateRow_add,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]
/-
**Matrix.det_updateCol_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_add_self (A : Matrix n n R) {i j : n} (hij : i != j) : det (
updateCol A i fun k => A k i + A k j) = det A
参数：A : Matrix n n R；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.det_updateRow_add_self`：det_updateRow_add_self (A : Matrix n n R)
 {i j : n} (hij : i != j) : det (updateRow A i (A i + A j)) = det A
-/
theorem det_updateCol_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateCol A i fun k => A k i + A k j) = det A := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  exact det_updateRow_add_self Aᵀ hij
/-
**Matrix.det_updateRow_add_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateRow_add_smul_self (A : Matrix n n R) {i j : n} (hij : i != j) (c
 : R) : det (updateRow A i (A i + c • A j)) = det A
参数：A : Matrix n n R；hij : i != j；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_updateRow_add`：det_updateRow_add (M : Matrix n n R) (j : n) (
u v : n -> R) : det (updateRow M j <| u + v) = det (updateRow M j u) + det (upda
teRow M j v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `Matrix.det_updateRow_smul`：det_updateRow_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateRow M j <| s • u) = s * det (updateRow M j u)
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_updateRow_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateRow A i (A i + c • A j)) = det A := by
  simp [det_updateRow_add, det_updateRow_smul,
    det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]
/-
**Matrix.det_updateCol_add_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_updateCol_add_smul_self (A : Matrix n n R) {i j : n} (hij : i != j) (c
 : R) : det (updateCol A i fun k => A k i + c • A k j) = det A
参数：A : Matrix n n R；hij : i != j；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.updateRow_transpose`：updateRow_transpose [DecidableEq n] : update
Row Mᵀ j c = (updateCol M j c)ᵀ
· 使用定理 `Matrix.det_updateRow_add_smul_self`：det_updateRow_add_smul_self (A : Mat
rix n n R) {i j : n} (hij : i != j) (c : R) : det (updateRow A i (A i + c • A j)
) = det A
-/
theorem det_updateCol_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateCol A i fun k => A k i + c • A k j) = det A := by
  rw [← det_transpose, ← updateRow_transpose, ← det_transpose A]
  exact det_updateRow_add_smul_self Aᵀ hij c
/-
**Matrix.det_eq_zero_of_not_linearIndependent_rows** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：det_eq_zero_of_not_linearIndependent_rows [IsDomain R] {A : Matrix m m R} 
(hA : ¬ LinearIndependent R (fun i => A i)) : det A = 0
参数：hA : ¬ LinearIndependent R (fun i => A i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_linearDependent`：map_linearDependent {K M N : Type*} 
[Ring K] [IsDomain K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N
] [IsTorsionFree K N] (f…
· 使用定理 `instIsTorsionFree`：∀ {R : Type u_1} [inst : Semiring R], Module.IsTorsio
nFree R R
-/
theorem det_eq_zero_of_not_linearIndependent_rows [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i ↦ A i)) :
    det A = 0 := detRowAlternating.map_linearDependent A hA
/-
**Matrix.linearIndependent_rows_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：linearIndependent_rows_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA 
: A.det != 0) : LinearIndependent R (fun i => A i)
参数：hA : A.det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Matrix.det_eq_zero_of_not_linearIndependent_rows`：det_eq_zero_of_not_lin
earIndependent_rows [IsDomain R] {A : Matrix m m R} (hA : ¬ LinearIndependent R 
(fun i => A i)) : det A = 0
-/
theorem linearIndependent_rows_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R (fun i ↦ A i) := by
  contrapose hA
  exact det_eq_zero_of_not_linearIndependent_rows hA
/-
**Matrix.linearIndependent_cols_of_det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：linearIndependent_cols_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA 
: A.det != 0) : LinearIndependent R A.col
参数：hA : A.det != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linearIndependent_rows_of_det_ne_zero`：linearIndependent_rows_of_
det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det != 0) : LinearIndependen
t R (fun i => A i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem linearIndependent_cols_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R A.col :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by simpa [Matrix.col])
/-
**Matrix.det_eq_zero_of_not_linearIndependent_cols** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：det_eq_zero_of_not_linearIndependent_cols [IsDomain R] {A : Matrix m m R} 
(hA : ¬ LinearIndependent R (fun i => Aᵀ i)) : det A = 0
参数：hA : ¬ LinearIndependent R (fun i => Aᵀ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Matrix.linearIndependent_cols_of_det_ne_zero`：linearIndependent_cols_of_
det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det != 0) : LinearIndependen
t R A.col
-/
theorem det_eq_zero_of_not_linearIndependent_cols [IsDomain R] {A : Matrix m m R}
    (hA : ¬ LinearIndependent R (fun i ↦ Aᵀ i)) :
    det A = 0 := by
  contrapose! hA
  exact linearIndependent_cols_of_det_ne_zero hA
/-
**Matrix.det_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vecMulVec [Nontrivial n] (u v : n -> R) : (vecMulVec u v).det = 0
参数：u v : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateRow_comm`：updateRow_comm [DecidableEq m] (A : Matrix m n α)
 {i i' : m} (h : i != i') (x y : n -> α) : (A.updateRow i x).updateRow i' y = (A
.updateRow …
· 使用定理 `Matrix.updateRow_idem`：updateRow_idem [DecidableEq m] (A : Matrix m n α)
 (i : m) (x y : n -> α) : (A.updateRow i x).updateRow i y = A.updateRow i y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.update_vecMulVec`：update_vecMulVec [DecidableEq m] [Mul α] (u : m
 -> α) (v : n -> α) (i : m) (a : α) : vecMulVec (Function.update u i a) v = (vec
MulVec u v).u…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Matrix.det_updateRow_smul`：det_updateRow_smul (M : Matrix n n R) (j : n)
 (s : R) (u : n -> R) : det (updateRow M j <| s • u) = s * det (updateRow M j u)
· 使用定理 `Matrix.updateRow_eq_self`：updateRow_eq_self [DecidableEq m] (A : Matrix 
m n α) (i : m) : A.updateRow i (A i) = A
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem det_vecMulVec [Nontrivial n] (u v : n → R) : (vecMulVec u v).det = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let uv' := ((vecMulVec u v).updateRow i v).updateRow j v
  have huv' : uv'.det = 0 := by
    refine detRowAlternating.map_eq_zero_of_eq _ ?_ hij
    simp [uv', hij]
  have : vecMulVec u v =
      (uv'.updateRow i (u i • uv' i)).updateRow j (u j • uv'.updateRow i (u i • uv' i) j) := by
    unfold uv'
    rw [updateRow_comm _ hij, updateRow_idem, updateRow_ne hij.symm, updateRow_ne hij,
      updateRow_self, updateRow_self, updateRow_comm _ hij, updateRow_idem,
      ← update_vecMulVec u v j, update_eq_self, ← update_vecMulVec u v i, update_eq_self]
  rw [this, det_updateRow_smul, updateRow_eq_self, det_updateRow_smul, updateRow_eq_self, huv',
    mul_zero, mul_zero]
/-
**Matrix.det_eq_of_forall_row_eq_smul_add_const_aux** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix`。
形式化陈述：det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finse
t n} : forall (c : n -> R) (_ : forall i, i ∉ s -> c i = 0) (k : n) (_ : k ∉ s) 
(_ : forall i j, A i j = B i j + c i * B k j), det A = det B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Matrix.updateRow_apply`：updateRow_apply [DecidableEq m] {i' : m} : updat
eRow M i b i' j = if i' = i then b j else M i' j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Matrix.det_updateRow_add_smul_self`：det_updateRow_add_smul_self (A : Mat
rix n n R) {i j : n} (hij : i != j) (c : R) : det (updateRow A i (A i + c • A j)
) = det A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} :
    ∀ (c : n → R) (_ : ∀ i, i ∉ s → c i = 0) (k : n) (_ : k ∉ s)
      (_ : ∀ i j, A i j = B i j + c i * B k j), det A = det B := by
  induction s using Finset.induction_on generalizing B with
  | empty =>
    rintro c hs k - A_eq
    have : ∀ i, c i = 0 := by grind
    congr
    ext i j
    rw [A_eq, this, zero_mul, add_zero]
  | insert i s _hi ih =>
    intro c hs k hk A_eq
    have hAi : A i = B i + c i • B k := funext (A_eq i)
    rw [@ih (updateRow B i (A i)) (Function.update c i 0), hAi, det_updateRow_add_smul_self]
    · exact mt (fun h => show k ∈ insert i s from h ▸ Finset.mem_insert_self _ _) hk
    · intro i' hi'
      rw [Function.update_apply]
      split_ifs with hi'i
      · rfl
      · exact hs i' fun h => hi' ((Finset.mem_insert.mp h).resolve_left hi'i)
    · exact k
    · exact fun h => hk (Finset.mem_insert_of_mem h)
    · intro i' j'
      rw [updateRow_apply, Function.update_apply]
      split_ifs with hi'i
      · simp [hi'i]
      rw [A_eq, updateRow_ne fun h : k = i => hk <| h ▸ Finset.mem_insert_self k s]

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
/-
**Matrix.det_eq_of_forall_row_eq_smul_add_const** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x`。
形式化陈述：det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n -> R) (
k : n) (hk : c k = 0) (A_eq : forall i j, A i j = B i j + c i * B k j) : det A =
 det B
参数：c : n -> R；k : n；hk : c k = 0；A_eq : forall i j, A i j = B i j + c i * B k j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_eq_of_forall_row_eq_smul_add_const_aux`：det_eq_of_forall_row_
eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} : forall (c : n -> R) 
(_ : forall i, i ∉ s -> c i = 0) (k : n…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a

--- 原说明 ---
If you add multiples of row `B k` to other rows, the determinant doesn't change.
-/
theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n → R) (k : n)
    (hk : c k = 0) (A_eq : ∀ i j, A i j = B i j + c i * B k j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.notMem_erase k Finset.univ) A_eq
/-
**Matrix.det_eq_of_forall_row_eq_smul_add_pred_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：det_eq_of_forall_row_eq_smul_add_pred_aux {n : Nat} (k : Fin (n + 1)) : fo
rall (c : Fin n -> R) (_hc : forall i : Fin n, k < i.succ -> c i = 0) {M N : Mat
rix (Fin n.succ) (Fin n.succ) R} (_h0 : forall j, M 0 j = N 0 j) (_hsucc : foral
l (i : Fin n) (j), M i.succ j = N i.succ j + c i * M (Fin.castSucc i) j), det M 
= det N
参数：k : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.succ_pos`：∀ {n : ℕ} (a : Fin n), 0 < a.succ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.updateRow.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq m} [inst_1 : DecidableEq m] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (i i_…
· 使用定理 `Matrix.updateRow_self`：updateRow_self [DecidableEq m] : updateRow M i b 
i = b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.updateRow_ne`：updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' !=
 i) : updateRow M i b i' = M i'
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_updateRow_add_smul_self`：det_updateRow_add_smul_self (A : Mat
rix n n R) {i j : n} (hij : i != j) (c : R) : det (updateRow A i (A i + c • A j)
) = det A
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
（共 39 条，此处仅展示前 30 条）
-/
theorem det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : Fin (n + 1)) :
    ∀ (c : Fin n → R) (_hc : ∀ i : Fin n, k < i.succ → c i = 0)
      {M N : Matrix (Fin n.succ) (Fin n.succ) R} (_h0 : ∀ j, M 0 j = N 0 j)
      (_hsucc : ∀ (i : Fin n) (j), M i.succ j = N i.succ j + c i * M (Fin.castSucc i) j),
      det M = det N := by
  refine Fin.induction ?_ (fun k ih => ?_) k <;> intro c hc M N h0 hsucc
  · congr
    ext i j
    refine Fin.cases (h0 j) (fun i => ?_) i
    rw [hsucc, hc i (Fin.succ_pos _), zero_mul, add_zero]
  set M' := updateRow M k.succ (N k.succ) with hM'
  have hM : M = updateRow M' k.succ (M' k.succ + c k • M (Fin.castSucc k)) := by
    ext i j
    by_cases hi : i = k.succ
    · simp [hi, hM', hsucc, updateRow_self]
    rw [updateRow_ne hi, hM', updateRow_ne hi]
  have k_ne_succ : (Fin.castSucc k) ≠ k.succ := Fin.castSucc_lt_succ.ne
  have M_k : M (Fin.castSucc k) = M' (Fin.castSucc k) := (updateRow_ne k_ne_succ).symm
  rw [hM, M_k, det_updateRow_add_smul_self M' k_ne_succ.symm, ih (Function.update c k 0)]
  · intro i hi
    rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Nat.lt_succ_iff] at hi
    rw [Function.update_apply]
    split_ifs with hik
    · rfl
    exact hc _ (Fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (Ne.symm hik)))
  · rwa [hM', updateRow_ne (Fin.succ_ne_zero _).symm]
  intro i j
  rw [Function.update_apply]
  split_ifs with hik
  · rw [zero_mul, add_zero, hM', hik, updateRow_self]
  rw [hM', updateRow_ne ((Fin.succ_injective _).ne hik), hsucc]
  by_cases hik2 : k < i
  · simp [hc i (Fin.succ_lt_succ_iff.mpr hik2)]
  rw [updateRow_ne]
  apply ne_of_lt
  rwa [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Nat.lt_succ_iff, ← not_lt]

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
/-
**Matrix.det_eq_of_forall_row_eq_smul_add_pred** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：det_eq_of_forall_row_eq_smul_add_pred {n : Nat} {A B : Matrix (Fin (n + 1)
) (Fin (n + 1)) R} (c : Fin n -> R) (A_zero : forall j, A 0 j = B 0 j) (A_succ :
 forall (i : Fin n) (j), A i.succ j = B i.succ j + c i * A (Fin.castSucc i) j) :
 det A = det B
参数：Fin (n + 1)；Fin (n + 1)；c : Fin n -> R；A_zero : forall j, A 0 j = B 0 j；A_suc
c : forall (i : Fin n) (j), A i.succ j = B i.succ j + c i * A (Fin.castSucc i) j
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_eq_of_forall_row_eq_smul_add_pred_aux`：det_eq_of_forall_row_e
q_smul_add_pred_aux {n : Nat} (k : Fin (n + 1)) : forall (c : Fin n -> R) (_hc :
 forall i : Fin n, k < i.succ -> c i =…
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n

--- 原说明 ---
If you add multiples of previous rows to the next row, the determinant doesn't c
hange.
-/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ j, A 0 j = B 0 j)
    (A_succ : ∀ (i : Fin n) (j), A i.succ j = B i.succ j + c i * A (Fin.castSucc i) j) :
    det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun _ hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
/-
**Matrix.det_eq_of_forall_col_eq_smul_add_pred** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：det_eq_of_forall_col_eq_smul_add_pred {n : Nat} {A B : Matrix (Fin (n + 1)
) (Fin (n + 1)) R} (c : Fin n -> R) (A_zero : forall i, A i 0 = B i 0) (A_succ :
 forall (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)) :
 det A = det B
参数：Fin (n + 1)；Fin (n + 1)；c : Fin n -> R；A_zero : forall i, A i 0 = B i 0；A_suc
c : forall (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_eq_of_forall_row_eq_smul_add_pred`：det_eq_of_forall_row_eq_sm
ul_add_pred {n : Nat} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (c : Fin n ->
 R) (A_zero : forall j, A 0 j = B …

--- 原说明 ---
If you add multiples of previous columns to the next columns, the determinant do
esn't change.
-/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ i, A i 0 = B i 0)
    (A_succ : ∀ (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)) :
    det A = det B := by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

end DetEq

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.det_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] (M : o -> Matrix
 n n R) : (blockDiagonal M).det = ∏ k, (M k).det
参数：M : o -> Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply'`：det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n,
 ε σ * ∏ i, M (σ i) i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Finset.prod_sum`：prod_sum {κ : ι -> Type*} (s : Finset ι) (t : forall i,
 Finset (κ i)) (f : forall i, κ i -> R) : ∏ a in s, ∑ b in t a, f a b = ∑ p in s
.pi t…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_attach_univ`：prod_attach_univ [Fintype ι] (f : {i // i in @u
niv ι _} -> M) : ∏ i in univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩
· 使用定理 `Finset.univ_pi_univ`：Finset.univ_pi_univ {α : Type*} {β : α -> Type*} [D
ecidableEq α] [Fintype α] [forall a, Fintype (β a)] : (Finset.univ.pi fun a : α 
=> (Finse…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Matrix.blockDiagonal_apply_ne`：blockDiagonal_apply_ne (M : o -> Matrix m
 n α) (i j) {k k'} (h : k != k') : blockDiagonal M (i, k) (j, k') = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
（共 41 条，此处仅展示前 30 条）
-/
theorem det_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] (M : o → Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det := by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right-hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equiv.Perm (n × o)) := {σ | ∀ x, (σ x).snd = x.snd}
  have mem_preserving_snd :
    ∀ {σ : Equiv.Perm (n × o)}, σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd := fun {σ} =>
    Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → Equiv.Perm m`.
  · refine (Finset.sum_bij (fun σ _ => prodCongrLeft fun k ↦ σ k (mem_univ k)) ?_ ?_ ?_ ?_).symm
    · intro σ _
      rw [mem_preserving_snd]
      rintro ⟨-, x⟩
      simp only [prodCongrLeft_apply]
    · intro σ _ σ' _ eq
      ext x hx k
      have :
        ∀ k x,
          prodCongrLeft (fun k => σ k (Finset.mem_univ _)) (k, x) =
            prodCongrLeft (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
        fun k x => by rw [eq]
      simp only [prodCongrLeft_apply, Prod.mk_inj] at this
      exact (this k x).1
    · intro σ hσ
      rw [mem_preserving_snd] at hσ
      have hσ' x : (σ.symm x).snd = x.snd := by simpa [eq_comm] using hσ (σ.symm x)
      have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k) := by
        intro k x
        ext
        · simp only
        · simp only [hσ]
      have mk_inv_apply_eq : ∀ k x, ((σ.symm (x, k)).fst, k) = σ.symm (x, k) := by grind
      refine ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ.symm (x, k)).fst, ?_, ?_⟩, ?_, ?_⟩
      · intro x
        simp [mk_apply_eq]
      · intro x
        simp [mk_inv_apply_eq]
      · apply Finset.mem_univ
      · ext ⟨k, x⟩
        · simp only [coe_fn_mk, prodCongrLeft_apply]
        · simp only [prodCongrLeft_apply, hσ]
    · intro σ _
      rw [Finset.prod_mul_distrib, ← Finset.univ_product_univ, Finset.prod_product_right]
      simp only [sign_prodCongrLeft, Units.coe_prod, Int.cast_prod, blockDiagonal_apply_eq,
        prodCongrLeft_apply]
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k, x)), mul_zero]
    rw [blockDiagonal_apply_ne]
    exact hkx

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a 2×2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_isUpperTriangular`. -/
@[simp]
/-
**Matrix.det_fromBlocks_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a 2×2 block matrix with the lower-left block equal to zero is
 the product of
the determinants of the diagonal blocks. For the generalization to any number of
 blocks, see
`Matrix.det_of_isUpperTriangular`.
-/
theorem det_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
    simp_rw [det_apply']
    convert!
      Eq.symm <|
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
      · intro σ₁₂ _
        simp
      · intro σ₁ _ σ₂ _
        dsimp only
        intro h
        have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
          DFunLike.congr_fun h
        simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
          Sum.inr.injEq] at h2
        ext x
        · exact h2.left x
        · exact h2.right x
      · intro σ hσ
        rw [mem_coe, Set.mem_toFinset] at hσ
        obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
        use σ₁₂
        rw [← hσ₁₂]
        simp
      · simp only [forall_prop_of_true, Prod.forall, mem_univ]
        intro σ₁ σ₂
        rw [Fintype.prod_sum_type]
        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
          fromBlocks_apply₂₂]
        rw [mul_mul_mul_comm]
        congr
        rw [sign_sumCongr, Units.val_mul, Int.cast_mul]
    · rintro σ - hσn
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσn
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
      obtain ⟨a, ha⟩ := not_forall.mp h1
      rcases hx : σ (Sum.inl a) with a2 | b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
        rw [hx, fromBlocks_apply₂₁, zero_apply]

/-- The determinant of a 2×2 block matrix with the upper-right block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`Matrix.det_of_isLowerTriangular`. -/
@[simp]
/-
**Matrix.det_fromBlocks_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a 2×2 block matrix with the upper-right block equal to zero i
s the product of
the determinants of the diagonal blocks. For the generalization to any number of
 blocks, see
`Matrix.det_of_isLowerTriangular`.
-/
theorem det_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← det_transpose, fromBlocks_transpose, transpose_zero, det_fromBlocks_zero₂₁, det_transpose,
    det_transpose]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
/-
**Matrix.det_succ_column_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_succ_column_zero {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) : 
det A = ∑ i : Fin n.succ, (-1) ^ (i : Nat) * A i 0 * det (A.submatrix i.succAbov
e Fin.succ)
参数：A : Matrix (Fin n.succ) (Fin n.succ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.univ_perm_fin_succ`：Finset.univ_perm_fin_succ {n : Nat} : @Finset
.univ (Perm <| Fin n.succ) _ = (Finset.univ : Finset <| Fin n.succ × Perm (Fin n
)).map Equiv.Pe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_product_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintyp
e α] [inst_1 : Fintype β], Finset.univ ×ˢ Finset.univ = Finset.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.decomposeFin.symm_sign`：Equiv.Perm.decomposeFin.symm_sign {n 
: Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) : Perm.sign (Equiv.Perm.decomposeFin
.symm (p, e)) = ite (p …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `Equiv.Perm.decomposeFin_symm_apply_zero`：Equiv.Perm.decomposeFin_symm_ap
ply_zero {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) : Equiv.Perm.decomposeFi
n.symm (p, e) 0 = p
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.decomposeFin_symm_apply_succ`：Equiv.Perm.decomposeFin_symm_ap
ply_succ {n : Nat} (e : Perm (Fin n)) (p : Fin (n + 1)) (x : Fin n) : Equiv.Perm
.decomposeFin.symm (p, e) x.s…
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0.
-/
theorem det_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succAbove Fin.succ) := by
  rw [Matrix.det_apply, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero, one_mul,
      Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_self, if_true, id,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, Equiv.coe_refl, pow_zero,
      mul_smul_comm, of_apply]
  -- `univ_perm_fin_succ` gives a different embedding of `Perm (Fin n)` into
  -- `Perm (Fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = (Perm.sign i.cycleRange) := by simp [Fin.sign_cycleRange]
  rw [Fin.val_succ, pow_succ', this, mul_assoc, mul_assoc, mul_left_comm (ε _),
    ← det_permute, Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Equiv.Perm.decomposeFin.symm_sign, if_neg (Fin.succ_ne_zero i)]
  calc
    ((-1 * Perm.sign σ : ℤ) • ∏ i', A (Perm.decomposeFin.symm (Fin.succ i, σ) i') i') =
        (-1 * Perm.sign σ : ℤ) • (A (Fin.succ i) 0 *
          ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
        Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
    _ = -1 * (A (Fin.succ i) 0 * (Perm.sign σ : ℤ) •
        ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp [_root_.neg_mul, one_mul, zsmul_eq_mul, neg_smul,
        Fin.succAbove_cycleRange, mul_left_comm]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
/-
**Matrix.det_succ_row_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_succ_row_zero {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) : det
 A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * det (A.submatrix Fin.succ j.su
ccAbove)
参数：A : Matrix (Fin n.succ) (Fin n.succ) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_succ_column_zero`：det_succ_column_zero {n : Nat} (A : Matrix 
(Fin n.succ) (Fin n.succ) R) : det A = ∑ i : Fin n.succ, (-1) ^ (i : Nat) * A i 
0 * det (A.submat…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0.
-/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * det (A.submatrix Fin.succ j.succAbove) := by
  rw [← det_transpose A, det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
/-
**Matrix.det_succ_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n
.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) * A i j * det (A.submatr
ix i.succAbove j.succAbove)
参数：A : Matrix (Fin n.succ) (Fin n.succ) R；i : Fin n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Equiv.Perm.sign_inv`：sign_inv (f : Perm α) : sign f⁻¹ = sign f
· 使用定理 `Fin.sign_cycleRange`：sign_cycleRange (i : Fin n) : Perm.sign (cycleRange
 i) = (-1) ^ (i : Nat)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_permute`：det_permute (σ : Perm n) (M : Matrix n n R) : (M.sub
matrix σ id).det = Perm.sign σ * M.det
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_succ_row_zero`：det_succ_row_zero {n : Nat} (A : Matrix (Fin n
.succ) (Fin n.succ) R) : det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * de
t (A.submatrix…
· 使用定理 `Matrix.submatrix_apply`：submatrix_apply (A : Matrix m n α) (r : l -> m) 
(c : o -> n) (i j) : A.submatrix r c i j = A (r i) (c j)
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Fin.cycleRange_symm_zero`：cycleRange_symm_zero [NeZero n] (i : Fin n) : 
i.cycleRange.symm 0 = i
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`.
-/
theorem det_succ_row {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    det A =
      ∑ j : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * det A := by
    calc
      det A = ↑((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ) : ℤˣ) * det A := by simp
      _ = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * det A := by simp [-Int.units_mul_self]
  rw [this, mul_assoc]
  congr
  rw [← det_permute, det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Matrix.submatrix_apply, submatrix_submatrix, id_comp, Function.comp_def, id]
  simp

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
/-
**Matrix.det_succ_column** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_succ_column {n : Nat} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fi
n n.succ) : det A = ∑ i : Fin n.succ, (-1) ^ (i + j : Nat) * A i j * det (A.subm
atrix i.succAbove j.succAbove)
参数：A : Matrix (Fin n.succ) (Fin n.succ) R；j : Fin n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M

--- 原说明 ---
Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`
.
-/
theorem det_succ_column {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    det A =
      ∑ i : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) := by
  rw [← det_transpose, det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, ← det_transpose, transpose_apply, transpose_submatrix, transpose_transpose]

/-- Determinant of 0x0 matrix -/
@[simp]
/-
**Matrix.det_fin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A = 1
参数：Fin 0；Fin 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1

--- 原说明 ---
Determinant of 0x0 matrix
-/
theorem det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A = 1 :=
  det_isEmpty

/-- Determinant of 1x1 matrix -/
/-
**Matrix.det_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A = A 0 0
参数：A : Matrix (Fin 1) (Fin 1) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default

--- 原说明 ---
Determinant of 1x1 matrix
-/
theorem det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A = A 0 0 :=
  det_unique A
/-
**Matrix.det_fin_one_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_one_of (a : R) : det !![a] = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_fin_one`：det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A =
 A 0 0
-/
theorem det_fin_one_of (a : R) : det !![a] = a :=
  det_fin_one _

/-- Determinant of 2x2 matrix -/
/-
**Matrix.det_fin_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A = A 0 0 * A 1 1 - A 0 1
 * A 1 0
参数：A : Matrix (Fin 2) (Fin 2) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_succ_row_zero`：det_succ_row_zero {n : Nat} (A : Matrix (Fin n
.succ) (Fin n.succ) R) : det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * de
t (A.submatrix…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用引理 `Fin.succ_succAbove_zero`：succ_succAbove_zero {n : Nat} [NeZero n] (i : F
in n) : succAbove i.succ 0 = 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Determinant of 2x2 matrix
-/
theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp only [det_succ_row_zero, det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, sum_singleton]
  ring

@[simp]
/-
**Matrix.det_fin_two_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_two_of (a b c d : R) : Matrix.det !![a, b; c, d] = a * d - b * c
参数：a b c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
-/
theorem det_fin_two_of (a b c d : R) : Matrix.det !![a, b; c, d] = a * d - b * c :=
  det_fin_two _

/-- Determinant of 3x3 matrix -/
/-
**Matrix.det_fin_three** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_fin_three (A : Matrix (Fin 3) (Fin 3) R) : det A = A 0 0 * A 1 1 * A 2
 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0
 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0
参数：A : Matrix (Fin 3) (Fin 3) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_succ_row_zero`：det_succ_row_zero {n : Nat} (A : Matrix (Fin n
.succ) (Fin n.succ) R) : det A = ∑ j : Fin n.succ, (-1) ^ (j : Nat) * A 0 j * de
t (A.submatrix…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用引理 `Fin.succ_succAbove_zero`：succ_succAbove_zero {n : Nat} [NeZero n] (i : F
in n) : succAbove i.succ 0 = 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Fin.succ_succAbove_one`：∀ {n : ℕ} [inst : NeZero n] (i : Fin (n + 1)), i
.succ.succAbove 1 = (i.succAbove 0).succ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
Determinant of 3x3 matrix
-/
theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
      - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
      + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_zero, sum_singleton, Fin.succ_succAbove_one]
  ring

end Matrix

