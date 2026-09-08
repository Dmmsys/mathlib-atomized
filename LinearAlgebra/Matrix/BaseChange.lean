/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Field.Subfield.Defs

/-!
# Matrices and base change

This file is a home for results about base change for matrices.

## Main results:
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (right) inverse.
* `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left`: if an invertible matrix over `L` takes
  values in subfield `K ⊆ L`, then so does its (left) inverse.

-/

public section

namespace Matrix

variable {m n L : Type*} [Finite m] [Fintype n] [DecidableEq m] [Field L]
  (e : m ≃ n) (K : Subfield L) {A : Matrix m n L} {B : Matrix n m L} (hAB : A * B = 1)

include e hAB

/-
**Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right** 是 Mathlib 中的一个引理，位于命
名空间 `Matrix`。
形式化陈述：mem_subfield_of_mul_eq_one_of_mem_subfield_right (h_mem : forall i j, A i 
j in K) (i : n) (j : m) : B i j in K
参数：h_mem : forall i j, A i j in K；i : n；j : m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsStablyFiniteRingSubtypeMem`：∀ {R : Type u_10} {F : Type u_12} [ins
t : NonAssocSemiring R] [inst_1 : SetLike F R] [inst_2 : SubsemiringClass F R]  
 (S : F) [IsStablyFini…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.submatrix_id_mul_left`：submatrix_id_mul_left [Fintype n] [Fintype
 o] [Mul α] [AddCommMonoid α] {p : Type*} (M : Matrix m n α) (N : Matrix o p α) 
(e₁ : l -> m) (e₂ …
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
（共 34 条，此处仅展示前 30 条）
-/
lemma mem_subfield_of_mul_eq_one_of_mem_subfield_right
    (h_mem : ∀ i j, A i j ∈ K) (i : n) (j : m) :
    B i j ∈ K := by
  cases nonempty_fintype m
  let A' : Matrix m m K := of fun i j ↦ ⟨A.submatrix id e i j, h_mem i (e j)⟩
  have hA' : A'.map K.subtype = A.submatrix id e := rfl
  have hA : IsUnit A' := by
    have h_unit : IsUnit (A.submatrix id e) :=
      .of_mul_eq_one (B.submatrix e id) (by simpa)
    have h_det : (A.submatrix id e).det = K.subtype A'.det := by
      simp [A', K.subtype.map_det, map, submatrix]
    simpa [isUnit_iff_isUnit_det, h_det] using! h_unit
  obtain ⟨B', hB⟩ := isUnit_iff_exists_inv.mp hA
  suffices (B'.submatrix e.symm id).map K.subtype = B by simp [← this]
  replace hB : A * (B'.submatrix e.symm id).map K.subtype = 1 := by
    replace hB := congr_arg (fun C ↦ C.map K.subtype) hB
    simp_rw [Matrix.map_mul] at hB
    rw [hA', ← e.symm_symm, ← submatrix_id_mul_left] at hB
    simpa using! hB
  classical
  simpa [← Matrix.mul_assoc, (mul_eq_one_comm_of_equiv e).mp hAB] using! congr_arg (B * ·) hB
/-
**Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left** 是 Mathlib 中的一个引理，位于命名
空间 `Matrix`。
形式化陈述：mem_subfield_of_mul_eq_one_of_mem_subfield_left (h_mem : forall i j, B i j
 in K) (i : m) (j : n) : A i j in K
参数：h_mem : forall i j, B i j in K；i : m；j : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用引理 `Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right`：mem_subfield_of
_mul_eq_one_of_mem_subfield_right (h_mem : forall i j, A i j in K) (i : n) (j : 
m) : B i j in K
-/
lemma mem_subfield_of_mul_eq_one_of_mem_subfield_left
    (h_mem : ∀ i j, B i j ∈ K) (i : m) (j : n) :
    A i j ∈ K := by
  replace hAB : Bᵀ * Aᵀ = 1 := by simpa using congr_arg transpose hAB
  rw [← A.transpose_apply]
  simp_rw [← B.transpose_apply] at h_mem
  exact mem_subfield_of_mul_eq_one_of_mem_subfield_right e K hAB (fun i j ↦ h_mem j i) j i

end Matrix

