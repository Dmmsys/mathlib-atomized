/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Transitivity of algebra norm

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## References

* [silvester2000] Silvester, *Determinants of Block Matrices*, The Mathematical Gazette (2000).

-/

@[expose] public section

variable {R S A n m : Type*} [CommRing R] [CommRing S]
variable (M : Matrix m m S) [DecidableEq m] [DecidableEq n] (k : m)
open Matrix Polynomial

namespace Algebra.Norm.Transitivity

/-- Given a ((m-1)+1)x((m-1)+1) block matrix `M = [[A,b],[c,d]]`, `auxMat M k` is the auxiliary
matrix `[[dI,0],[-c,1]]`. `k` corresponds to the last row/column of the matrix. -/
/-
**Algebra.Norm.Transitivity.auxMat** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Norm.Trans
itivity`。
形式化陈述：auxMat : Matrix m m S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ((m-1)+1)x((m-1)+1) block matrix `M = [[A,b],[c,d]]`, `auxMat M k` is th
e auxiliary
matrix `[[dI,0],[-c,1]]`. `k` corresponds to the last row/column of the matrix.
-/
def auxMat : Matrix m m S :=
  of fun i j ↦
    if j = k then
      if i = k then 1 else 0
    else if i = k then -M k j
    else if i = j then M k k
    else 0

/-- `aux M k` is lower triangular. -/
/-
**Algebra.Norm.Transitivity.auxMat_blockTriangular** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Norm.Transitivity`。
形式化陈述：auxMat_blockTriangular : (auxMat M k).BlockTriangular (· != k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Norm.Transitivity.auxMat.eq_1`：∀ {S : Type u_2} {m : Type u_5} [
inst : CommRing S] (M : Matrix m m S) [inst_1 : DecidableEq m] (k : m),   Algebr
a.Norm.Transitivity.auxMat …
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
`aux M k` is lower triangular.
-/
lemma auxMat_blockTriangular : (auxMat M k).BlockTriangular (· ≠ k) :=
  fun i j lt ↦ by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp, not_not] at lt
    rw [auxMat, of_apply, if_pos lt.2, if_neg lt.1]
/-
**Algebra.Norm.Transitivity.auxMat_toSquareBlock_ne** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.Norm.Transitivity`。
形式化陈述：auxMat_toSquareBlock_ne : (auxMat M k).toSquareBlock (· != k) True = M k k
 • 1
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
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma auxMat_toSquareBlock_ne : (auxMat M k).toSquareBlock (· ≠ k) True = M k k • 1 := by
  ext i j
  simp [auxMat, toSquareBlock_def, if_neg (of_eq_true i.2), if_neg (of_eq_true j.2),
    Matrix.one_apply, Subtype.ext_iff]
/-
**Algebra.Norm.Transitivity.auxMat_toSquareBlock_eq** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.Norm.Transitivity`。
形式化陈述：auxMat_toSquareBlock_eq : (auxMat M k).toSquareBlock (· != k) False = 1
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
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma auxMat_toSquareBlock_eq : (auxMat M k).toSquareBlock (· ≠ k) False = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff, iff_false, not_not] at hi hj
  simp [auxMat, toSquareBlock_def, if_pos hi, if_pos hj, Matrix.one_apply, if_pos (hj ▸ hi)]

variable [Fintype m]

/-- `M * aux M k` is upper triangular. -/
/-
**Algebra.Norm.Transitivity.mul_auxMat_blockTriangular** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.Norm.Transitivity`。
形式化陈述：mul_auxMat_blockTriangular : (M * auxMat M k).BlockTriangular (· = k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
`M * aux M k` is upper triangular.
-/
lemma mul_auxMat_blockTriangular : (M * auxMat M k).BlockTriangular (· = k) :=
  fun i j lt ↦ by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp] at lt
    simp_rw [Matrix.mul_apply, auxMat, of_apply, if_neg lt.2, mul_ite, mul_neg, mul_zero]
    rw [Finset.sum_ite, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton,
      Finset.sum_ite_eq', if_pos, lt.1, mul_comm, neg_add_cancel]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt.2⟩

/-- The lower-right corner of `M * aux M k` is the same as the corner of `M`. -/
/-
**Algebra.Norm.Transitivity.mul_auxMat_corner** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.Norm.Transitivity`。
形式化陈述：mul_auxMat_corner : (M * auxMat M k) k k = M k k
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

--- 原说明 ---
The lower-right corner of `M * aux M k` is the same as the corner of `M`.
-/
lemma mul_auxMat_corner : (M * auxMat M k) k k = M k k := by simp [Matrix.mul_apply, auxMat]
/-
**Algebra.Norm.Transitivity.mul_auxMat_toSquareBlock_eq** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.Norm.Transitivity`。
形式化陈述：mul_auxMat_toSquareBlock_eq : (M * auxMat M k).toSquareBlock (· = k) True 
= M k k • 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用引理 `Algebra.Norm.Transitivity.mul_auxMat_corner`：mul_auxMat_corner : (M * au
xMat M k) k k = M k k
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_auxMat_toSquareBlock_eq :
    (M * auxMat M k).toSquareBlock (· = k) True = M k k • 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff, iff_true] at hi hj
  simp [toSquareBlock_def, hi, hj, mul_auxMat_corner]

set_option quotPrecheck false in
/-- The upper-left block of `M * aux M k`. -/
scoped notation "mulAuxMatBlock" => (M * auxMat M k).toSquareBlock (· = k) False

/-
**Algebra.Norm.Transitivity.det_mul_corner_pow** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Norm.Transitivity`。
形式化陈述：det_mul_corner_pow : M.det * M k k ^ (Fintype.card m - 1) = M k k * (mulAu
xMatBlock).det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.BlockTriangular.det_fintype`：∀ {α : Type u_1} {m : Type u_3} {R :
 Type v} {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableE
q m]   [inst_2 : Fintype…
· 使用引理 `Algebra.Norm.Transitivity.auxMat_blockTriangular`：auxMat_blockTriangular
 : (auxMat M k).BlockTriangular (· != k)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fintype.univ_Prop`：Fintype.univ_Prop : (Finset.univ : Finset Prop) = {Tr
ue, False}
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `Algebra.Norm.Transitivity.auxMat_toSquareBlock_ne`：auxMat_toSquareBlock_
ne : (auxMat M k).toSquareBlock (· != k) True = M k k • 1
· 使用定理 `Matrix.det_smul_of_tower`：det_smul_of_tower {α} [Monoid α] [MulAction α 
R] [IsScalarTower α R R] [SMulCommClass α R R] (c : α) (A : Matrix n n R) : det 
(c • A) = c ^ …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用引理 `Algebra.Norm.Transitivity.auxMat_toSquareBlock_eq`：auxMat_toSquareBlock_
eq : (auxMat M k).toSquareBlock (· != k) False = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.Norm.Transitivity.mul_auxMat_blockTriangular`：mul_auxMat_blockTr
iangular : (M * auxMat M k).BlockTriangular (· = k)
· 使用定理 `Fintype.prod_Prop`：∀ {M : Type u_4} [inst : CommMonoid M] (f : Prop → M)
, ∏ p, f p = f True * f False
（共 37 条，此处仅展示前 30 条）
-/
lemma det_mul_corner_pow :
    M.det * M k k ^ (Fintype.card m - 1) = M k k * (mulAuxMatBlock).det := by
  trans (M * auxMat M k).det
  · simp [det_mul, (auxMat_blockTriangular M k).det_fintype,
      auxMat_toSquareBlock_ne, auxMat_toSquareBlock_eq]
  rw [(mul_auxMat_blockTriangular M k).det_fintype, Fintype.prod_Prop, mul_auxMat_toSquareBlock_eq]
  simp_rw [det_smul_of_tower, eq_iff_iff, iff_true, Fintype.card_unique,
    pow_one, det_one, smul_eq_mul, mul_one]
  -- `Decidable (P = Q)` diamond induced by `Prop.linearOrder`, which is classical, when `P` and `Q`
  -- are themselves decidable.
  convert! rfl

/-- A matrix with X added to the corner. -/
/-
**Algebra.Norm.Transitivity.cornerAddX** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Norm.T
ransitivity`。
形式化陈述：cornerAddX : Matrix m m S[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix with X added to the corner.
-/
noncomputable def cornerAddX : Matrix m m S[X] :=
  (diagonal fun i ↦ if i = k then X else 0) + M.map C

variable [Fintype n] (f : S →+* Matrix n n R)

omit [Fintype m] in
/-
**Algebra.Norm.Transitivity.polyToMatrix_cornerAddX** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.Norm.Transitivity`。
形式化陈述：polyToMatrix_cornerAddX : f.polyToMatrix (cornerAddX M k k k) = (-f (M k k
)).charmatrix
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `matPolyEquiv_symm_X`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   matPolyEquiv.symm Polynomial
.X = Matr…
· 使用定理 `matPolyEquiv_symm_C`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type 
w} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   matPolyEq
uiv.symm …
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
lemma polyToMatrix_cornerAddX :
    f.polyToMatrix (cornerAddX M k k k) = (-f (M k k)).charmatrix := by
  simp [cornerAddX, Matrix.add_apply, charmatrix,
    RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, map_neg]
/-
**Algebra.Norm.Transitivity.eval_zero_det_det** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.Norm.Transitivity`。
形式化陈述：eval_zero_det_det : eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f 
M.det).det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_evalRingHom`：coe_evalRingHom (r : R) : (evalRingHom r : R
[X] -> R) = eval r
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用引理 `evalRingHom_mapMatrix_comp_polyToMatrix`：evalRingHom_mapMatrix_comp_poly
ToMatrix : (evalRingHom 0).mapMatrix.comp f.polyToMatrix = f.comp (evalRingHom 0
)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_zero_det_det : eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det := by
  rw [← coe_evalRingHom, RingHom.map_det, ← RingHom.comp_apply,
    evalRingHom_mapMatrix_comp_polyToMatrix, f.comp_apply, RingHom.map_det]
  congr; ext; simp [cornerAddX, diagonal, apply_ite]
/-
**Algebra.Norm.Transitivity.eval_zero_comp_det** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Norm.Transitivity`。
形式化陈述：eval_zero_comp_det : eval 0 (comp m m n n R[X] <| (cornerAddX M k).map f.p
olyToMatrix).det = (comp m m n n R <| M.map f).det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `evalRingHom_mapMatrix_comp_compRingEquiv`：evalRingHom_mapMatrix_comp_com
pRingEquiv {m} [Fintype m] [DecidableEq m] : (evalRingHom 0).mapMatrix.comp (com
pRingEquiv m n R[X]) = (compRi…
· 使用引理 `evalRingHom_mapMatrix_comp_polyToMatrix`：evalRingHom_mapMatrix_comp_poly
ToMatrix : (evalRingHom 0).mapMatrix.comp f.polyToMatrix = f.comp (evalRingHom 0
)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_zero_comp_det :
    eval 0 (comp m m n n R[X] <| (cornerAddX M k).map f.polyToMatrix).det =
      (comp m m n n R <| M.map f).det := by
  simp_rw [← coe_evalRingHom, RingHom.map_det, ← compRingEquiv_apply, ← RingEquiv.coe_toRingHom,
    ← RingHom.mapMatrix_apply, ← RingHom.comp_apply, ← RingHom.comp_assoc,
    evalRingHom_mapMatrix_comp_compRingEquiv, RingHom.comp_assoc, RingHom.mapMatrix_comp,
    evalRingHom_mapMatrix_comp_polyToMatrix, ← RingHom.mapMatrix_comp, RingHom.comp_apply]
  congr with i j
  simp [cornerAddX, diagonal, apply_ite]
/-
**Algebra.Norm.Transitivity.comp_det_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
Norm.Transitivity`。
形式化陈述：comp_det_mul_pow : ((M.map f).comp m m n n R).det * (f (M k k)).det ^ (Fin
type.card m - 1) = (f (M k k)).det * (((mulAuxMatBlock).map f).comp _ _ n n R).d
et
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.BlockTriangular.det_fintype`：∀ {α : Type u_1} {m : Type u_3} {R :
 Type v} {M : Matrix m m R} {b : m → α} [inst : CommRing R] [inst_1 : DecidableE
q m]   [inst_2 : Fintype…
· 使用定理 `Matrix.BlockTriangular.comp`：∀ {α : Type u_1} {m : Type u_3} {n : Type u
_4} {R : Type v} {b : m → α} [inst : LT α] [inst_1 : Zero R]   {M : Matrix m m (
Matrix n n R)}, M…
· 使用定理 `Matrix.BlockTriangular.map`：∀ {α : Type u_1} {m : Type u_3} {R : Type v}
 {M : Matrix m m R} {b : m → α} [inst : LT α] {S : Type u_9} {F : Type u_10}   [
inst_1 : FunLike…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Algebra.Norm.Transitivity.auxMat_blockTriangular`：auxMat_blockTriangular
 : (auxMat M k).BlockTriangular (· != k)
· 使用定理 `Fintype.prod_Prop`：∀ {M : Type u_4} [inst : CommMonoid M] (f : Prop → M)
, ∏ p, f p = f True * f False
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Matrix.comp_toSquareBlock`：Matrix.comp_toSquareBlock {b : m -> α} (M : M
atrix m m (Matrix n n R)) (a : α) : letI equiv
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用引理 `Matrix.map_toSquareBlock`：Matrix.map_toSquareBlock (f : α -> β) {M : Mat
rix m m α} {ι} {b : m -> ι} {i : ι} : (M.map f).toSquareBlock b i = (M.toSquareB
lock b i).map …
· 使用引理 `Algebra.Norm.Transitivity.auxMat_toSquareBlock_eq`：auxMat_toSquareBlock_
eq : (auxMat M k).toSquareBlock (· != k) False = 1
· 使用引理 `Algebra.Norm.Transitivity.auxMat_toSquareBlock_ne`：auxMat_toSquareBlock_
ne : (auxMat M k).toSquareBlock (· != k) True = M k k • 1
· 使用定理 `Matrix.smul_one_eq_diagonal`：smul_one_eq_diagonal [DecidableEq m] (a : α
) : a • (1 : Matrix m m α) = diagonal fun _ => a
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用引理 `Matrix.comp_diagonal`：Matrix.comp_diagonal (d) : comp m m n n R (diagona
l d) = (blockDiagonal d).reindex (.prodComm ..) (.prodComm ..)
（共 49 条，此处仅展示前 30 条）
-/
theorem comp_det_mul_pow :
    ((M.map f).comp m m n n R).det * (f (M k k)).det ^ (Fintype.card m - 1) =
      (f (M k k)).det * (((mulAuxMatBlock).map f).comp _ _ n n R).det := by
  trans (((M * auxMat M k).map f).comp m m n n R).det
  · simp_rw [← f.mapMatrix_apply, ← compRingEquiv_apply, map_mul, det_mul, f.mapMatrix_apply,
      compRingEquiv_apply, ((auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· ≠ k)), det_reindex_self, map_toSquareBlock,
      auxMat_toSquareBlock_eq, auxMat_toSquareBlock_ne, smul_one_eq_diagonal, ← diagonal_one,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp
  · simp_rw [((mul_auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· = k)), det_reindex_self, map_toSquareBlock,
      mul_auxMat_toSquareBlock_eq, smul_one_eq_diagonal,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp

variable {M f} in
/-
**Algebra.Norm.Transitivity.det_det_aux** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Norm.
Transitivity`。
形式化陈述：det_det_aux (ih : forall M, (f (det M)).det = ((M.map f).comp {a // (a = k
) = False} _ n n R).det) : ((f M.det).det - ((M.map f).comp m m n n R).det) * (f
 (M k k)).det ^ (Fintype.card m - 1) = 0
参数：ih : forall M, (f (det M)).det = ((M.map f).comp {a // (a = k) = False} _ n n
 R).det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Algebra.Norm.Transitivity.comp_det_mul_pow`：comp_det_mul_pow : ((M.map f
).comp m m n n R).det * (f (M k k)).det ^ (Fintype.card m - 1) = (f (M k k)).det
 * (((mulAuxMatBlock).map f).com…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_pow`：det_pow (M : Matrix m m R) (n : Nat) : det (M ^ n) = det
 M ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `Algebra.Norm.Transitivity.det_mul_corner_pow`：det_mul_corner_pow : M.det
 * M k k ^ (Fintype.card m - 1) = M k k * (mulAuxMatBlock).det
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma det_det_aux
    (ih : ∀ M, (f (det M)).det = ((M.map f).comp {a // (a = k) = False} _ n n R).det) :
    ((f M.det).det - ((M.map f).comp m m n n R).det) *
      (f (M k k)).det ^ (Fintype.card m - 1) = 0 := by
  rw [sub_mul, comp_det_mul_pow, ← det_pow, ← map_pow, ← det_mul, ← map_mul,
    det_mul_corner_pow, map_mul, det_mul, ih, sub_self]

end Algebra.Norm.Transitivity

open Algebra.Norm.Transitivity

/-- The main result in Silvester's paper *Determinants of Block Matrices*: the determinant of
a block matrix with commuting, equal-sized, square blocks can be computed by taking determinants
twice in a row: first take the determinant over the commutative ring generated by the
blocks (`S` here), then take the determinant over the base ring. -/
/-
**Matrix.det_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.det_det [Fintype m] [Fintype n] (f : S ->+* Matrix n n R) : (f M.de
t).det = ((M.map f).comp m m n n R).det
参数：f : S ->+* Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.det_isEmpty`：det_isEmpty [IsEmpty n] {A : Matrix n n R} : det A =
 1
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `Algebra.Norm.Transitivity.polyToMatrix_cornerAddX`：polyToMatrix_cornerAd
dX : f.polyToMatrix (cornerAddX M k k k) = (-f (M k k)).charmatrix
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.charpoly.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4
} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),   M.charpoly
 = M.charm…
· 使用定理 `Polynomial.Monic.mem_nonZeroDivisors`：∀ {R : Type u} [inst : CommRing R]
 {p : Polynomial R}, p.Monic → p ∈ nonZeroDivisors (Polynomial R)
· 使用定理 `Matrix.charpoly_monic`：charpoly_monic (M : Matrix n n R) : M.charpoly.Mo
nic
· 使用引理 `Algebra.Norm.Transitivity.det_det_aux`：det_det_aux (ih : forall M, (f (d
et M)).det = ((M.map f).comp {a // (a = k) = False} _ n n R).det) : ((f M.det).d
et - ((M.map f).comp m m n …
· 使用引理 `Algebra.Norm.Transitivity.eval_zero_det_det`：eval_zero_det_det : eval 0 
(f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Algebra.Norm.Transitivity.eval_zero_comp_det`：eval_zero_comp_det : eval 
0 (comp m m n n R[X] <| (cornerAddX M k).map f.polyToMatrix).det = (comp m m n n
 R <| M.map f).det

--- 原说明 ---
The main result in Silvester's paper *Determinants of Block Matrices*: the deter
minant of
a block matrix with commuting, equal-sized, square blocks can be computed by tak
ing determinants
twice in a row: first take the determinant over the commutative ring generated b
y the
blocks (`S` here), then take the determinant over the base ring.
-/
theorem Matrix.det_det [Fintype m] [Fintype n] (f : S →+* Matrix n n R) :
    (f M.det).det = ((M.map f).comp m m n n R).det := by
  induction l : Fintype.card m generalizing R S m with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at l
    simp_rw [Matrix.det_isEmpty, map_one, det_one]
  | succ l ih =>
    have ⟨k⟩ := Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ l)
    let f' := f.polyToMatrix
    let M' := cornerAddX M k
    have : (f' M'.det).det = ((M'.map f').comp m m n n R[X]).det := by
      refine sub_eq_zero.mp <| mem_nonZeroDivisors_iff_right.mp
        (pow_mem ?_ _) _ (det_det_aux k fun M ↦ ih _ _ <| by
          grind [Fintype.card_subtype_compl, Fintype.card_unique])
      rw [polyToMatrix_cornerAddX, ← charpoly]
      exact (Matrix.charpoly_monic _).mem_nonZeroDivisors
    rw [← eval_zero_det_det, congr_arg (eval 0) this, eval_zero_comp_det]

variable [Algebra R S] [Module.Free R S]
/-
**LinearMap.det_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.det_restrictScalars [AddCommGroup A] [Module R A] [Module S A] [
IsScalarTower R S A] [Module.Free S A] {f : A ->ₗ[S] A} : (f.restrictScalars R).
det = Algebra.norm R f.det
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_eq_one_of_subsingleton`：det_eq_one_of_subsingleton [Subsin
gleton M] (f : M ->ₗ[R] M) : LinearMap.det (f : M ->ₗ[R] M) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `Algebra.norm_eq_matrix_det`：norm_eq_matrix_det [Fintype ι] [DecidableEq 
ι] (b : Basis ι R S) (s : S) : norm R s = Matrix.det (Algebra.leftMulMatrix b s)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Matrix.det_det`：Matrix.det_det [Fintype m] [Fintype n] (f : S ->+* Matri
x n n R) : (f M.det).det = ((M.map f).comp m m n n R).det
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `LinearMap.restrictScalars_toMatrix`：∀ {R : Type u_1} [inst : CommSemirin
g R] {m : Type u_3} [inst_1 : Fintype m] [inst_2 : DecidableEq m] {A : Type u_4}
   {M : Type u_5} {n : T…
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `LinearMap.det_eq_one_of_not_module_finite`：det_eq_one_of_not_module_fini
te (h : ¬Module.Finite R M) (f : M ->ₗ[R] M) : f.det = 1
· 使用引理 `Module.not_finite_of_infinite_basis`：not_finite_of_infinite_basis [Nontr
ivial R] {ι} [Infinite ι] (b : Basis ι R M) : ¬ Module.Finite R M
· 使用定理 `Algebra.norm_eq_one_of_not_module_finite`：norm_eq_one_of_not_module_fini
te (h : ¬Module.Finite R S) (x : S) : norm R x = 1
-/
theorem LinearMap.det_restrictScalars [AddCommGroup A] [Module R A] [Module S A]
    [IsScalarTower R S A] [Module.Free S A] {f : A →ₗ[S] A} :
    (f.restrictScalars R).det = Algebra.norm R f.det := by
  classical
  nontriviality R
  nontriviality A
  have := Module.nontrivial S A
  let ⟨ιS, bS⟩ := Module.Free.exists_basis (R := R) (M := S)
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := S) (M := A)
  have := bS.index_nonempty
  have := bA.index_nonempty
  cases fintypeOrInfinite ιS; swap
  · rw [Algebra.norm_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bS),
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  cases fintypeOrInfinite ιA; swap
  · rw [det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bA), map_one,
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  rw [Algebra.norm_eq_matrix_det bS, ← AlgHom.coe_toRingHom, ← det_toMatrix bA, det_det,
    ← det_toMatrix (bS.smulTower' bA), restrictScalars_toMatrix, RingHom.coe_coe]

/-- Let A/S/R be a tower of finite free tower of rings (with R and S commutative).
Then $\text{Norm}_{A/R} = \text{Norm}_{A/S} \circ \text{Norm}_{S/R}$. -/
/-
**Algebra.norm_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra S A] [IsScalarTower 
R S A] [Module.Free S A] {a : A} : norm R (norm S a) = norm R a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_restrictScalars`：LinearMap.det_restrictScalars [AddCommGro
up A] [Module R A] [Module S A] [IsScalarTower R S A] [Module.Free S A] {f : A -
>ₗ[S] A} : (f.restr…

--- 原说明 ---
Let A/S/R be a tower of finite free tower of rings (with R and S commutative).
Then $\text{Norm}_{A/R} = \text{Norm}_{A/S} \circ \text{Norm}_{S/R}$.
-/
theorem Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Free S A] {a : A} :
    norm R (norm S a) = norm R a := by
  rw [norm_apply S, norm_apply R a, ← LinearMap.det_restrictScalars]; rfl

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L]

open Module IntermediateField AdjoinSimple

namespace Algebra

/-
**Algebra.isIntegral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] {x : L} 
(hx : IsIntegral R x) : IsIntegral R (norm K x)
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.norm_norm`：Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra
 S A] [IsScalarTower R S A] [Module.Free S A] {a : A} : norm R (norm S a) = norm
 R a
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IntermediateField.AdjoinSimple.coe_gen`：∀ (F : Type u_1) [inst : Field F
] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   ↑(Intermed
iateField.AdjoinSimple.gen F…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
· 使用定理 `Algebra.norm_algebraMap_of_basis`：norm_algebraMap_of_basis [Fintype ι] (
b : Basis ι R S) (x : R) : norm R (algebraMap R S x) = x ^ Fintype.card ι
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots`：∀ {K : Type u_4} 
{L : Type u_5} {F : Type u_6} [inst : Field K] [inst_1 : Field L] [inst_2 : Fiel
d F]   [inst_3 : Algebra K L] [inst_4 : Alg…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `IsIntegral.multiset_prod`：IsIntegral.multiset_prod {s : Multiset A} (h :
 forall x in s, IsIntegral R x) : IsIntegral R s.prod
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 37 条，此处仅展示前 30 条）
-/
theorem isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] {x : L}
    (hx : IsIntegral R x) : IsIntegral R (norm K x) := by
  by_cases h : FiniteDimensional K L
  swap
  · simpa [norm_eq_one_of_not_module_finite h] using isIntegral_one
  let F := K⟮x⟯
  rw [← norm_norm (S := F), ← coe_gen K x, ← IntermediateField.algebraMap_apply,
    norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x), map_pow]
  apply IsIntegral.pow
  rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure F)).injective,
    norm_gen_eq_prod_roots _ (IsAlgClosed.splits _)]
  refine IsIntegral.multiset_prod (fun y hy ↦ ⟨minpoly R x, minpoly.monic hx, ?_⟩)
  suffices (aeval y) ((minpoly R x).map (algebraMap R K)) = 0 by simpa
  obtain ⟨P, hP⟩ := minpoly.dvd K x (show aeval x ((minpoly R x).map (algebraMap R K)) = 0 by simp)
  simp [hP, aeval_mul, (mem_aroots'.mp hy).2]
/-
**Algebra.norm_eq_norm_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_norm_adjoin (x : L) : norm K x = norm K (AdjoinSimple.gen K x) ^ f
inrank K⟮x⟯ L
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.AdjoinSimple.coe_gen`：∀ (F : Type u_1) [inst : Field F
] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   ↑(Intermed
iateField.AdjoinSimple.gen F…
· 使用定理 `Algebra.norm_norm`：Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra
 S A] [IsScalarTower R S A] [Module.Free S A] {a : A} : norm R (norm S a) = norm
 R a
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.algebraMap_apply`：∀ {K : Type u_1} {L : Type u_2} [ins
t : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K 
L)   (x : ↥S), (algebraM…
· 使用定理 `Algebra.norm_algebraMap_of_basis`：norm_algebraMap_of_basis [Fintype ι] (
b : Basis ι R S) (x : R) : norm R (algebraMap R S x) = x ^ Fintype.card ι
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.norm_eq_one_of_not_module_finite`：norm_eq_one_of_not_module_fini
te (h : ¬Module.Finite R S) (x : S) : norm R x = 1
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntermediateField.AdjoinSimple.isIntegral_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   IsI
ntegral F (IntermediateField.Adjoin…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem norm_eq_norm_adjoin (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L := by
  by_cases h : FiniteDimensional K L
  swap
  · rw [norm_eq_one_of_not_module_finite h]
    by_cases hx : IsIntegral K x
    · have h₁ : ¬ FiniteDimensional K⟮x⟯ L := fun H ↦ h <| by
        have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
        exact Finite.trans K⟮x⟯ L
      simp [finrank_of_not_finite h₁]
    · rw [norm_eq_one_of_not_module_finite]
      · simp
      · refine fun H ↦ hx ?_
        rw [← isIntegral_gen]
        exact IsIntegral.isIntegral (gen K x)
  let F := K⟮x⟯
  nth_rw 1 [← coe_gen K x]
  rw [← norm_norm (S := F), ← IntermediateField.algebraMap_apply,
    norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x), map_pow,
    finrank_eq_card_chooseBasisIndex]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]

variable {K} in
/-
**Algebra.norm_eq_prod_roots** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_prod_roots {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Spli
ts) : algebraMap K F (norm K x) = ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L
参数：hF : ((minpoly K x).map (algebraMap K F)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_norm_adjoin`：norm_eq_norm_adjoin (x : L) : norm K x = no
rm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots`：∀ {K : Type u_4} 
{L : Type u_5} {F : Type u_6} [inst : Field K] [inst_1 : Field L] [inst_2 : Fiel
d F]   [inst_3 : Algebra K L] [inst_4 : Alg…
-/
theorem norm_eq_prod_roots {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (norm K x) =
      ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L := by
  rw [norm_eq_norm_adjoin K x, map_pow, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

variable [FiniteDimensional K L]

/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ` of `L` into `E`. -/
/-
**Algebra.norm_eq_prod_embeddings** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_prod_embeddings [Algebra.IsSeparable K L] [IsAlgClosed E] (x : L) 
: algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] E, σ x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_norm_adjoin`：norm_eq_norm_adjoin (x : L) : norm K x = no
rm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `Algebra.norm_eq_prod_embeddings_gen`：norm_eq_prod_embeddings_gen [Algebr
a R F] (pb : PowerBasis R S) (hE : ((minpoly R pb.gen).map (algebraMap R F)).Spl
its) (hfx : IsSeparable R…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Algebra.prod_embeddings_eq_finrank_pow`：prod_embeddings_eq_finrank_pow [
Algebra L F] [IsScalarTower K L F] [IsAlgClosed E] [Algebra.IsSeparable K F] [Fi
niteDimensional K F] (pb : P…

--- 原说明 ---
For `L/K` a finite separable extension of fields and `E` an algebraically closed
 extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product 
of the images
of `x` over all the `K`-embeddings `σ` of `L` into `E`.
-/
theorem norm_eq_prod_embeddings [Algebra.IsSeparable K L] [IsAlgClosed E]
    (x : L) : algebraMap K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x, map_pow, ← adjoin.powerBasis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  · have := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _
/-
**Algebra.norm_eq_prod_automorphisms** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：norm_eq_prod_automorphisms [IsGalois K L] (x : L) : algebraMap K L (norm K
 x) = ∏ σ : Gal(L/K), σ x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.norm_eq_prod_embeddings`：norm_eq_prod_embeddings [Algebra.IsSepa
rable K L] [IsAlgClosed E] (x : L) : algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] 
E, σ x
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
-/
theorem norm_eq_prod_automorphisms [IsGalois K L] (x : L) :
    algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end Algebra

