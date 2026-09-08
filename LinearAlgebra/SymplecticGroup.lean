/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery, Seed Prover, Huanyu Zheng
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The Symplectic Group

This file defines the symplectic group and proves elementary properties.

## Main Definitions

* `Matrix.J`: the canonical `2n × 2n` skew-symmetric matrix
* `symplecticGroup`: the group of symplectic matrices

## Implementation Notes

* `SymplecticGroup.det_eq_one`: Symplectic matrices have determinant 1. The proof strategy
comes in two steps:

1. Consider a symplectic matrix `M` over a local ring, we can construct a matrix of the
form `fromBlocks 1 X 0 1` s.t. the upper-left block of `(fromBlocks 1 X 0 1) * M` is invertible.
From this we can calculate the determinant.

2. For a symplectic matrix `M` over general commutative ring `R`, we note that by step 1,
`M.det - 1 = 0` in any localization at a maximal ideal in `R`. Therefore `M.det = 1` in `R`.

Developing the proof in two steps is helpful, since the local ring hypothesis allows us to
construct the desired `X` in step 1 at the residue field level, and lift back to the ring while
keeping the upper-left block invertible.

## TODO
* For `n = 1` the symplectic group coincides with the special linear group.
-/

@[expose] public section


open Matrix

variable {l R : Type*}

namespace Matrix

variable (l) [DecidableEq l] (R) [CommRing R]

section JMatrixLemmas

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
/-
**Matrix.J** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：J : Matrix (l oplus l) (l oplus l) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix defining the canonical skew-symmetric bilinear form.
-/
def J : Matrix (l ⊕ l) (l ⊕ l) R :=
  Matrix.fromBlocks 0 (-1) 1 0

variable {R} in
@[simp]
/-
**Matrix.map_J** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_J {F S : Type*} [CommRing S] [FunLike F R S] [AddMonoidHomClass F R S]
 [OneHomClass F R S] (f : F) : (J l R).map f = J l S
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.fromBlocks_map`：fromBlocks_map (A : Matrix n l α) (B : Matrix n m
 α) (C : Matrix o l α) (D : Matrix o m α) (f : α -> β) : (fromBlocks A B C D).ma
p f = fromB…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.map_zero`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type 
w} [inst : Zero α] [inst_1 : Zero β] (f : α → β),   f 0 = 0 → Matrix.map 0 f = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.map_neg`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w
} [inst : Neg α] [inst_1 : Neg β] (f : α → β),   (∀ (a : α), f (-a) = -f a) → ∀ 
(M :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem map_J {F S : Type*} [CommRing S] [FunLike F R S]
    [AddMonoidHomClass F R S] [OneHomClass F R S] (f : F) :
    (J l R).map f = J l S := by
  simp [J, fromBlocks_map, Matrix.map_neg]

@[simp]
/-
**Matrix.J_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：J_transpose : (J l R)ᵀ = -J l R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.J.eq_1`：∀ (l : Type u_1) (R : Type u_2) [inst : DecidableEq l] [i
nst_1 : CommRing R],   Matrix.J l R = Matrix.fromBlocks 0 (-1) 1 0
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `Matrix.fromBlocks_smul`：fromBlocks_smul [SMul R α] (x : R) (A : Matrix n
 l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : x • fromBlocks 
A B C D = fr…
· 使用定理 `Matrix.transpose_zero`：transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.transpose_neg`：transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ =
 -Mᵀ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem J_transpose : (J l R)ᵀ = -J l R := by
  rw [J, fromBlocks_transpose, ← neg_one_smul R (fromBlocks _ _ _ _ : Matrix (l ⊕ l) (l ⊕ l) R),
    fromBlocks_smul, Matrix.transpose_zero, Matrix.transpose_one, transpose_neg]
  simp [fromBlocks]

variable [Fintype l]
/-
**Matrix.J_squared** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：J_squared : J l R * J l R = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.J.eq_1`：∀ (l : Type u_1) (R : Type u_2) [inst : DecidableEq l] [i
nst_1 : CommRing R],   Matrix.J l R = Matrix.fromBlocks 0 (-1) 1 0
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `Matrix.one_mul`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Non
AssocSemiring α] [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n
 α),…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.fromBlocks_neg`：fromBlocks_neg [Neg R] (A : Matrix n l R) (B : Ma
trix n m R) (C : Matrix o l R) (D : Matrix o m R) : -fromBlocks A B C D = fromBl
ocks (-A) (…
· 使用定理 `Matrix.fromBlocks_one`：fromBlocks_one : fromBlocks (1 : Matrix l l α) 0 
0 (1 : Matrix m m α) = 1
-/
theorem J_squared : J l R * J l R = -1 := by
  rw [J, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.neg_mul, zero_add, neg_zero, Matrix.one_mul, add_zero]
  rw [← neg_zero, ← Matrix.fromBlocks_neg, ← fromBlocks_one]
/-
**Matrix.J_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：J_inv : (J l R)⁻¹ = -J l R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_right_inv`：inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_neg`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `Matrix.J_squared`：J_squared : J l R * J l R = -1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem J_inv : (J l R)⁻¹ = -J l R := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, J_squared]
  exact neg_neg 1
/-
**Matrix.J_det_mul_J_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：J_det_mul_J_det : det (J l R) * det (J l R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.J_squared`：J_squared : J l R * J l R = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `Even.add_self`：∀ {α : Type u_2} [inst : Add α] (r : α), Even (r + r)
-/
theorem J_det_mul_J_det : det (J l R) * det (J l R) = 1 := by
  rw [← det_mul, J_squared, ← one_smul R (-1 : Matrix _ _ R), smul_neg, ← neg_smul, det_smul,
    Fintype.card_sum, det_one, mul_one]
  apply Even.neg_one_pow
  exact Even.add_self _
/-
**Matrix.isUnit_det_J** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isUnit_det_J : IsUnit (det (J l R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Matrix.J_det_mul_J_det`：J_det_mul_J_det : det (J l R) * det (J l R) = 1
-/
theorem isUnit_det_J : IsUnit (det (J l R)) :=
  isUnit_iff_exists_inv.mpr ⟨det (J l R), J_det_mul_J_det _ _⟩

end JMatrixLemmas

variable [Fintype l]

/-- The group of symplectic matrices over a ring `R`. -/
@[wikidata Q936434]
/-
**Matrix.symplecticGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：symplecticGroup : Submonoid (Matrix (l oplus l) (l oplus l) R) where carri
er
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of symplectic matrices over a ring `R`.
-/
def symplecticGroup : Submonoid (Matrix (l ⊕ l) (l ⊕ l) R) where
  carrier := { A | A * J l R * Aᵀ = J l R }
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, transpose_mul] at *
    rw [← Matrix.mul_assoc, a.mul_assoc, a.mul_assoc, hb]
    exact ha
  one_mem' := by simp

end Matrix

namespace SymplecticGroup

variable [DecidableEq l] [Fintype l] [CommRing R]

open Matrix

/-
**SymplecticGroup.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：mem_iff {A : Matrix (l oplus l) (l oplus l) R} : A in symplecticGroup l R 
↔ A * J l R * Aᵀ = J l R
参数：l oplus l；l oplus l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iff {A : Matrix (l ⊕ l) (l ⊕ l) R} :
    A ∈ symplecticGroup l R ↔ A * J l R * Aᵀ = J l R := by simp [symplecticGroup]
/-
**SymplecticGroup.coeMatrix** 是 Mathlib 中的一个实例，位于命名空间 `SymplecticGroup`。
形式化陈述：coeMatrix : Coe (symplecticGroup l R) (Matrix (l oplus l) (l oplus l) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeMatrix : Coe (symplecticGroup l R) (Matrix (l ⊕ l) (l ⊕ l) R) :=
  ⟨Subtype.val⟩

section SymplecticJ

variable (l) (R)

/-
**SymplecticGroup.J_mem** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：J_mem : J l R in symplecticGroup l R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
· 使用定理 `Matrix.J.eq_1`：∀ (l : Type u_1) (R : Type u_2) [inst : DecidableEq l] [i
nst_1 : CommRing R],   Matrix.J l R = Matrix.fromBlocks 0 (-1) 1 0
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem J_mem : J l R ∈ symplecticGroup l R := by
  rw [mem_iff, J, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_multiply]
  simp

/-- The canonical skew-symmetric matrix as an element in the symplectic group. -/
/-
**SymplecticGroup.symJ** 是 Mathlib 中的一个定义，位于命名空间 `SymplecticGroup`。
形式化陈述：symJ : symplecticGroup l R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SymplecticGroup.J_mem`：J_mem : J l R in symplecticGroup l R

--- 原说明 ---
The canonical skew-symmetric matrix as an element in the symplectic group.
-/
def symJ : symplecticGroup l R :=
  ⟨J l R, J_mem l R⟩

variable {l} {R}

@[simp]
/-
**SymplecticGroup.coe_J** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：coe_J : ↑(symJ l R) = J l R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_J : ↑(symJ l R) = J l R := rfl

end SymplecticJ

variable {A : Matrix (l ⊕ l) (l ⊕ l) R}

/-
**SymplecticGroup.neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：neg_mem (h : A in symplecticGroup l R) : -A in symplecticGroup l R
参数：h : A in symplecticGroup l R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mem (h : A ∈ symplecticGroup l R) : -A ∈ symplecticGroup l R := by
  rw [mem_iff] at h ⊢
  simp [h]
/-
**SymplecticGroup.symplectic_det** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：symplectic_det (hA : A in symplecticGroup l R) : IsUnit det A
参数：hA : A in symplecticGroup l R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsUnit.mul_left_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, 
IsUnit a → a * b = a * c → b = c
· 使用定理 `Matrix.isUnit_det_J`：isUnit_det_J : IsUnit (det (J l R))
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
-/
theorem symplectic_det (hA : A ∈ symplecticGroup l R) : IsUnit <| det A := by
  rw [isUnit_iff_exists_inv]
  use A.det
  refine (isUnit_det_J l R).mul_left_cancel ?_
  rw [mul_one]
  rw [mem_iff] at hA
  apply_fun det at hA
  simp only [det_mul, det_transpose] at hA
  rw [mul_comm A.det, mul_assoc] at hA
  exact hA
/-
**SymplecticGroup.map_mem** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：map_mem {F S : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S] (h
A : A in symplecticGroup l R) (f : F) : A.map f in symplecticGroup l S
参数：hA : A in symplecticGroup l R；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.map_J`：map_J {F S : Type*} [CommRing S] [FunLike F R S] [AddMonoi
dHomClass F R S] [OneHomClass F R S] (f : F) : (J l R).map f = J l S
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mem {F S : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (hA : A ∈ symplecticGroup l R) (f : F) : A.map f ∈ symplecticGroup l S := by
  simp_rw [mem_iff, ← transpose_map, ← map_J _ f, ← Matrix.map_mul, mem_iff.mp hA]
/-
**SymplecticGroup.transpose_mem** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：transpose_mem (hA : A in symplecticGroup l R) : Aᵀ in symplecticGroup l R
参数：hA : A in symplecticGroup l R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `SymplecticGroup.symplectic_det`：symplectic_det (hA : A in symplecticGrou
p l R) : IsUnit det A
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.J_inv`：J_inv : (J l R)⁻¹ = -J l R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.mul_inv_rev`：mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ *
 A⁻¹
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `Matrix.mul_nonsing_inv_cancel_left`：mul_nonsing_inv_cancel_left (B : Mat
rix n m α) (h : IsUnit A.det) : A * (A⁻¹ * B) = B
· 使用定理 `Matrix.nonsing_inv_mul_cancel_right`：nonsing_inv_mul_cancel_right (B : M
atrix m n α) (h : IsUnit A.det) : B * A⁻¹ * A = B
-/
theorem transpose_mem (hA : A ∈ symplecticGroup l R) : Aᵀ ∈ symplecticGroup l R := by
  rw [mem_iff] at hA ⊢
  rw [transpose_transpose]
  have huA := symplectic_det hA
  have huAT : IsUnit Aᵀ.det := by
    rw [Matrix.det_transpose]
    exact huA
  calc
    Aᵀ * J l R * A = (-Aᵀ) * (J l R)⁻¹ * A := by
      rw [J_inv]
      simp
    _ = (-Aᵀ) * (A * J l R * Aᵀ)⁻¹ * A := by rw [hA]
    _ = -(Aᵀ * (Aᵀ⁻¹ * (J l R)⁻¹)) * A⁻¹ * A := by
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.neg_mul]
    _ = -(J l R)⁻¹ := by
      rw [mul_nonsing_inv_cancel_left _ _ huAT, nonsing_inv_mul_cancel_right _ _ huA]
    _ = J l R := by simp [J_inv]

@[simp]
/-
**SymplecticGroup.transpose_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：transpose_mem_iff : Aᵀ in symplecticGroup l R ↔ A in symplecticGroup l R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `SymplecticGroup.transpose_mem`：transpose_mem (hA : A in symplecticGroup 
l R) : Aᵀ in symplecticGroup l R
-/
theorem transpose_mem_iff : Aᵀ ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun hA => by simpa using transpose_mem hA, transpose_mem⟩
/-
**SymplecticGroup.mem_iff'** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：mem_iff' : A in symplecticGroup l R ↔ Aᵀ * J l R * A = J l R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SymplecticGroup.transpose_mem_iff`：transpose_mem_iff : Aᵀ in symplecticG
roup l R ↔ A in symplecticGroup l R
· 使用定理 `SymplecticGroup.mem_iff`：mem_iff {A : Matrix (l oplus l) (l oplus l) R} 
: A in symplecticGroup l R ↔ A * J l R * Aᵀ = J l R
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff' : A ∈ symplecticGroup l R ↔ Aᵀ * J l R * A = J l R := by
  rw [← transpose_mem_iff, mem_iff, transpose_transpose]
/-
**SymplecticGroup.hasInv** 是 Mathlib 中的一个实例，位于命名空间 `SymplecticGroup`。
形式化陈述：hasInv : Inv (symplecticGroup l R) where inv A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasInv : Inv (symplecticGroup l R) where
  inv A := ⟨(-J l R) * (A : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R,
      mul_mem (mul_mem (neg_mem <| J_mem _ _) <| transpose_mem A.2) <| J_mem _ _⟩
/-
**SymplecticGroup.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A
)ᵀ * J l R
参数：A : symplecticGroup l R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Matrix _ _ _) = (-J l R) * (↑A)ᵀ * J l R := rfl
/-
**SymplecticGroup.inv_left_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：inv_left_mul_aux (hA : A in symplecticGroup l R) : -(J l R * Aᵀ * J l R * 
A) = 1
参数：hA : A in symplecticGroup l R。
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
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SymplecticGroup.mem_iff'`：mem_iff' : A in symplecticGroup l R ↔ Aᵀ * J l
 R * A = J l R
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.J_squared`：J_squared : J l R * J l R = -1
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
-/
theorem inv_left_mul_aux (hA : A ∈ symplecticGroup l R) : -(J l R * Aᵀ * J l R * A) = 1 :=
  calc
    -(J l R * Aᵀ * J l R * A) = (-J l R) * (Aᵀ * J l R * A) := by
      simp only [Matrix.mul_assoc, Matrix.neg_mul]
    _ = (-J l R) * J l R := by
      rw [mem_iff'] at hA
      rw [hA]
    _ = (-1 : R) • (J l R * J l R) := by simp only [Matrix.neg_mul, neg_smul, one_smul]
    _ = (-1 : R) • (-1 : Matrix _ _ _) := by rw [J_squared]
    _ = 1 := by simp only [neg_smul_neg, one_smul]
/-
**SymplecticGroup.coe_inv'** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (l oplus l) (l oplus l
) R) = (↑A)⁻¹
参数：A : symplecticGroup l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SymplecticGroup.coe_inv`：coe_inv (A : symplecticGroup l R) : (↑A⁻¹ : Mat
rix _ _ _) = (-J l R) * (↑A)ᵀ * J l R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `SymplecticGroup.inv_left_mul_aux`：inv_left_mul_aux (hA : A in symplectic
Group l R) : -(J l R * Aᵀ * J l R * A) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_inv' (A : symplecticGroup l R) : (↑A⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R) = (↑A)⁻¹ := by
  refine (coe_inv A).trans (inv_eq_left_inv ?_).symm
  simp [inv_left_mul_aux]
/-
**SymplecticGroup.inv_eq_symplectic_inv** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGro
up`。
形式化陈述：inv_eq_symplectic_inv (A : Matrix (l oplus l) (l oplus l) R) (hA : A in sy
mplecticGroup l R) : A⁻¹ = (-J l R) * Aᵀ * J l R
参数：A : Matrix (l oplus l) (l oplus l) R；hA : A in symplecticGroup l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.inv_eq_left_inv`：inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.neg_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocRing α] [inst_1 : Fintype n]   (M : Matrix m n α) (
N : …
· 使用定理 `SymplecticGroup.inv_left_mul_aux`：inv_left_mul_aux (hA : A in symplectic
Group l R) : -(J l R * Aᵀ * J l R * A) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_eq_symplectic_inv (A : Matrix (l ⊕ l) (l ⊕ l) R) (hA : A ∈ symplecticGroup l R) :
    A⁻¹ = (-J l R) * Aᵀ * J l R :=
  inv_eq_left_inv (by simp only [Matrix.neg_mul, inv_left_mul_aux hA])
/-
**SymplecticGroup.** 是 Mathlib 中的一个实例，位于命名空间 `SymplecticGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (symplecticGroup l R) :=
  { SymplecticGroup.hasInv, Submonoid.toMonoid _ with
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Matrix.neg_mul, coe_inv]
      exact inv_left_mul_aux A.2 }

section Determinant

variable {A B C D : Matrix l l R}

/-
**SymplecticGroup.fromBlocks_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`
。
形式化陈述：fromBlocks_mem_iff : fromBlocks A B C D in symplecticGroup l R ↔ Aᵀ * C = 
Cᵀ * A ∧ Bᵀ * D = Dᵀ * B ∧ Aᵀ * D - Cᵀ * B = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Matrix.fromBlocks_transpose`：fromBlocks_transpose (A : Matrix n l α) (B 
: Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBlocks A B C D)ᵀ = 
fromBlocks Aᵀ Cᵀ …
· 使用定理 `Matrix.fromBlocks_multiply`：fromBlocks_multiply [Fintype l] [Fintype m] 
[NonUnitalNonAssocSemiring α] (A : Matrix n l α) (B : Matrix n m α) (C : Matrix 
o l α) (D : Matr…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `SymplecticGroup.transpose_mem`：transpose_mem (hA : A in symplecticGroup 
l R) : Aᵀ in symplecticGroup l R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.fromBlocks_inj`：fromBlocks_inj {A : Matrix n l α} {B : Matrix n m
 α} {C : Matrix o l α} {D : Matrix o m α} {A' : Matrix n l α} {B' : Matrix n m α
} {C' : Mat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SymplecticGroup.mem_iff'`：mem_iff' : A in symplecticGroup l R ↔ Aᵀ * J l
 R * A = J l R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.transpose_sub`：transpose_sub [Sub α] (M : Matrix m n α) (N : Matr
ix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem fromBlocks_mem_iff :
    fromBlocks A B C D ∈ symplecticGroup l R ↔
      Aᵀ * C = Cᵀ * A ∧
      Bᵀ * D = Dᵀ * B ∧
      Aᵀ * D - Cᵀ * B = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_iff'.2 ?_⟩
  · have h_final : fromBlocks (Cᵀ * A - Aᵀ * C) (Cᵀ * B - Aᵀ * D)
        (Dᵀ * A - Bᵀ * C) (Dᵀ * B - Bᵀ * D) = J l R := by
      simpa [mem_iff, fromBlocks_transpose, J, fromBlocks_multiply,
        sub_eq_add_neg] using transpose_mem h
    obtain ⟨h_eq1, h_eq2, _, h_eq3⟩ := fromBlocks_inj.1 h_final
    exact ⟨(sub_eq_zero.1 h_eq1).symm, (sub_eq_zero.1 h_eq3).symm, by grind⟩
  · simp only [fromBlocks_transpose, J, fromBlocks_multiply, mul_zero, mul_one, zero_add, mul_neg,
      add_zero, neg_mul, ← sub_eq_add_neg, fromBlocks_inj, sub_eq_zero]
    exact ⟨h.1.symm, by grind, by simpa using congr(transpose $(h.2.2)), h.2.1.symm⟩

/-- The determinant of a symplectic matrix is 1 if its upper-left block is invertible. -/
/-
**SymplecticGroup.det_one_if_fromBlocks_invertible** 是 Mathlib 中的一个引理，位于命名空间 `Sy
mplecticGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The determinant of a symplectic matrix is 1 if its upper-left block is invertibl
e.
-/
private lemma det_one_if_fromBlocks_invertible [Invertible A]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    (fromBlocks A B C D).det = 1 := by
  have h_block := fromBlocks_mem_iff.1 hA
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, ← A.det_transpose, ← det_mul,
    mul_sub, ← mul_assoc, ← mul_assoc, h_block.1, mul_assoc Cᵀ,
    mul_inv_of_invertible, mul_one, h_block.2.2, det_one]

/-- Given square matrices `A` and `C` over a field, if the only vector annihilated by both of
them is 0, and `Aᵀ * C = Cᵀ * A`, then one can construct a symmetric matrix `X` such that
`A + X * C` is invertible.

This lemma, together with the one after, is used to turn the upper-left block into invertible
matrix in the main proof, so that we can use the previous lemma to calculate the determinant. -/
/-
**SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot** 是 
Mathlib 中的一个引理，位于命名空间 `SymplecticGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given square matrices `A` and `C` over a field, if the only vector annihilated b
y both of
them is 0, and `Aᵀ * C = Cᵀ * A`, then one can construct a symmetric matrix `X` 
such that
`A + X * C` is invertible.

This lemma, together with the one after, is used to turn the upper-left block in
to invertible
matrix in the main proof, so that we can use the previous lemma to calculate the
 determinant.
-/
private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU

/-- For any symplectic matrix `fromBlocks A B C D` over a local ring `R`, we can construct
a symmetric `X` s.t. `A + X * C` is invertible.

Introducing local ring hypothesis enables us to transport the construction of `X`
(from the previous lemma, which works only over fields) back to `R` while keeping
`A + X * C` invertible. -/
/-
**SymplecticGroup.exists_symmetric_X_isUnit_det_add_mul_of_symplectic** 是 Mathli
b 中的一个引理，位于命名空间 `SymplecticGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any symplectic matrix `fromBlocks A B C D` over a local ring `R`, we can con
struct
a symmetric `X` s.t. `A + X * C` is invertible.

Introducing local ring hypothesis enables us to transport the construction of `X
`
(from the previous lemma, which works only over fields) back to `R` while keepin
g
`A + X * C` invertible.
-/
private lemma exists_symmetric_X_isUnit_det_add_mul_of_symplectic [IsLocalRing R]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have hker (x : l → k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
    exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker <| by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul, (fromBlocks_mem_iff.1 hA).1, map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : ∃ X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j ↦ hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply _ X, hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

/-- Symplectic matrices over a local ring have determinant 1. -/
/-
**SymplecticGroup.det_eq_one_of_isLocalRing** 是 Mathlib 中的一个引理，位于命名空间 `Symplecti
cGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Symplectic matrices over a local ring have determinant 1.
-/
private lemma det_eq_one_of_isLocalRing [IsLocalRing R] {M : Matrix (l ⊕ l) (l ⊕ l) R}
    (hM : M ∈ symplecticGroup l R) : M.det = 1 := by
  set A := M.toBlocks₁₁; set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁; set D := M.toBlocks₂₂
  obtain ⟨X, hX_symm, hA_isUnit⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic <|
    M.fromBlocks_toBlocks ▸ hM
  -- `fromBlocks 1 X 0 1` turns the upper-left block of `M` into an invertible matrix, here `X`
  -- is obtained via previous result.
  have Lx_mul : (fromBlocks 1 X 0 1) * M = fromBlocks (A + X * C) (B + X * D) C D := by
    rw [← M.fromBlocks_toBlocks, fromBlocks_multiply]
    simp only [one_mul, zero_mul, zero_add]; rfl
  have h_fromBlocks_in : fromBlocks (A + X * C) (B + X * D) C D ∈ symplecticGroup l R := by
    rw [← Lx_mul]
    refine (symplecticGroup l R).mul_mem ?_ hM
    simp [mem_iff, fromBlocks_transpose, hX_symm.eq, J, fromBlocks_multiply]
  have _ : Invertible (A + X * C) := (A + X * C).invertibleOfIsUnitDet hA_isUnit
  -- And we know that a symmetric matrix with invertible upper-left block has determinant 1.
  have h_main : ((fromBlocks 1 X 0 1) * M).det = 1 := by
    rw [Lx_mul, det_one_if_fromBlocks_invertible h_fromBlocks_in]
  rwa [det_mul, det_fromBlocks_zero₂₁, det_one, one_mul, one_mul] at h_main

/-- Symplectic matrices have determinant 1.

The proof strategy comes in two steps:
1. Consider a symplectic matrix `M` over a local ring, we can construct a matrix of the
form `fromBlocks 1 X 0 1` s.t. the upper-left block of `(fromBlocks 1 X 0 1) * M` is invertible.
From this we can calculate the determinant.

2. For a symplectic matrix `M` over general commutative ring `R`, we note that by step 1,
`M.det - 1 = 0` in any localization at a maximal ideal in `R`. Therefore `M.det = 1` in `R`. -/
/-
**SymplecticGroup.det_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SymplecticGroup`。
形式化陈述：det_eq_one {M : Matrix (l oplus l) (l oplus l) R} (hM : M in symplecticGro
up l R) : M.det = 1
参数：l oplus l；l oplus l；hM : M in symplecticGroup l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_zero_of_localization`：eq_zero_of_localization (r : R) (h : forall (J 
: Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) : r =
 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `_private.Mathlib.LinearAlgebra.SymplecticGroup.0.SymplecticGroup.det_eq_
one_of_isLocalRing`：∀ {l : Type u_1} {R : Type u_2} [inst : DecidableEq l] [inst
_1 : Fintype l] [inst_2 : CommRing R] [IsLocalRing R]   {M : Matrix (l ⊕ l) (l ⊕
…
· 使用定理 `SymplecticGroup.map_mem`：map_mem {F S : Type*} [CommRing S] [FunLike F R
 S] [RingHomClass F R S] (hA : A in symplecticGroup l R) (f : F) : A.map f in sy
mplecticGroup…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
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
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Symplectic matrices have determinant 1.

The proof strategy comes in two steps:
1. Consider a symplectic matrix `M` over a local ring, we can construct a matrix
 of the
form `fromBlocks 1 X 0 1` s.t. the upper-left block of `(fromBlocks 1 X 0 1) * M
` is invertible.
From this we can calculate the determinant.

2. For a symplectic matrix `M` over general commutative ring `R`, we note that b
y step 1,
`M.det - 1 = 0` in any localization at a maximal ideal in `R`. Therefore `M.det 
= 1` in `R`.
-/
theorem det_eq_one {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) :
    M.det = 1 := by
  refine sub_eq_zero.1 <| eq_zero_of_localization _ fun _ _ ↦ ?_
  simp [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_one_of_isLocalRing <| map_mem hM _]

end Determinant

end SymplecticGroup

