/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Aristotle AI
-/
module

public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence and nonsingularity of matrices

In this file we formalize several theorems proved by Yi-Jia Tan in his paper [Tan2016]
*Free sets and free subsemimodules in a semimodule*. As consequences, we show that
commutative semirings satisfy the strong rank condition, and that the columns of a square matrix
are linearly independent if and only if the matrix is nonsingular (over a commutative ring,
a matrix is nonsingular if and only if its determinant is not a zero divisor).

## Main theorems

* `Matrix.Nonsingular.of_linearIndependent_col`: if the columns of a square matrix are linearly
  independent, then the matrix is nonsingular. Corollary 3.2(1) of [Tan2016].

* `Matrix.Nonsingular.linearIndependent_col`: if a matrix over a commutative semiring with
  cancellative addition is nonsingular, then its columns are linearly independent.
  Corollary 3.2(2) of [Tan2016].

* `CommSemiring.strongRankCondition_of_nontrivial`: a commutative semiring satisfies the strong
  rank condition.
-/

public section

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {A : Matrix n n R}

namespace Matrix

/-
**Matrix.isDetpBalanced_iff_sub_mul_det_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x`。
形式化陈述：isDetpBalanced_iff_sub_mul_det_eq_zero {R : Type*} [CommRing R] {A : Matri
x n n R} {a b : R} : A.IsDetpBalanced a b ↔ (a - b) * A.det = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isDetpBalanced_iff_sub_mul_det_eq_zero {R : Type*} [CommRing R] {A : Matrix n n R} {a b : R} :
    A.IsDetpBalanced a b ↔ (a - b) * A.det = 0 := by
  grind [IsDetpBalanced, det_eq_detp_sub_detp]
/-
**Matrix.nonsingular_iff_det_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Matr
ix`。
形式化陈述：nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R] {A : Matr
ix n n R} : A.Nonsingular ↔ A.det in nonZeroDivisors R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
lemma nonsingular_iff_det_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det ∈ nonZeroDivisors R := by
  simp_rw [Nonsingular, isDetpBalanced_iff_sub_mul_det_eq_zero, mem_nonZeroDivisors_iff_right]
  exact ⟨fun h x eq ↦ h x 0 (by simpa), fun h a b eq ↦ sub_eq_zero.mp <| h _ (by simpa)⟩
/-
**Matrix.nonsingular_iff_det_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonsingular_iff_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] {A : Mat
rix n n R} : A.Nonsingular ↔ A.det != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.nonsingular_iff_det_mem_nonZeroDivisors`：nonsingular_iff_det_mem_
nonZeroDivisors {R : Type*} [CommRing R] {A : Matrix n n R} : A.Nonsingular ↔ A.
det in nonZeroDivisors R
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonsingular_iff_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {A : Matrix n n R} : A.Nonsingular ↔ A.det ≠ 0 := by
  rw [nonsingular_iff_det_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_ne_zero]

/-- If the columns of a square matrix are linearly independent, then the matrix is nonsingular. -/
/-
**Matrix.Nonsingular.of_linearIndependent_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
Nonsingular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n]   {A : Matrix n n R}, LinearIndependent R A.col → A.
Nonsingular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsDetpBalanced.submatrix_of_card_le`：∀ {n : Type u_1} {m : Type u
_2} {R : Type u_3} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq
 m]   [inst_3 : DecidableEq n] […
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Matrix.detp_option_expand_row_none`：detp_option_expand_row_none (A : Mat
rix (Option n) (Option n) R) : A.detp s = A none none * (A.submatrix some some).
detp s + ∑ k : n, A none…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If the columns of a square matrix are linearly independent, then the matrix is n
onsingular.
-/
theorem Nonsingular.of_linearIndependent_col (ind : LinearIndependent R A.col) : A.Nonsingular := by
  intro a b bal
  let P (r : ℕ) : Prop := ∀ f g : Fin r → n, (A.submatrix f g).IsDetpBalanced a b
  suffices h : P 0 by simpa [IsDetpBalanced] using h Fin.elim0 Fin.elim0
  refine Nat.decreasingInduction' (n := Fintype.card n) (fun r _ _ ih f g ↦ ?_) (Nat.zero_le _) <|
    bal.submatrix_of_card_le (Fintype.card_fin _).ge
  by_cases hg : g.Surjective
  · exact bal.submatrix_of_card_le (Fintype.card_le_of_surjective g hg) f g
  obtain ⟨j₀, h₀⟩ := by simpa [Function.Surjective] using hg
  let D := A.submatrix f g
  let Aj (j : Fin r) := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n →₀ R := ∑ j, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  suffices h : v a b = v b a by simpa [IsDetpBalanced, v, h₀] using congr($h j₀)
  refine ind (funext fun i ↦ ?_)
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : ℤˣ) : Ai.detp s = ∑ j, (Aj j).detp (-s) * A.col (g j) i + D.detp s * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; aesop (add simp Function.update)
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp [v, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_add_add_comm, mul_add, this]
  simpa [this, IsDetpBalanced, ← submatrix_submatrix] using
    ih (Option.rec i f ∘ finSuccEquiv r) (Option.rec j₀ g ∘ finSuccEquiv r)
/-
**Matrix.Nonsingular.of_linearIndependent_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
Nonsingular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n]   {A : Matrix n n R}, LinearIndependent R A.row → A.
Nonsingular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.of_linearIndependent_col`：∀ {R : Type u_1} {n : Type 
u_3} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   {A 
: Matrix n n R}, LinearIndependen…
-/
theorem Nonsingular.of_linearIndependent_row (ind : LinearIndependent R A.row) : A.Nonsingular := by
  simpa using Nonsingular.of_linearIndependent_col (A := Aᵀ) ind
/-
**Matrix.Nonsingular.of_leftRegular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonsingula
r`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n]   {A : Matrix n n R}, IsLeftRegular A → A.Nonsingula
r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.of_linearIndependent_col`：∀ {R : Type u_1} {n : Type 
u_3} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   {A 
: Matrix n n R}, LinearIndependen…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_injective_iff`：Matrix.mulVec_injective_iff {M : Matrix m n
 R} : Function.Injective M.mulVec ↔ LinearIndependent R M.col
· 使用引理 `Matrix.isLeftRegular_iff_mulVec_injective`：isLeftRegular_iff_mulVec_inje
ctive [Fintype m] {A : Matrix m m α} : IsLeftRegular A ↔ Function.Injective A.mu
lVec
-/
theorem Nonsingular.of_leftRegular (h : IsLeftRegular A) : A.Nonsingular :=
  .of_linearIndependent_col (by rwa [← mulVec_injective_iff, ← isLeftRegular_iff_mulVec_injective])
/-
**Matrix.Nonsingular.of_rightRegular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonsingul
ar`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n]   {A : Matrix n n R}, IsRightRegular A → A.Nonsingul
ar
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.of_linearIndependent_row`：∀ {R : Type u_1} {n : Type 
u_3} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   {A 
: Matrix n n R}, LinearIndependen…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_injective_iff`：Matrix.vecMul_injective_iff {M : Matrix m n
 R} : Function.Injective M.vecMul ↔ LinearIndependent R M.row
· 使用引理 `Matrix.isRightRegular_iff_vecMul_injective`：isRightRegular_iff_vecMul_in
jective [Fintype m] {A : Matrix m m α} : IsRightRegular A ↔ Function.Injective A
.vecMul
-/
theorem Nonsingular.of_rightRegular (h : IsRightRegular A) : A.Nonsingular :=
  .of_linearIndependent_row (by rwa [← vecMul_injective_iff, ← isRightRegular_iff_vecMul_injective])

variable [IsCancelAdd R]

/-- If a matrix over a commutative semiring with cancellative addition is nonsingular, then its
columns are linearly independent. Generalizes `Matrix.linearIndependent_cols_of_det_ne_zero`. -/
/-
**Matrix.Nonsingular.linearIndependent_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Non
singular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : Matrix n n R}   [IsCancelAdd R], A.Nonsingular 
→ LinearIndependent R A.col
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.mulVec_injective_iff`：Matrix.mulVec_injective_iff {M : Matrix m n
 R} : Function.Injective M.mulVec ↔ LinearIndependent R M.col
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.adjp_mul_apply_eq`：adjp_mul_apply_eq : (adjp s A * A) i i = detp 
s A
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.adjp_mul_apply_ne`：adjp_mul_apply_ne (h : i != j) : (adjp 1 A * A
) i j = (adjp (-1) A * A) i j
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
· 使用定理 `Matrix.smul_mulVec`：smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarT
ower R α α] (b : R) (M : Matrix m n α) (v : n -> α) : (b • M) *ᵥ v = b • M *ᵥ v
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v

--- 原说明 ---
If a matrix over a commutative semiring with cancellative addition is nonsingula
r, then its
columns are linearly independent. Generalizes `Matrix.linearIndependent_cols_of_
det_ne_zero`.
-/
theorem Nonsingular.linearIndependent_col (hA : A.Nonsingular) : LinearIndependent R A.col :=
  mulVec_injective_iff.mp fun x y eq ↦ funext fun k ↦ hA _ _ <| show _ = _ by
    have h v : ((A.adjp 1 * A + A.detp (-1) • 1) *ᵥ v) k =
        ((A.adjp (-1) * A + A.detp 1 • 1) *ᵥ v) k := by
      congr 1; ext k i
      obtain (h | h) := eq_or_ne k i <;> simp [adjp_mul_apply_eq, add_comm, adjp_mul_apply_ne, h]
    simp [add_mulVec, smul_mulVec, ← mulVec_mulVec] at h; grind
/-
**Matrix.Nonsingular.linearIndependent_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Non
singular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : Matrix n n R}   [IsCancelAdd R], A.Nonsingular 
→ LinearIndependent R A.row
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.linearIndependent_col`：∀ {R : Type u_1} {n : Type u_3
} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Mat
rix n n R}   [IsCancelAdd R], …
· 使用定理 `Matrix.Nonsingular.transpose`：∀ {n : Type u_1} {R : Type u_3} [inst : Fi
ntype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R]   {A : Matrix n n R}
, A.Nonsingular → …
-/
theorem Nonsingular.linearIndependent_row (hA : A.Nonsingular) : LinearIndependent R A.row :=
  hA.transpose.linearIndependent_col
/-
**Matrix.linearIndependent_col_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_col_iff : LinearIndependent R A.col ↔ A.Nonsingular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.of_linearIndependent_col`：∀ {R : Type u_1} {n : Type 
u_3} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   {A 
: Matrix n n R}, LinearIndependen…
· 使用定理 `Matrix.Nonsingular.linearIndependent_col`：∀ {R : Type u_1} {n : Type u_3
} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Mat
rix n n R}   [IsCancelAdd R], …
-/
theorem linearIndependent_col_iff : LinearIndependent R A.col ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_col, (·.linearIndependent_col)⟩
/-
**Matrix.linearIndependent_row_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_row_iff : LinearIndependent R A.row ↔ A.Nonsingular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.Nonsingular.of_linearIndependent_row`：∀ {R : Type u_1} {n : Type 
u_3} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n]   {A 
: Matrix n n R}, LinearIndependen…
· 使用定理 `Matrix.Nonsingular.linearIndependent_row`：∀ {R : Type u_1} {n : Type u_3
} [inst : CommSemiring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Mat
rix n n R}   [IsCancelAdd R], …
-/
theorem linearIndependent_row_iff : LinearIndependent R A.row ↔ A.Nonsingular :=
  ⟨.of_linearIndependent_row, (·.linearIndependent_row)⟩
/-
**Matrix.isLeftRegular_iff_nonsingular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isLeftRegular_iff_nonsingular : IsLeftRegular A ↔ A.Nonsingular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.isLeftRegular_iff_mulVec_injective`：isLeftRegular_iff_mulVec_inje
ctive [Fintype m] {A : Matrix m m α} : IsLeftRegular A ↔ Function.Injective A.mu
lVec
· 使用定理 `Matrix.mulVec_injective_iff`：Matrix.mulVec_injective_iff {M : Matrix m n
 R} : Function.Injective M.mulVec ↔ LinearIndependent R M.col
· 使用定理 `Matrix.linearIndependent_col_iff`：linearIndependent_col_iff : LinearInde
pendent R A.col ↔ A.Nonsingular
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLeftRegular_iff_nonsingular : IsLeftRegular A ↔ A.Nonsingular := by
  rw [isLeftRegular_iff_mulVec_injective, mulVec_injective_iff, linearIndependent_col_iff]
/-
**Matrix.isRightRegular_iff_nonsingular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isRightRegular_iff_nonsingular : IsRightRegular A ↔ A.Nonsingular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.isRightRegular_iff_vecMul_injective`：isRightRegular_iff_vecMul_in
jective [Fintype m] {A : Matrix m m α} : IsRightRegular A ↔ Function.Injective A
.vecMul
· 使用定理 `Matrix.vecMul_injective_iff`：Matrix.vecMul_injective_iff {M : Matrix m n
 R} : Function.Injective M.vecMul ↔ LinearIndependent R M.row
· 使用定理 `Matrix.linearIndependent_row_iff`：linearIndependent_row_iff : LinearInde
pendent R A.row ↔ A.Nonsingular
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRightRegular_iff_nonsingular : IsRightRegular A ↔ A.Nonsingular := by
  rw [isRightRegular_iff_vecMul_injective, vecMul_injective_iff, linearIndependent_row_iff]
/-
**Matrix.Nonsingular.mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonsingular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : Matrix n n R}   [IsCancelAdd R] {B : Matrix n n
 R}, A.Nonsingular → B.Nonsingular → (A * B).Nonsingular
参数：A * B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isLeftRegular_iff_nonsingular`：isLeftRegular_iff_nonsingular : Is
LeftRegular A ↔ A.Nonsingular
· 使用定理 `IsLeftRegular.mul`：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLe
ftRegular b) : IsLeftRegular (a * b)
-/
lemma Nonsingular.mul {B : Matrix n n R} (hA : A.Nonsingular) (hB : B.Nonsingular) :
    (A * B).Nonsingular := by
  rw [← isLeftRegular_iff_nonsingular] at *
  exact hA.mul hB
/-
**Matrix.nonsingular_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：nonsingular_mul_iff {A B : Matrix n n R} : (A * B).Nonsingular ↔ A.Nonsing
ular ∧ B.Nonsingular where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isRightRegular_iff_nonsingular`：isRightRegular_iff_nonsingular : 
IsRightRegular A ↔ A.Nonsingular
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.isLeftRegular_iff_nonsingular`：isLeftRegular_iff_nonsingular : Is
LeftRegular A ↔ A.Nonsingular
· 使用定理 `IsLeftRegular.of_mul`：IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) 
: IsLeftRegular b
· 使用定理 `Matrix.Nonsingular.mul`：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemi
ring R] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n R}   [IsCa
ncelAdd R] {…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma nonsingular_mul_iff {A B : Matrix n n R} :
    (A * B).Nonsingular ↔ A.Nonsingular ∧ B.Nonsingular where
  mp h := ⟨isRightRegular_iff_nonsingular.mp <| .of_mul <| isRightRegular_iff_nonsingular.mpr h,
    isLeftRegular_iff_nonsingular.mp <| .of_mul <| isLeftRegular_iff_nonsingular.mpr h⟩
  mpr h := h.1.mul h.2
/-
**Matrix.Nonsingular.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Nonsingular`。
形式化陈述：∀ {R : Type u_1} {n : Type u_3} [inst : CommSemiring R] [inst_1 : Fintype 
n] [inst_2 : DecidableEq n] {A : Matrix n n R}   [IsCancelAdd R], A.Nonsingular 
→ ∀ (k : ℕ), (A ^ k).Nonsingular
参数：k : ℕ；A ^ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonsingular.pow (hA : A.Nonsingular) : ∀ k, (A ^ k).Nonsingular
  | 0 => by simp
  | k + 1 => by simp [pow_succ, (hA.pow k).mul hA]

omit [DecidableEq n] in
/-
**Matrix.isLeftRegular_iff_isRightRegular** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isLeftRegular_iff_isRightRegular : IsLeftRegular A ↔ IsRightRegular A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isLeftRegular_iff_nonsingular`：isLeftRegular_iff_nonsingular : Is
LeftRegular A ↔ A.Nonsingular
· 使用定理 `Matrix.isRightRegular_iff_nonsingular`：isRightRegular_iff_nonsingular : 
IsRightRegular A ↔ A.Nonsingular
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLeftRegular_iff_isRightRegular : IsLeftRegular A ↔ IsRightRegular A := by
  classical rw [isLeftRegular_iff_nonsingular, isRightRegular_iff_nonsingular]

omit [DecidableEq n] [Fintype n] in
/-- https://mathoverflow.net/questions/511862/transpose-symmetry-of-injectivity-of-linear-maps-over-semirings
asks whether this is still true without `IsCancelAdd R`. -/
/-
**Matrix.linearIndependent_col_iff_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linearIndependent_col_iff_row [Finite n] : LinearIndependent R A.col ↔ Lin
earIndependent R A.row
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.linearIndependent_col_iff`：linearIndependent_col_iff : LinearInde
pendent R A.col ↔ A.Nonsingular
· 使用定理 `Matrix.linearIndependent_row_iff`：linearIndependent_row_iff : LinearInde
pendent R A.row ↔ A.Nonsingular
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
https://mathoverflow.net/questions/511862/transpose-symmetry-of-injectivity-of-l
inear-maps-over-semirings
asks whether this is still true without `IsCancelAdd R`.
-/
theorem linearIndependent_col_iff_row [Finite n] :
    LinearIndependent R A.col ↔ LinearIndependent R A.row := by
  have := Fintype.ofFinite
  classical rw [linearIndependent_col_iff, linearIndependent_row_iff]

end Matrix

open Matrix

/-- A nontrivial commutative semiring satisfies the strong rank condition. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nontrivial commutative semiring satisfies the strong rank condition.
-/
instance (priority := 100) CommSemiring.strongRankCondition_of_nontrivial [Nontrivial R] :
    StrongRankCondition R where
  le_of_fin_injective {n m} f hf := by
    let g : (Fin m → R) →ₗ[R] (Fin n → R) := .pi fun i ↦ if h : i < m then .proj ⟨i, h⟩ else 0
    by_contra! hnm
    have hg : Function.Injective g := fun x y eq ↦ funext fun i ↦ by
      simpa [g] using congr($eq ⟨i, i.prop.trans hnm⟩)
    let A := (g ∘ₗ f).toMatrix'
    have hA : A.Nonsingular := .of_linearIndependent_col <| mulVec_injective_iff.mp <| by
      convert hg.comp hf; ext; simp [A, g]
    have : A.row ⟨m, hnm⟩ = 0 := by ext; simp [A, g]
    exact not_subsingleton R
      ⟨by simpa [Nonsingular, IsDetpBalanced, detp_eq_of_row_eq_zero _ this] using hA⟩
