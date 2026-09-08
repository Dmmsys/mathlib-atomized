/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Tactic.NoncommRing

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

When a module carries a bilinear form, the Lie algebra of endomorphisms of the module contains a
distinguished Lie subalgebra: the skew-adjoint endomorphisms. Such subalgebras are important
because they provide a simple, explicit construction of the so-called classical Lie algebras.

This file defines the Lie subalgebra of skew-adjoint endomorphisms cut out by a bilinear form on
a module and proves some basic related results. It also provides the corresponding definitions and
results for the Lie algebra of square matrices.

## Main definitions

  * `skewAdjointLieSubalgebra`
  * `skewAdjointLieSubalgebraEquiv`
  * `skewAdjointMatricesLieSubalgebra`
  * `skewAdjointMatricesLieSubalgebraEquiv`

## Tags

lie algebra, skew-adjoint, bilinear form
-/

@[expose] public section


universe u v w w₁

section SkewAdjointEndomorphisms

open LinearMap (BilinForm)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : BilinForm R M)

/-
**LinearMap.BilinForm.isSkewAdjoint_bracket** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M} (hf : f i
n B.skewAdjointSubmodule) (hg : g in B.skewAdjointSubmodule) : ⁅f, g⁆ in B.skewA
djointSubmodule
参数：hf : f in B.skewAdjointSubmodule；hg : g in B.skewAdjointSubmodule。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_skewAdjointSubmodule`：mem_skewAdjointSubmodule (f : Module
.End R M) : f in B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `LinearMap.IsAdjointPair.comp`：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type
 u_6} {M₂ : Type u_7} {M₃ : Type u_8} [inst : CommSemiring R]   [inst_1 : AddCom
mMonoid M] [inst_2…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `LinearMap.IsAdjointPair.sub`：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type 
u_6} {M₂ : Type u_7} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M]…
-/
theorem LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M}
    (hf : f ∈ B.skewAdjointSubmodule) (hg : g ∈ B.skewAdjointSubmodule) :
    ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  exact hfg.sub hgf

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
/-
**skewAdjointLieSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.isSkewAdjoint_bracket`：LinearMap.BilinForm.isSkewAdj
oint_bracket {f g : Module.End R M} (hf : f in B.skewAdjointSubmodule) (hg : g i
n B.skewAdjointSubmodule) : ⁅f,…

--- 原说明 ---
Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomor
phisms form a
Lie subalgebra of the Lie algebra of endomorphisms.
-/
def skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M) :=
  { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
/-
**skewAdjointLieSubalgebraEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointLieSubalgebraEquiv : skewAdjointLieSubalgebra (B.compl₁₂ (e : N
 ->ₗ[R] M) e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of modules with bilinear forms gives equivalence of Lie algebras 
of skew-adjoint
endomorphisms.
-/
def skewAdjointLieSubalgebraEquiv :
    skewAdjointLieSubalgebra (B.compl₁₂ (e : N →ₗ[R] M) e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm

@[simp]
/-
**skewAdjointLieSubalgebraEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjointLieSubalgebraEquiv_apply (f : skewAdjointLieSubalgebra (B.compl
₁₂ (Qₗ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem skewAdjointLieSubalgebraEquiv_apply
    (f : skewAdjointLieSubalgebra (B.compl₁₂ (Qₗ := N) (Qₗ' := N) ↑e ↑e)) :
    ↑(skewAdjointLieSubalgebraEquiv B e f) = e.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

@[simp]
/-
**skewAdjointLieSubalgebraEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) 
: ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f
参数：f : skewAdjointLieSubalgebra B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) :
    ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

end SkewAdjointEndomorphisms

section SkewAdjointMatrices

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [Fintype n]
variable (J : Matrix n n R)

/-
**Matrix.lie_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆
参数：A B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transpose_sub`：transpose_sub [Sub α] (M : Matrix m n α) (N : Matr
ix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
  show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp

variable [DecidableEq n]
/-
**Matrix.isSkewAdjoint_bracket** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A in skewAdjointMa
tricesSubmodule J) (hB : B in skewAdjointMatricesSubmodule J) : ⁅A, B⁆ in skewAd
jointMatricesSubmodule J
参数：hA : A in skewAdjointMatricesSubmodule J；hB : B in skewAdjointMatricesSubmodu
le J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.lie_transpose`：Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆
ᵀ = ⁅Bᵀ, Aᵀ⁆
· 使用定理 `LieRing.of_associative_ring_bracket`：of_associative_ring_bracket (x y : 
A) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `_private.Mathlib.Algebra.Lie.SkewAdjoint.0.Matrix.isSkewAdjoint_bracket.
_abel_1_2`：∀ {R : Type u_1} {n : Type u_2} [inst : CommRing R] [inst_1 : Fintype
 n] (J : Matrix n n R) [inst_2 : DecidableEq n]   {A B : Matrix n n R},…
-/
theorem Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A ∈ skewAdjointMatricesSubmodule J)
    (hB : B ∈ skewAdjointMatricesSubmodule J) : ⁅A, B⁆ ∈ skewAdjointMatricesSubmodule J := by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose, LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket, sub_mul, mul_assoc, mul_assoc, hA, hB, ← mul_assoc,
    ← mul_assoc, hA, hB]
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
/-
**skewAdjointMatricesLieSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointMatricesLieSubalgebra : LieSubalgebra R (Matrix n n R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isSkewAdjoint_bracket`：Matrix.isSkewAdjoint_bracket {A B : Matrix
 n n R} (hA : A in skewAdjointMatricesSubmodule J) (hB : B in skewAdjointMatrice
sSubmodule J) : ⁅A…

--- 原说明 ---
The Lie subalgebra of skew-adjoint square matrices corresponding to a square mat
rix `J`.
-/
def skewAdjointMatricesLieSubalgebra : LieSubalgebra R (Matrix n n R) :=
  { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }

@[simp]
/-
**mem_skewAdjointMatricesLieSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) : A in skewAdjoint
MatricesLieSubalgebra J ↔ A in skewAdjointMatricesSubmodule J
参数：A : Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra J ↔ A ∈ skewAdjointMatricesSubmodule J :=
  Iff.rfl

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
/-
**skewAdjointMatricesLieSubalgebraEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointMatricesLieSubalgebraEquiv (P : Matrix n n R) (h : Invertible P
) : skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (P
ᵀ * J * P)
参数：P : Matrix n n R；h : Invertible P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invertible matrix `P` gives a Lie algebra equivalence between those endomorph
isms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP
`.
-/
def skewAdjointMatricesLieSubalgebraEquiv (P : Matrix n n R) (h : Invertible P) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (Pᵀ * J * P) :=
  LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm <| by
    ext A
    suffices P.lieConj h A ∈ skewAdjointMatricesSubmodule J ↔
        A ∈ skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      exact this
    simp [Matrix.IsSkewAdjoint, J.isAdjointPair_equiv _ _ P (isUnit_of_invertible P)]
/-
**skewAdjointMatricesLieSubalgebraEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invert
ible P) (A : skewAdjointMatricesLieSubalgebra J) : ↑(skewAdjointMatricesLieSubal
gebraEquiv J P h A) = P⁻¹ * A * P
参数：P : Matrix n n R；h : Invertible P；A : skewAdjointMatricesLieSubalgebra J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.lieConj_symm_apply`：lieConj_symm_apply (P A : Matrix n n R) (h : 
Invertible P) : (P.lieConj h).symm A = P⁻¹ * A * P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invertible P)
    (A : skewAdjointMatricesLieSubalgebra J) :
    ↑(skewAdjointMatricesLieSubalgebraEquiv J P h A) = P⁻¹ * A * P := by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
/-
**skewAdjointMatricesLieSubalgebraEquivTranspose** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointMatricesLieSubalgebraEquivTranspose {m : Type w} [DecidableEq m
] [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : forall A, (e A)ᵀ = e Aᵀ
) : skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (e
 J)
参数：e : Matrix n n R ≃ₐ[R] Matrix m m R；h : forall A, (e A)ᵀ = e Aᵀ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of matrix algebras commuting with the transpose endomorphisms res
tricts to an
equivalence of Lie algebras of skew-adjoint matrices.
-/
def skewAdjointMatricesLieSubalgebraEquivTranspose {m : Type w} [DecidableEq m] [Fintype m]
    (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (e J) :=
  LieEquiv.ofSubalgebras _ _ e.toLieEquiv <| by
    ext A
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      simpa [-LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective, map_mul, AlgEquiv.apply_symm_apply, map_neg]

@[simp]
/-
**skewAdjointMatricesLieSubalgebraEquivTranspose_apply** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：skewAdjointMatricesLieSubalgebraEquivTranspose_apply {m : Type w} [Decidab
leEq m] [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : forall A, (e A)ᵀ 
= e Aᵀ) (A : skewAdjointMatricesLieSubalgebra J) : (skewAdjointMatricesLieSubalg
ebraEquivTranspose J e h A : Matrix m m R) = e A
参数：e : Matrix n n R ≃ₐ[R] Matrix m m R；h : forall A, (e A)ᵀ = e Aᵀ；A : skewAdjoi
ntMatricesLieSubalgebra J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewAdjointMatricesLieSubalgebraEquivTranspose_apply {m : Type w} [DecidableEq m]
    [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : ∀ A, (e A)ᵀ = e Aᵀ)
    (A : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointMatricesLieSubalgebraEquivTranspose J e h A : Matrix m m R) = e A :=
  rfl
/-
**mem_skewAdjointMatricesLieSubalgebra_unit_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_skewAdjointMatricesLieSubalgebra_unit_smul (u : Rˣ) (J A : Matrix n n 
R) : A in skewAdjointMatricesLieSubalgebra (u • J) ↔ A in skewAdjointMatricesLie
Subalgebra J
参数：u : Rˣ；J A : Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_skewAdjointMatricesLieSubalgebra_unit_smul (u : Rˣ) (J A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra (u • J) ↔ A ∈ skewAdjointMatricesLieSubalgebra J := by
  change A ∈ skewAdjointMatricesSubmodule (u • J) ↔ A ∈ skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor <;> intro h
  · simpa using congr_arg (fun B => u⁻¹ • B) h
  · simp [h]

end SkewAdjointMatrices

