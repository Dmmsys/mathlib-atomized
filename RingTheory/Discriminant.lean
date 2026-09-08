/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `Algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `Algebra.discr_zero_of_not_linearIndependent` : if `b` is not linear independent, then
  `Algebra.discr A b = 0`.
* `Algebra.discr_of_matrix_vecMul` and `Algebra.discr_of_matrix_mulVec` : formulas relating
  `Algebra.discr A ι b` with `Algebra.discr A (b ᵥ* P.map (algebraMap A B))` and
  `Algebra.discr A (P.map (algebraMap A B) *ᵥ b)`.
* `Algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `Algebra.discr K b ≠ 0`.
* `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `Algebra.discr_powerBasis_eq_prod` : the discriminant of a power basis.
* `Algebra.discr_isIntegral` : if `K` and `L` are fields and `IsScalarTower R K L`, if
  `b : ι → L` satisfies `∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`.
* `Algebra.discr_mul_isIntegral_mem_adjoin` : let `K` be the fraction field of an integrally
  closed domain `R` and let `L` be a finite separable extension of `K`. Let `B : PowerBasis K L`
  be such that `IsIntegral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : Set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/

@[expose] public section


universe u v w z

open scoped Matrix

open Matrix Module Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w} [DecidableEq ι]
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `traceMatrix A ι b`. -/
/-
**Algebra.discr** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [F
intype ι] (b : ι -> B)
参数：A : Type u；b : ι -> B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we d
efine
`discr A ι b` as the determinant of `traceMatrix A ι b`.
-/
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := (traceMatrix A b).det
/-
**Algebra.discr_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_def [Fintype ι] (b : ι -> B) : discr A b = (traceMatrix A b).det
参数：b : ι -> B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem discr_def [Fintype ι] (b : ι → B) : discr A b = (traceMatrix A b).det := rfl

variable {A C} in
/-- Mapping a family of vectors along an `AlgEquiv` preserves the discriminant. -/
/-
**Algebra.discr_eq_discr_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_eq_discr_of_algEquiv [Fintype ι] (b : ι -> B) (f : B ≃ₐ[A] C) : Alge
bra.discr A b = Algebra.discr A (f ∘ b)
参数：b : ι -> B；f : B ≃ₐ[A] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Algebra.trace_eq_of_algEquiv`：Algebra.trace_eq_of_algEquiv {A B C : Type
*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (e : B ≃ₐ[
A] C) (x) : Algebr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping a family of vectors along an `AlgEquiv` preserves the discriminant.
-/
theorem discr_eq_discr_of_algEquiv [Fintype ι] (b : ι → B) (f : B ≃ₐ[A] C) :
    Algebra.discr A b = Algebra.discr A (f ∘ b) := by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]

variable {ι' : Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']

section Basic

@[simp]
/-
**Algebra.discr_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = dis
cr A b
参数：b : Basis ι A B；f : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Algebra.traceMatrix_reindex`：traceMatrix_reindex {κ' : Type*} (b : Basis
 κ A B) (f : κ ≃ κ') : traceMatrix A (b.reindex f) = reindex f f (traceMatrix A 
b)
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
-/
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  rw [← Basis.coe_reindex, discr_def, traceMatrix_reindex, det_reindex_self, ← discr_def]

/-- If `b` is not linear independent, then `Algebra.discr A b = 0`. -/
/-
**Algebra.discr_zero_of_not_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
形式化陈述：discr_zero_of_not_linearIndependent [IsDomain A] {b : ι -> B} (hli : ¬Line
arIndependent A b) : discr A b = 0
参数：hli : ¬LinearIndependent A b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.not_linearIndependent_iff`：Fintype.not_linearIndependent_iff [Fi
ntype ι] : ¬LinearIndependent R v ↔ exists g : ι -> R, ∑ i, g i • v i = 0 ∧ exis
ts i, g i != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matrix.eq_zero_of_mulVec_eq_zero`：eq_zero_of_mulVec_eq_zero [NoZeroDivis
ors R] (hM : M.det != 0) {v : m -> R} (hv : M *ᵥ v = 0) : v = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If `b` is not linear independent, then `Algebra.discr A b = 0`.
-/
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b : ι → B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b) *ᵥ g = 0 := by
    ext i
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← map_sum, ← sum_mul, hg, zero_mul, map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi

variable {A}

/-- Relation between `Algebra.discr A ι b` and
`Algebra.discr A (b ᵥ* P.map (algebraMap A B))`. -/
/-
**Algebra.discr_of_matrix_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_of_matrix_vecMul (b : ι -> B) (P : Matrix ι ι A) : discr A (b ᵥ* P.m
ap (algebraMap A B)) = P.det ^ 2 * discr A b
参数：b : ι -> B；P : Matrix ι ι A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Algebra.traceMatrix_of_matrix_vecMul`：traceMatrix_of_matrix_vecMul [Fint
ype κ] (b : κ -> B) (P : Matrix κ κ A) : traceMatrix A (b ᵥ* P.map (algebraMap A
 B)) = Pᵀ * traceMatrix A …
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
Relation between `Algebra.discr A ι b` and
`Algebra.discr A (b ᵥ* P.map (algebraMap A B))`.
-/
theorem discr_of_matrix_vecMul (b : ι → B) (P : Matrix ι ι A) :
    discr A (b ᵥ* P.map (algebraMap A B)) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_vecMul, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]

/-- Relation between `Algebra.discr A ι b` and
`Algebra.discr A ((P.map (algebraMap A B)) *ᵥ b)`. -/
/-
**Algebra.discr_of_matrix_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_of_matrix_mulVec (b : ι -> B) (P : Matrix ι ι A) : discr A (P.map (a
lgebraMap A B) *ᵥ b) = P.det ^ 2 * discr A b
参数：b : ι -> B；P : Matrix ι ι A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Algebra.traceMatrix_of_matrix_mulVec`：traceMatrix_of_matrix_mulVec [Fint
ype κ] (b : κ -> B) (P : Matrix κ κ A) : traceMatrix A (P.map (algebraMap A B) *
ᵥ b) = P * traceMatrix A b…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
Relation between `Algebra.discr A ι b` and
`Algebra.discr A ((P.map (algebraMap A B)) *ᵥ b)`.
-/
theorem discr_of_matrix_mulVec (b : ι → B) (P : Matrix ι ι A) :
    discr A (P.map (algebraMap A B) *ᵥ b) = P.det ^ 2 * discr A b := by
  rw [discr_def, traceMatrix_of_matrix_mulVec, det_mul, det_mul, det_transpose, mul_comm, ←
    mul_assoc, discr_def, pow_two]

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]
variable [Algebra K L] [Algebra K E]
variable [Module.Finite K L] [IsAlgClosed E]

/-- If `b` is a basis of a finite separable field extension `L/K`, then `Algebra.discr K b ≠ 0`. -/
/-
**Algebra.discr_not_zero_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_not_zero_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) : disc
r K b != 0
参数：b : Basis ι K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.traceMatrix_of_basis`：traceMatrix_of_basis [Fintype κ] [Decidabl
eEq κ] (b : Basis κ A B) : traceMatrix A b = (traceForm A B).toMatrix b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det
_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) : B.Nondegenerate ↔ (BilinForm.
toMatrix b B).det != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate

--- 原说明 ---
If `b` is a basis of a finite separable field extension `L/K`, then `Algebra.dis
cr K b ≠ 0`.
-/
theorem discr_not_zero_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) :
    discr K b ≠ 0 := by
  rw [discr_def, traceMatrix_of_basis, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_nondegenerate _ _

/-- If `b` is a basis of a finite separable field extension `L/K`,
  then `Algebra.discr K b` is a unit. -/
/-
**Algebra.discr_isUnit_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_isUnit_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) : IsUnit
 (discr K b)
参数：b : Basis ι K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Algebra.discr_not_zero_of_basis`：discr_not_zero_of_basis [Algebra.IsSepa
rable K L] (b : Basis ι K L) : discr K b != 0

--- 原说明 ---
If `b` is a basis of a finite separable field extension `L/K`,
  then `Algebra.discr K b` is a unit.
-/
theorem discr_isUnit_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)

variable (b : ι → L) (pb : PowerBasis K L)

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
/-
**Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra`。
形式化陈述：discr_eq_det_embeddingsMatrixReindex_pow_two [Algebra.IsSeparable K L] (e 
: ι ≃ (L ->ₐ[K] E)) : algebraMap K E (discr K b) = (embeddingsMatrixReindex K E 
b e).det ^ 2
参数：e : ι ≃ (L ->ₐ[K] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans`：traceMatrix_eq
_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L ->ₐ[K] E)) : (traceMa
trix K b).map (algebraMap K E) = embeddingsMat…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of
 the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : 
L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bi
jection
`e : ι ≃ (L →ₐ[K] E)`.
-/
theorem discr_eq_det_embeddingsMatrixReindex_pow_two
    [Algebra.IsSeparable K L] (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    traceMatrix_eq_embeddingsMatrixReindex_mul_trans, det_mul, det_transpose, pow_two]

/-- The discriminant of a power basis. -/
/-
**Algebra.discr_powerBasis_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L ->ₐ[K] E)) [Algebra.IsSepara
ble K L] : algebraMap K E (discr K pb.basis) = ∏ i : Fin pb.dim, ∏ j in Ioi i, (
e j pb.gen - e i pb.gen) ^ 2
参数：e : Fin pb.dim ≃ (L ->ₐ[K] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`：discr_eq_det_embed
dingsMatrixReindex_pow_two [Algebra.IsSeparable K L] (e : ι ≃ (L ->ₐ[K] E)) : al
gebraMap K E (discr K b) = (embeddingsMatr…
· 使用定理 `Algebra.embeddingsMatrixReindex_eq_vandermonde`：embeddingsMatrixReindex_
eq_vandermonde (pb : PowerBasis A B) (e : Fin pb.dim ≃ (B ->ₐ[A] C)) : embedding
sMatrixReindex A C pb.basis e = (van…
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_vandermonde`：det_vandermonde (v : Fin n -> R) : det (vandermo
nde v) = ∏ i : Fin n, ∏ j in Ioi i, (v j - v i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The discriminant of a power basis.
-/
theorem discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L →ₐ[K] E)) [Algebra.IsSeparable K L] :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e,
    embeddingsMatrixReindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow]
  congr; ext i
  rw [← prod_pow]

/-- A variation of `Algebra.discr_powerBasis_eq_prod`. -/
/-
**Algebra.discr_powerBasis_eq_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_powerBasis_eq_prod' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L -
>ₐ[K] E)) : algebraMap K E (discr K pb.basis) = ∏ i : Fin pb.dim, ∏ j in Ioi i, 
-((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen))
参数：e : Fin pb.dim ≃ (L ->ₐ[K] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_powerBasis_eq_prod`：discr_powerBasis_eq_prod (e : Fin pb.d
im ≃ (L ->ₐ[K] E)) [Algebra.IsSeparable K L] : algebraMap K E (discr K pb.basis)
 = ∏ i : Fin pb.dim, ∏…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_bit0`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a b c : R} {k : ℕ}, a ^ k = b → b * b = c → a ^ Nat.mul 2 k = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one`：∀ {R : Type u_1} [inst : CommSemirin
g R] (a : R), a ^ 1 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
A variation of `Algebra.discr_powerBasis_eq_prod`.
-/
theorem discr_powerBasis_eq_prod' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) := by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring

local notation "n" => finrank K L

/-- A variation of `Algebra.discr_powerBasis_eq_prod`. -/
/-
**Algebra.discr_powerBasis_eq_prod''** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_powerBasis_eq_prod'' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L 
->ₐ[K] E)) : algebraMap K E (discr K pb.basis) = (-1) ^ (n * (n - 1) / 2) * ∏ i 
: Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen
)
参数：e : Fin pb.dim ≃ (L ->ₐ[K] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_powerBasis_eq_prod'`：discr_powerBasis_eq_prod' [Algebra.Is
Separable K L] (e : Fin pb.dim ≃ (L ->ₐ[K] E)) : algebraMap K E (discr K pb.basi
s) = ∏ i : Fin pb.dim, …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.card_Ioi`：card_Ioi : #(Ioi a) = n - 1 - a
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 104 条，此处仅展示前 30 条）

--- 原说明 ---
A variation of `Algebra.discr_powerBasis_eq_prod`.
-/
theorem discr_powerBasis_eq_prod'' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      (-1) ^ (n * (n - 1) / 2) *
        ∏ i : Fin pb.dim, ∏ j ∈ Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) := by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj ℚ, Nat.cast_sum]
  have : ∀ x : Fin pb.dim, ↑x + 1 ≤ pb.dim := by simp [Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum, ← @Finset.sum_range ℕ _ pb.dim fun i => i, sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E, ← Fintype.card_fin pb.dim]
    -- FIXME: Without the `Fintype` namespace, why does it complain about `Finset.card_congr` being
    -- deprecated?
    exact Fintype.card_congr e.symm
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := pb.dim.even_mul_pred_self.two_dvd
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp
  have hle : 1 ≤ pb.dim := by
    rw [← hn, Nat.one_le_iff_ne_zero, ← zero_lt_iff, Module.finrank_pos_iff]
    infer_instance
  rw [hn, Nat.cast_div h₂ hne, Nat.cast_mul, Nat.cast_sub hle]
  ring

/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
/-
**Algebra.discr_powerBasis_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_powerBasis_eq_norm [Algebra.IsSeparable K L] : discr K pb.basis = (-
1) ^ (n * (n - 1) / 2) * norm K (aeval pb.gen (minpoly K pb.gen).derivative)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.Separable.map`：∀ {R : Type u} [inst : CommSemiring R] {S : Ty
pe v} [inst_1 : CommSemiring S] {p : Polynomial R},   p.Separable → ∀ {f : R →+*
 S}, (Polynomi…
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `PowerBasis.isIntegral_gen`：isIntegral_gen (pb : PowerBasis A S) : IsInte
gral A pb.gen
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for the discriminant of a power basis using the norm of the field extens
ion.
-/
theorem discr_powerBasis_eq_norm [Algebra.IsSeparable K L] :
    discr K pb.basis =
      (-1) ^ (n * (n - 1) / 2) *
      norm K (aeval pb.gen (minpoly K pb.gen).derivative) := by
  let E := AlgebraicClosure L
  let := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).aroots E).Nodup :=
    nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (minpoly K pb.gen).aroots E := by
    intro σ
    rw [mem_roots, IsRoot.def, eval_map_algebraMap, aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  apply (algebraMap K E).injective
  rw [map_mul, map_pow, map_neg, map_one, discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings, prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply, ← eval_map_algebraMap, ← derivative_map,
      (IsAlgClosed.splits _).eval_root_derivative ((minpoly.monic pb.isIntegral_gen).map _)
      (hroots σ), ← Finset.prod_mk _ (hnodup.erase _)]
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine prod_bij' (fun i _ ↦ ⟨e i.2, e i.1 pb.gen⟩)
    (fun σ hσ ↦ ⟨e.symm (PowerBasis.lift pb σ.2 ?_), e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _ ↦ by simp)
    <;> simp only [mem_sigma, mem_univ, Finset.mem_mk, hnodup.mem_erase_iff, IsRoot.def,
      mem_roots', mem_singleton, true_and, mem_compl, Sigma.forall, Equiv.apply_symm_apply,
      PowerBasis.lift_gen, implies_true, Equiv.symm_apply_apply,
      Sigma.ext_iff, Equiv.symm_apply_eq, heq_eq_eq, and_true] at *
  · simpa only [aeval_def, eval₂_eq_eval_map] using hσ.2.2
  · exact fun a b hba ↦ ⟨fun h ↦ hba <| e.injective <| pb.algHom_ext h.symm, hroots _⟩
  · rintro a b hba ha
    rw [ha, PowerBasis.lift_gen] at hba
    exact hba.1 rfl
  · exact fun a b _ ↦ pb.algHom_ext <| pb.lift_gen _ _

section Integral

variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]

/-- If `K` and `L` are fields and `IsScalarTower R K L`, and `b : ι → L` satisfies
` ∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`. -/
/-
**Algebra.discr_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_isIntegral {b : ι -> L} (h : forall i, IsIntegral R (b i)) : IsInteg
ral R (discr K b)
参数：h : forall i, IsIntegral R (b i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `IsIntegral.det`：IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {
M : Matrix n n A} (h : forall i j, IsIntegral R (M i j)) : IsIntegral R M.det
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …

--- 原说明 ---
If `K` and `L` are fields and `IsScalarTower R K L`, and `b : ι → L` satisfies
` ∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`.
-/
theorem discr_isIntegral {b : ι → L} (h : ∀ i, IsIntegral R (b i)) : IsIntegral R (discr K b) := by
  rw [discr_def]
  exact IsIntegral.det fun i j ↦ isIntegral_trace ((h i).mul (h j))

/-- Let `K` be the fraction field of an integrally closed domain `R` and let `L` be a finite
separable extension of `K`. Let `B : PowerBasis K L` be such that `IsIntegral R B.gen`.
Then for all, `z : L` that are integral over `R`, we have
`(discr K B.basis) • z ∈ adjoin R ({B.gen} : Set L)`. -/
/-
**Algebra.discr_mul_isIntegral_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_mul_isIntegral_mem_adjoin [Algebra.IsSeparable K L] [IsIntegrallyClo
sed R] [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z 
: L} (hz : IsIntegral R z) : discr K B.basis • z in adjoin R ({B.gen} : Set L)
参数：hint : IsIntegral R B.gen；hz : IsIntegral R z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `Algebra.discr.congr_simp`：∀ {ι : Type w} {inst : DecidableEq ι} [inst_1 
: DecidableEq ι] (A : Type u) {B : Type v} [inst_2 : CommRing A]   [inst_3 : Com
mRing B] [inst…
· 使用定理 `Algebra.discr_isUnit_of_basis`：discr_isUnit_of_basis [Algebra.IsSeparabl
e K L] (b : Basis ι K L) : IsUnit (discr K b)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.traceMatrix_of_basis_mulVec`：traceMatrix_of_basis_mulVec [Fintyp
e ι] (b : Basis ι A B) (z : B) : traceMatrix A b *ᵥ b.equivFun z = fun i => trac
e A B (z * b i)
· 使用定理 `Matrix.mulVec_cramer`：mulVec_cramer (A : Matrix n n α) (b : n -> α) : A 
*ᵥ cramer A b = A.det • b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_smul`：mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommC
lass R α α] (M : Matrix m n α) (b : R) (v : n -> α) : M *ᵥ (b • v) = b • M *ᵥ v
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
· 使用定理 `Matrix.nonsing_inv_mul`：nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ * A = 1
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用定理 `Subalgebra.zsmul_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [i
nst_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → ∀
 (n : ℤ), …
· 使用定理 `Subalgebra.prod_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {ι : Ty
pe w} {t …
· 使用定理 `Matrix.updateCol.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type v
} {inst : DecidableEq n} [inst_1 : DecidableEq n] (M M_1 : Matrix m n α),   M = 
M_1 →     ∀ (j j_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be the fraction field of an integrally closed domain `R` and let `L` be 
a finite
separable extension of `K`. Let `B : PowerBasis K L` be such that `IsIntegral R 
B.gen`.
Then for all, `z : L` that are integral over `R`, we have
`(discr K B.basis) • z ∈ adjoin R ({B.gen} : Set L)`.
-/
theorem discr_mul_isIntegral_mem_adjoin [Algebra.IsSeparable K L] [IsIntegrallyClosed R]
    [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z : L}
    (hz : IsIntegral R z) : discr K B.basis • z ∈ adjoin R ({B.gen} : Set L) := by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices ∀ i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i ∈ (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z, Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def, Pi.smul_apply, mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc, ← hr, algebraMap_smul]
    refine Subalgebra.smul_mem _ ?_ _
    rw [B.basis_eq_pow i]
    exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H, ← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec,
    one_mulVec] at cramer
  rw [← congr_fun cramer i, cramer_apply, det_apply]
  refine
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))

end Integral

end Field

section Int

/-- Two (finite) ℤ-bases have the same discriminant. -/
/-
**Algebra.discr_eq_discr** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：discr_eq_discr (b : Basis ι Int A) (b' : Basis ι Int A) : Algebra.discr In
t b = Algebra.discr Int b'
参数：b : Basis ι Int A；b' : Basis ι Int A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toMatrix_map_vecMul`：toMatrix_map_vecMul {S : Type*} [Semir
ing S] [Algebra R S] [Fintype ι] (b : Basis ι R S) (v : ι' -> S) : b ᵥ* ((b.toMa
trix v).map <| algebra…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix_id_eq_basis_toMatrix`：LinearMap.toMatrix_id_eq_basis_
toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] : LinearMap.toMatrix b b' id = 
b'.toMatrix b
· 使用定理 `LinearEquiv.isUnit_det`：LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Bas
is ι R M) (v' : Basis ι R M') : IsUnit (LinearMap.toMatrix v v' f).det
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `Int.isUnit_iff`：isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.discr_of_matrix_vecMul`：discr_of_matrix_vecMul (b : ι -> B) (P :
 Matrix ι ι A) : discr A (b ᵥ* P.map (algebraMap A B)) = P.det ^ 2 * discr A b

--- 原说明 ---
Two (finite) ℤ-bases have the same discriminant.
-/
theorem discr_eq_discr (b : Basis ι ℤ A) (b' : Basis ι ℤ A) :
    Algebra.discr ℤ b = Algebra.discr ℤ b' := by
  convert! Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  · rw [Basis.toMatrix_map_vecMul]
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff, ← sq_eq_one_iff] at this
      rw [this, one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℤ A) b b'

end Int

end Discr

end Algebra

