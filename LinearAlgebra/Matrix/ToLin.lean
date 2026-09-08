/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Ideal.Span

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `LinearMap.toMatrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
  the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `Matrix κ ι R`
* `Matrix.toLin`: the inverse of `LinearMap.toMatrix`
* `LinearMap.toMatrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
  to `Matrix m n R` (with the standard basis on `m → R` and `n → R`)
* `Matrix.toLin'`: the inverse of `LinearMap.toMatrix'`
* `algEquivMatrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
  `R`-endomorphisms of `M` and `Matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `Matrix.mulVec` gives us a linear equivalence
`Matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `Matrix.vecMul` gives us a linear equivalence
`Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `Matrix.vecMul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/

@[expose] public section

noncomputable section

open LinearMap Matrix Module Set Submodule

/-!
### Bilinear versions of matrix products

The definitions in this section are stated with two extra rings, to allow for non-commutative rings.
-/

section Bilinear
variable {l m n R S A : Type*}
variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]
variable [Module R A] [Module S A]
variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

variable (R S)

/-- `Matrix.vecMul` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `vecMulBilin A Aᵐᵒᵖ` -/
/-
**Matrix.vecMulBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.vecMulBilin [Fintype m] : (m -> A) ->ₗ[R] Matrix m n A ->ₗ[S] (n ->
 A) where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.vecMul_add`：vecMul_add [Fintype m] (A B : Matrix m n α) (x : m ->
 α) : x ᵥ* (A + B) = x ᵥ* A + x ᵥ* B

--- 原说明 ---
`Matrix.vecMul` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `vecMulBilin A Aᵐᵒᵖ`
-/
def Matrix.vecMulBilin [Fintype m] : (m → A) →ₗ[R] Matrix m n A →ₗ[S] (n → A) where
  toFun x :=
  { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _

@[simp]
/-
**Matrix.vecMulBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.vecMulBilin_apply [Fintype m] (v : m -> A) (M : Matrix m n A) : Mat
rix.vecMulBilin R S v M = v ᵥ* M
参数：v : m -> A；M : Matrix m n A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.vecMulBilin_apply [Fintype m] (v : m → A) (M : Matrix m n A) :
    Matrix.vecMulBilin R S v M = v ᵥ* M := rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ →ₗ[_] Matrix m n A →ₗ[_] _)

/-- `Matrix.mulVec` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `mulVecBilin A Aᵐᵒᵖ` -/
/-
**Matrix.mulVecBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.mulVecBilin [Fintype n] : Matrix m n A ->ₗ[R] (n -> A) ->ₗ[S] (m ->
 A) where toFun M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVec_add`：mulVec_add [Fintype n] (A : Matrix m n α) (x y : n ->
 α) : A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y

--- 原说明 ---
`Matrix.mulVec` as a bilinear map.

When `A` is non-commutative, this can be instantiated as `mulVecBilin A Aᵐᵒᵖ`
-/
def Matrix.mulVecBilin [Fintype n] : Matrix m n A →ₗ[R] (n → A) →ₗ[S] (m → A) where
  toFun M :=
  { toFun x := M *ᵥ x
    map_add' _ _ := mulVec_add _ _ _
    map_smul' _ _ := mulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_mulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_mulVec _ _ _

@[simp]
/-
**Matrix.mulVecBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecBilin_apply [Fintype n] (M : Matrix m n A) (v : n -> A) : Mat
rix.mulVecBilin R S M v = M *ᵥ v
参数：M : Matrix m n A；v : n -> A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.mulVecBilin_apply [Fintype n] (M : Matrix m n A) (v : n → A) :
    Matrix.mulVecBilin R S M v = M *ᵥ v := rfl
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A →ₗ[_] _ →ₗ[_] _)

/-- `vecMulVec` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `vecMulVecBilin A Aᵐᵒᵖ`. -/
@[simps]
/-
**vecMulVecBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：vecMulVecBilin : (m -> A) ->ₗ[R] (n -> A) ->ₗ[S] Matrix m n A where toFun 
x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecMulVec` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `vecMulVecBilin A
 Aᵐᵒᵖ`.
-/
def vecMulVecBilin : (m → A) →ₗ[R] (n → A) →ₗ[S] Matrix m n A where
  toFun x :=
    { toFun y := vecMulVec x y
      map_add' _ _ := vecMulVec_add _ _ _
      map_smul' _ _ := vecMulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMulVec _ _ _
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {A} [Semiring A] := (vecMulVecBilin A Aᵐᵒᵖ : (m → A) →ₗ[_] (n → A) →ₗ[_] _)

/-- `dotProduct` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `dotProductBilin A Aᵐᵒᵖ`. -/
@[simps]
/-
**dotProductBilin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dotProductBilin [Fintype m] : (m -> A) ->ₗ[R] (m -> A) ->ₗ[S] A where toFu
n x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `dotProduct_add`：dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w

--- 原说明 ---
`dotProduct` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `dotProductBilin 
A Aᵐᵒᵖ`.
-/
def dotProductBilin [Fintype m] : (m → A) →ₗ[R] (m → A) →ₗ[S] A where
  toFun x :=
    { toFun y := dotProduct x y
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' _ _ := dotProduct_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_dotProduct _ _ _
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {A} [Semiring A] [Fintype m] := (dotProductBilin A Aᵐᵒᵖ : (m → A) →ₗ[_] _ →ₗ[_] _)

end Bilinear

section ToMatrixRight
variable {R : Type*} [Semiring R]
variable {l m n : Type*}

/-- `Matrix.vecMul M` is a linear map.

Note this is a special case of `Matrix.vecMulBilin`. -/
/-
**Matrix.vecMulLinear** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m -> R) ->ₗ[R] n -> 
R
参数：M : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.vecMul M` is a linear map.

Note this is a special case of `Matrix.vecMulBilin`.
-/
abbrev Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R :=
  Matrix.vecMulBilin R Rᵐᵒᵖ |>.flip M
/-
**Matrix.vecMulLinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {m : Type u_3} {n : Type u_4} [inst_1
 : Fintype m] (M : Matrix m n R) (x : m → R),   M.vecMulLinear x = Matrix.vecMul
 x M
参数：M : Matrix m n R；x : m → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Matrix.vecMulLinear_apply [Fintype m] (M : Matrix m n R) (x : m → R) :
    M.vecMulLinear x = x ᵥ* M := rfl
/-
**Matrix.coe_vecMulLinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) : (M.vecMulLinear :
 _ -> _) = M.vecMul
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ → _) = M.vecMul := rfl

variable [Fintype m]

set_option backward.isDefEq.respectTransparency false in
/-
**range_vecMulLinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_vecMulLinear (M : Matrix m n R) : LinearMap.range M.vecMulLinear = s
pan R (range M.row)
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.iSup_span`：iSup_span {ι : Sort*} (p : ι -> Set M) : ⨆ i, span 
R (p i) = span R (⋃ i, p i)
· 使用定理 `Set.range_eq_iUnion`：range_eq_iUnion {ι} (f : ι -> α) : range f = ⋃ i, {
f i}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `single_dotProduct`：single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ 
v = x * v i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_vecMulLinear (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M.row) := by
  let := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    LinearMap.single, LinearMap.coe_mk, AddHom.coe_mk, row_def]
  unfold vecMul
  simp_rw [single_dotProduct, one_mul]
/-
**Matrix.vecMul_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.vecMul_injective_iff {M : Matrix m n R} : Function.Injective M.vecM
ul ↔ LinearIndependent R M.row
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.coe_vecMulLinear`：Matrix.coe_vecMulLinear [Fintype m] (M : Matrix
 m n R) : (M.vecMulLinear : _ -> _) = M.vecMul
· 使用定理 `linearIndependent_iff_injective_fintypeLinearCombination`：linearIndepend
ent_iff_injective_fintypeLinearCombination [Fintype ι] : LinearIndependent R v ↔
 Injective (Fintype.linearCombination R v)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.vecMul_eq_sum`：vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix
 m n α) : v ᵥ* M = ∑ i, v i • M i
-/
theorem Matrix.vecMul_injective_iff {M : Matrix m n R} :
    Function.Injective M.vecMul ↔ LinearIndependent R M.row := by
  rw [← coe_vecMulLinear, linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _
/-
**Matrix.linearIndependent_rows_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.linearIndependent_rows_of_isUnit {A : Matrix m m R} [DecidableEq m]
 (ha : IsUnit A) : LinearIndependent R A.row
参数：ha : IsUnit A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_injective_iff`：Matrix.vecMul_injective_iff {M : Matrix m n
 R} : Function.Injective M.vecMul ↔ LinearIndependent R M.row
· 使用引理 `Matrix.vecMul_injective_of_isUnit`：vecMul_injective_of_isUnit [Fintype m
] [DecidableEq m] {A : Matrix m m R} (ha : IsUnit A) : Function.Injective A.vecM
ul
-/
lemma Matrix.linearIndependent_rows_of_isUnit {A : Matrix m m R}
    [DecidableEq m] (ha : IsUnit A) : LinearIndependent R A.row := by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

section

set_option backward.isDefEq.respectTransparency false in
/-- Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `Matrix m n R`,
by having matrices act by right multiplication.
-/
/-
**LinearMap.toMatrixRight'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixRight' [DecidableEq m] : ((m -> R) ->ₗ[R] n -> R) ≃ₗ[Rᵐᵒ
ᵖ] Matrix m n R where toFun f i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `Matr
ix m n R`,
by having matrices act by right multiplication.
-/
def LinearMap.toMatrixRight' [DecidableEq m] : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (single R (fun _ ↦ R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]

/-- A `Matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
/-
**Matrix.toLinearMapRight'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Matrix.toLinearMapRight' [DecidableEq m] : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m -> R) 
->ₗ[R] n -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[
R] (n → R)`,
by having matrices act by right multiplication.
-/
abbrev Matrix.toLinearMapRight' [DecidableEq m] : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearEquiv.symm LinearMap.toMatrixRight'

variable [DecidableEq m]

@[simp]
/-
**Matrix.toLinearMapRight'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {m : Type u_3} {n : Type u_4} [inst_1
 : Fintype m] [inst_2 : DecidableEq m]   (M : Matrix m n R) (v : m → R), (Matrix
.toLinearMapRight' M) v = Matrix.vecMul v M
参数：M : Matrix m n R；v : m → R；Matrix.toLinearMapRight' M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m → R) :
    M.toLinearMapRight' v = v ᵥ* M := rfl

@[simp]
/-
**Matrix.toLinearMapRight'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {l : Type u_2} {m : Type u_3} {n : Ty
pe u_4} [inst_1 : Fintype m]   [inst_2 : DecidableEq m] [inst_3 : Fintype l] [in
st_4 : DecidableEq l] (M : Matrix l m R) (N : Matrix m n R),   Matrix.toLinearMa
pRight' (M * N) = Matrix.toLinearMapRight' N ∘ₗ Matrix.toLinearMapRight' M
参数：M : Matrix l m R；N : Matrix m n R；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
-/
theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    (M * N).toLinearMapRight' = N.toLinearMapRight' ∘ₗ M.toLinearMapRight' :=
  LinearMap.ext fun _x ↦ (vecMul_vecMul _ M N).symm
/-
**Matrix.toLinearMapRight'_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {l : Type u_2} {m : Type u_3} {n : Ty
pe u_4} [inst_1 : Fintype m]   [inst_2 : DecidableEq m] [inst_3 : Fintype l] [in
st_4 : DecidableEq l] (M : Matrix l m R) (N : Matrix m n R)   (x : l → R), (Matr
ix.toLinearMapRight' (M * N)) x = (Matrix.toLinearMapRight' N) ((Matrix.toLinear
MapRight' M) x)
参数：M : Matrix l m R；N : Matrix m n R；x : l → R；Matrix.toLinearMapRight' (M * N)；
Matrix.toLinearMapRight' N；(Matrix.toLinearMapRight' M) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
-/
theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    (M * N).toLinearMapRight' x = N.toLinearMapRight' (M.toLinearMapRight' x) :=
  (vecMul_vecMul _ M N).symm

@[simp]
/-
**LinearMap.toMatrixRight'_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {l : Type u_2} {m : Type u_3} {n : Ty
pe u_4} [inst_1 : Fintype m]   [inst_2 : DecidableEq m] [inst_3 : Fintype l] [in
st_4 : DecidableEq l] (f : (l → R) →ₗ[R] m → R)   (g : (m → R) →ₗ[R] n → R), Lin
earMap.toMatrixRight' (g ∘ₗ f) = LinearMap.toMatrixRight' f * LinearMap.toMatrix
Right' g
参数：f : (l → R) →ₗ[R] m → R；g : (m → R) →ₗ[R] n → R；g ∘ₗ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Matrix.toLinearMapRight'_mul`：∀ {R : Type u_1} [inst : Semiring R] {l : 
Type u_2} {m : Type u_3} {n : Type u_4} [inst_1 : Fintype m]   [inst_2 : Decidab
leEq m] [inst_3 : …
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrixRight'_comp [Fintype l] [DecidableEq l] (f : (l → R) →ₗ[R] m → R)
    (g : (m → R) →ₗ[R] n → R) : (g ∘ₗ f).toMatrixRight' = f.toMatrixRight' * g.toMatrixRight' :=
  Matrix.toLinearMapRight'.injective <| by simp

@[simp]
/-
**Matrix.toLinearMapRight'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {m : Type u_3} [inst_1 : Fintype m] [
inst_2 : DecidableEq m],   Matrix.toLinearMapRight' 1 = LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_one`：vecMul_one (v : m -> α) : v ᵥ* 1 = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toLinearMapRight'_one :
    (1 : Matrix m m R).toLinearMapRight' = LinearMap.id := by
  ext
  simp
/-
**LinearMap.toMatrixRight'_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {m : Type u_3} [inst_1 : Fintype m] [
inst_2 : DecidableEq m],   LinearMap.toMatrixRight' LinearMap.id = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Matrix.toLinearMapRight'_one`：∀ {R : Type u_1} [inst : Semiring R] {m : 
Type u_3} [inst_1 : Fintype m] [inst_2 : DecidableEq m],   Matrix.toLinearMapRig
ht' 1 = LinearMap.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem LinearMap.toMatrixRight'_id : (@LinearMap.id R (m → R)).toMatrixRight' = 1 :=
  Matrix.toLinearMapRight'.injective <| by simp

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`. -/
@[simps]
/-
**Matrix.toLinearEquivRight'OfInv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {m : Type u_3} →       {n : T
ype u_4} →         [inst_1 : Fintype m] →           [inst_2 : DecidableEq m] →  
           [inst_3 : Fintype n] →               [inst_4 : DecidableEq n] →      
           {M : Matrix m n R} → {M' : Matrix n m R} → M * M' = 1 → M' * M = 1 → 
(n → R) ≃ₗ[R] m → R
参数：n → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `M'` are each other's inverse matrices, they provide an equivalence b
etween `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`.
-/
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n → R) ≃ₗ[R] m → R :=
  { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x ↦ by
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }

end
end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section mulVec

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*}

/-- `Matrix.mulVec M` as a linear map.

Note this is a special case of `Matrix.mulVecBilin`. -/
/-
**Matrix.mulVecLin** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n -> R) ->ₗ[R] m -> R
参数：M : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.mulVec M` as a linear map.

Note this is a special case of `Matrix.mulVecBilin`.
-/
abbrev Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R := mulVecBilin R R M
/-
**Matrix.coe_mulVecLin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) : (M.mulVecLin : _ -> 
_) = M.mulVec
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) :
    (M.mulVecLin : _ → _) = M.mulVec := rfl

@[simp]
/-
**Matrix.mulVecLin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n -> R) : M.mul
VecLin v = M *ᵥ v
参数：M : Matrix m n R；v : n -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M *ᵥ v :=
  rfl

@[simp]
/-
**Matrix.mulVecLin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.zero_mulVec`：zero_mulVec [Fintype n] (v : n -> α) : (0 : Matrix m
 n α) *ᵥ v = 0
-/
theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
  LinearMap.ext zero_mulVec

@[simp]
/-
**Matrix.mulVecLin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) : (M + N).mulVecLin 
= M.mulVecLin + N.mulVecLin
参数：M N : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Matrix.add_mulVec`：add_mulVec [Fintype n] (A B : Matrix m n α) (x : n ->
 α) : (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x
-/
theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
  LinearMap.ext fun _ ↦ add_mulVec _ _ _
/-
**Matrix.mulVecLin_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : Fintype m] (M : Matrix m n R),   M.transpose.mulVecLin = M.vecMulLinear
参数：M : Matrix m n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_transpose`：mulVec_transpose [Fintype m] (A : Matrix m n α)
 (x : m -> α) : Aᵀ *ᵥ x = x ᵥ* A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Matrix.mulVecLin_transpose [Fintype m] (M : Matrix m n R) :
    Mᵀ.mulVecLin = M.vecMulLinear := by
  ext; simp [mulVec_transpose]
/-
**Matrix.vecMulLinear_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : Fintype n] (M : Matrix m n R),   M.transpose.vecMulLinear = M.mulVecLin
参数：M : Matrix m n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Matrix.vecMulLinear_transpose [Fintype n] (M : Matrix m n R) :
    Mᵀ.vecMulLinear = M.mulVecLin := by
  ext; simp [vecMul_transpose]
/-
**Matrix.mulVecLin_submatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m -> k) (e₂ : n ≃
 l) (M : Matrix k l R) : (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mul
VecLin ∘ₗ funLeft _ _ e₂.symm
参数：f₁ : m -> k；e₂ : n ≃ l；M : Matrix k l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.submatrix_mulVec_equiv`：submatrix_mulVec_equiv [Fintype n] [Finty
pe o] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : o -> α) (e₁ : l -> m
) (e₂ : o ≃ n) : M.…
-/
theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
  LinearMap.ext fun _ ↦ submatrix_mulVec_equiv _ _ _ _

/-- A variant of `Matrix.mulVecLin_submatrix` that keeps around `LinearEquiv`s. -/
/-
**Matrix.mulVecLin_reindex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
 (M : Matrix k l R) : (reindex e₁ e₂ M).mulVecLin = ↑(LinearEquiv.funCongrLeft R
 R e₁.symm) ∘ₗ M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂)
参数：e₁ : k ≃ m；e₂ : l ≃ n；M : Matrix k l R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVecLin_submatrix`：Matrix.mulVecLin_submatrix [Fintype n] [Fint
ype l] (f₁ : m -> k) (e₂ : n ≃ l) (M : Matrix k l R) : (M.submatrix f₁ e₂).mulVe
cLin = funLeft R…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A variant of `Matrix.mulVecLin_submatrix` that keeps around `LinearEquiv`s.
-/
theorem Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).mulVecLin =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
        M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_submatrix _ _ _

variable [Fintype n]

@[simp]
/-
**Matrix.mulVecLin_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_one [DecidableEq n] : Matrix.mulVecLin (1 : Matrix n n R)
 = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.mulVecLin_one [DecidableEq n] :
    Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]
/-
**Matrix.mulVecLin_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) : M
atrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N)
参数：M : Matrix l m R；N : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
-/
theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
  LinearMap.ext fun _ ↦ (mulVec_mulVec _ _ _).symm
/-
**Matrix.ker_mulVecLin_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix m n R} : (LinearMap.ker M.mulV
ecLin) = ⊥ ↔ forall v, M *ᵥ v = 0 -> v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix m n R} :
    (LinearMap.ker M.mulVecLin) = ⊥ ↔ ∀ v, M *ᵥ v = 0 → v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
/-
**Matrix.range_mulVecLin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.range_mulVecLin (M : Matrix m n R) : LinearMap.range M.mulVecLin = 
span R (range M.col)
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMulLinear_transpose`：∀ {R : Type u_1} [inst : CommSemiring R] 
{m : Type u_4} {n : Type u_5} [inst_1 : Fintype n] (M : Matrix m n R),   M.trans
pose.vecMulLinear =…
· 使用定理 `range_vecMulLinear`：range_vecMulLinear (M : Matrix m n R) : LinearMap.ra
nge M.vecMulLinear = span R (range M.row)
· 使用引理 `Matrix.row_transpose`：row_transpose (A : Matrix m n α) : Aᵀ.row = A.col
-/
theorem Matrix.range_mulVecLin (M : Matrix m n R) :
    LinearMap.range M.mulVecLin = span R (range M.col) := by
  rw [← vecMulLinear_transpose, range_vecMulLinear, row_transpose]
/-
**Matrix.mulVec_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.mulVec_injective_iff {M : Matrix m n R} : Function.Injective M.mulV
ec ↔ LinearIndependent R M.col
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_transpose`：vecMul_transpose [Fintype n] (A : Matrix m n α)
 (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Matrix.mulVec_injective_iff {M : Matrix m n R} :
    Function.Injective M.mulVec ↔ LinearIndependent R M.col := by
  change Function.Injective (fun x ↦ _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]
/-
**Matrix.linearIndependent_cols_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.linearIndependent_cols_of_isUnit [Fintype m] {A : Matrix m m R} [De
cidableEq m] (ha : IsUnit A) : LinearIndependent R A.col
参数：ha : IsUnit A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.mulVec_injective_iff`：Matrix.mulVec_injective_iff {M : Matrix m n
 R} : Function.Injective M.mulVec ↔ LinearIndependent R M.col
· 使用引理 `Matrix.mulVec_injective_of_isUnit`：mulVec_injective_of_isUnit [Fintype m
] [DecidableEq m] {A : Matrix m m R} (ha : IsUnit A) : Function.Injective A.mulV
ec
-/
lemma Matrix.linearIndependent_cols_of_isUnit [Fintype m]
    {A : Matrix m m R} [DecidableEq m] (ha : IsUnit A) :
    LinearIndependent R A.col := by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

end mulVec

section ToMatrix'

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*} [DecidableEq n] [Fintype n]

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `Matrix m n R`. -/
/-
**LinearMap.toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ[R] (n -> R))) : (star 
f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
参数：f : WithConv ((m -> R) ->ₗ[R] (n -> R))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `Matrix m n R`.
-/
def LinearMap.toMatrix' : ((n → R) →ₗ[R] m → R) ≃ₗ[R] Matrix m n R where
  toFun f := of fun i j ↦ f (Pi.single j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_single_one, col_apply, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_single_one, col_apply,
      Matrix.mulVecLin_apply, of_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, of_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply, Matrix.smul_apply]

/-- A `Matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `DecidableEq` and is `Matrix.mulVecLin`. -/
/-
**Matrix.toLin'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toLin' : Matrix m n R ≃ₗ[R] (n -> R) ->ₗ[R] m -> R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star

--- 原说明 ---
A `Matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `DecidableEq` and is `Matrix.mu
lVecLin`.
-/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm
/-
**Matrix.toLin'_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix m n R), Matrix.toLin' M
 = M.mulVecLin
参数：M : Matrix m n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin :=
  rfl

@[simp]
/-
**LinearMap.toMatrix'_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix'.symm = Matrix.
toLin'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
-/
theorem LinearMap.toMatrix'_symm :
    (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl

@[simp]
/-
**Matrix.toLin'_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n],   Matrix.toLin'.symm = LinearMap.toM
atrix'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Matrix.toLin'_symm :
    (Matrix.toLin'.symm : ((n → R) →ₗ[R] m → R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl

@[simp]
/-
**LinearMap.toMatrix'_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix m n R), LinearMap.toMat
rix' (Matrix.toLin' M) = M
参数：M : Matrix m n R；Matrix.toLin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
-/
theorem LinearMap.toMatrix'_toLin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M

@[simp]
/-
**Matrix.toLin'_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n → R) →ₗ[R] m → R), Matrix.t
oLin' (LinearMap.toMatrix' f) = f
参数：f : (n → R) →ₗ[R] m → R；LinearMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Matrix.toLin'_toMatrix' (f : (n → R) →ₗ[R] m → R) :
    Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f

@[simp]
/-
**LinearMap.toMatrix'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n → R) →ₗ[R] m → R) (i : m) (
j : n), LinearMap.toMatrix' f i j = f (Pi.single j 1) i
参数：f : (n → R) →ₗ[R] m → R；i : m；j : n；Pi.single j 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
-/
theorem LinearMap.toMatrix'_apply (f : (n → R) →ₗ[R] m → R) (i j) :
    LinearMap.toMatrix' f i j = f (Pi.single j 1) i :=
  rfl

@[simp]
/-
**Matrix.toLin'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix m n R) (v : n → R), (Ma
trix.toLin' M) v = M.mulVec v
参数：M : Matrix m n R；v : n → R；Matrix.toLin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M *ᵥ v :=
  rfl

@[simp]
/-
**LinearMap.toMatrix'_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} {n : Type u_5} [in
st_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n → R) →ₗ[R] m → R) (v : n → 
R), (LinearMap.toMatrix' f).mulVec v = f v
参数：f : (n → R) →ₗ[R] m → R；v : n → R；LinearMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
-/
theorem LinearMap.toMatrix'_mulVec (f : (n → R) →ₗ[R] m → R) (v : n → R) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← toLin'_apply, toLin'_toMatrix']

@[simp]
/-
**Matrix.toLin'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   Matrix.toLin' 1 = LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVecLin_one`：Matrix.mulVecLin_one [DecidableEq n] : Matrix.mulV
ecLin (1 : Matrix n n R) = LinearMap.id
-/
theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.mulVecLin_one

@[simp]
/-
**LinearMap.toMatrix'_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' LinearMap.id = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `LinearMap.toMatrix'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m :
 Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (
n → R) →ₗ[R] m …
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
theorem LinearMap.toMatrix'_id : LinearMap.toMatrix' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 := by
  ext
  rw [Matrix.one_apply, LinearMap.toMatrix'_apply, id_apply, Pi.single_apply]

@[simp]
/-
**LinearMap.toMatrix'_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'_id`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Ty
pe u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' Lin
earMap.id = …
-/
theorem LinearMap.toMatrix'_one : LinearMap.toMatrix' (1 : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id

@[simp]
/-
**Matrix.toLin'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_3} {m : Type u_4} {n 
: Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n] [inst_3 : Fintype m]
 [inst_4 : DecidableEq m] (M : Matrix l m R) (N : Matrix m n R),   Matrix.toLin'
 (M * N) = Matrix.toLin' M ∘ₗ Matrix.toLin' N
参数：M : Matrix l m R；N : Matrix m n R；M * N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVecLin_mul`：Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R
) (N : Matrix m n R) : Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Mat
rix.mulVec…
-/
theorem Matrix.toLin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.mulVecLin_mul _ _

@[simp]
/-
**Matrix.toLin'_pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n] (M : Matrix n n R)   (k : ℕ), Matrix.toLin' (M ^ k) 
= Matrix.toLin' M ^ k
参数：M : Matrix n n R；k : ℕ；M ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.toLin'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_
5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   Matrix.toLin' 1 = LinearMap.
id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
-/
theorem Matrix.toLin'_pow (M : Matrix n n R) (k : ℕ) :
    (M ^ k).toLin' = M.toLin' ^ k := by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

@[simp]
/-
**Matrix.toLin'_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {k : Type u_2} {l : Type u_3} {m 
: Type u_4} {n : Type u_5}   [inst_1 : DecidableEq n] [inst_2 : Fintype n] [inst
_3 : Fintype l] [inst_4 : DecidableEq l] (f₁ : m → k) (e₂ : n ≃ l)   (M : Matrix
 k l R),   Matrix.toLin' (M.submatrix f₁ ⇑e₂) = LinearMap.funLeft R R f₁ ∘ₗ Matr
ix.toLin' M ∘ₗ LinearMap.funLeft R R ⇑e₂.symm
参数：f₁ : m → k；e₂ : n ≃ l；M : Matrix k l R；M.submatrix f₁ ⇑e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVecLin_submatrix`：Matrix.mulVecLin_submatrix [Fintype n] [Fint
ype l] (f₁ : m -> k) (e₂ : n ≃ l) (M : Matrix k l R) : (M.submatrix f₁ e₂).mulVe
cLin = funLeft R…
-/
theorem Matrix.toLin'_submatrix [Fintype l] [DecidableEq l] (f₁ : m → k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    Matrix.toLin' (M.submatrix f₁ e₂) =
      funLeft R R f₁ ∘ₗ (Matrix.toLin' M) ∘ₗ funLeft _ _ e₂.symm :=
  Matrix.mulVecLin_submatrix _ _ _

/-- A variant of `Matrix.toLin'_submatrix` that keeps around `LinearEquiv`s. -/
/-
**Matrix.toLin'_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {k : Type u_2} {l : Type u_3} {m 
: Type u_4} {n : Type u_5}   [inst_1 : DecidableEq n] [inst_2 : Fintype n] [inst
_3 : Fintype l] [inst_4 : DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)   (M : Matrix
 k l R),   Matrix.toLin' ((Matrix.reindex e₁ e₂) M) =     ↑(LinearEquiv.funCongr
Left R R e₁.symm) ∘ₗ Matrix.toLin' M ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂)
参数：e₁ : k ≃ m；e₂ : l ≃ n；M : Matrix k l R；(Matrix.reindex e₁ e₂) M；LinearEquiv.f
unCongrLeft R R e₁.symm；LinearEquiv.funCongrLeft R R e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mulVecLin_reindex`：Matrix.mulVecLin_reindex [Fintype n] [Fintype 
l] (e₁ : k ≃ m) (e₂ : l ≃ n) (M : Matrix k l R) : (reindex e₁ e₂ M).mulVecLin = 
↑(LinearEquiv.…

--- 原说明 ---
A variant of `Matrix.toLin'_submatrix` that keeps around `LinearEquiv`s.
-/
theorem Matrix.toLin'_reindex [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    Matrix.toLin' (reindex e₁ e₂ M) =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ (Matrix.toLin' M) ∘ₗ
        ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_reindex _ _ _

/-- Shortcut lemma for `Matrix.toLin'_mul` and `LinearMap.comp_apply` -/
/-
**Matrix.toLin'_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_3} {m : Type u_4} {n 
: Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n] [inst_3 : Fintype m]
 [inst_4 : DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) (x : n → R),   (
Matrix.toLin' (M * N)) x = (Matrix.toLin' M) ((Matrix.toLin' N) x)
参数：M : Matrix l m R；N : Matrix m n R；x : n → R；Matrix.toLin' (M * N)；Matrix.toLi
n' M；(Matrix.toLin' N) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)

--- 原说明 ---
Shortcut lemma for `Matrix.toLin'_mul` and `LinearMap.comp_apply`
-/
theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M * N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]
/-
**LinearMap.toMatrix'_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_3} {m : Type u_4} {n 
: Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n] [inst_3 : Fintype l]
 [inst_4 : DecidableEq l] (f : (n → R) →ₗ[R] m → R)   (g : (l → R) →ₗ[R] n → R),
 LinearMap.toMatrix' (f ∘ₗ g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g
参数：f : (n → R) →ₗ[R] m → R；g : (l → R) →ₗ[R] n → R；f ∘ₗ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
-/
theorem LinearMap.toMatrix'_comp [Fintype l] [DecidableEq l] (f : (n → R) →ₗ[R] m → R)
    (g : (l → R) →ₗ[R] n → R) :
    LinearMap.toMatrix' (f.comp g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this, LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
/-
**LinearMap.toMatrix'_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type u_4} [inst_1 : Fintype 
m] [inst_2 : DecidableEq m]   (f g : (m → R) →ₗ[R] m → R), LinearMap.toMatrix' (
f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g
参数：f g : (m → R) →ₗ[R] m → R；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'_comp`：∀ {R : Type u_1} [inst : CommSemiring R] {l : 
Type u_3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fin
type n] [inst_…
-/
theorem LinearMap.toMatrix'_mul [Fintype m] [DecidableEq m] (f g : (m → R) →ₗ[R] m → R) :
    LinearMap.toMatrix' (f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g :=
  LinearMap.toMatrix'_comp f g

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearMap.toMatrix'_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n] (x : R),   LinearMap.toMatrix' ((algebraMap R (Modul
e.End R (n → R))) x) = (Matrix.scalar n) x
参数：x : R；(algebraMap R (Module.End R (n → R))) x；Matrix.scalar n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.toMatrix'_id`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Ty
pe u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' Lin
earMap.id = …
· 使用定理 `Matrix.smul_eq_diagonal_mul`：smul_eq_diagonal_mul [Fintype m] [Decidable
Eq m] (M : Matrix m n α) (a : α) : a • M = (diagonal fun _ => a) * M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n → R)) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]
/-
**Matrix.ker_toLin'_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   {M : Matrix n n R}, (Matrix.toLin' M).ker = ⊥ ↔ ∀ 
(v : n → R), M.mulVec v = 0 → v = 0
参数：Matrix.toLin' M；v : n → R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ker_mulVecLin_eq_bot_iff`：Matrix.ker_mulVecLin_eq_bot_iff {M : Ma
trix m n R} : (LinearMap.ker M.mulVecLin) = ⊥ ↔ forall v, M *ᵥ v = 0 -> v = 0
-/
theorem Matrix.ker_toLin'_eq_bot_iff {M : Matrix n n R} :
    LinearMap.ker (Matrix.toLin' M) = ⊥ ↔ ∀ v, M *ᵥ v = 0 → v = 0 :=
  Matrix.ker_mulVecLin_eq_bot_iff
/-
**Matrix.range_toLin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.range_toLin' (M : Matrix m n R) : LinearMap.range (Matrix.toLin' M)
 = span R (range M.col)
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.range_mulVecLin`：Matrix.range_mulVecLin (M : Matrix m n R) : Line
arMap.range M.mulVecLin = span R (range M.col)
-/
theorem Matrix.range_toLin' (M : Matrix m n R) :
    LinearMap.range (Matrix.toLin' M) = span R (range M.col) :=
  Matrix.range_mulVecLin _

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mulVec` and `M'.mulVec`. -/
@[simps]
/-
**Matrix.toLin'OfInv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {m : Type u_4} →       {n
 : Type u_5} →         [inst_1 : DecidableEq n] →           [inst_2 : Fintype n]
 →             [inst_3 : Fintype m] →               [inst_4 : DecidableEq m] →  
               {M : Matrix m n R} → {M' : Matrix n m R} → M * M' = 1 → M' * M = 
1 → (m → R) ≃ₗ[R] n → R
参数：m → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `M'` are each other's inverse matrices, they provide an equivalence b
etween `m → A`
and `n → A` corresponding to `M.mulVec` and `M'.mulVec`.
-/
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (m → R) ≃ₗ[R] n → R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x ↦ by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLin'_mul_apply, hM'M, Matrix.toLin'_one, id_apply] }

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `Matrix n n R`. -/
/-
**LinearMap.toMatrixAlgEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv' : ((n -> R) ->ₗ[R] n -> R) ≃ₐ[R] Matrix n n R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearMap.toMatrix'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : T
ype u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' 1 
= 1
· 使用定理 `LinearMap.toMatrix'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} [inst_1 : Fintype m] [inst_2 : DecidableEq m]   (f g : (m → R) →ₗ[R] m 
→ R), LinearM…

--- 原说明 ---
Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `Matrix n n R`.
-/
def LinearMap.toMatrixAlgEquiv' : ((n → R) →ₗ[R] n → R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul

/-- A `Matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
/-
**Matrix.toLinAlgEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n -> R) ->ₗ[R] n -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`.
-/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n → R) →ₗ[R] n → R :=
  LinearMap.toMatrixAlgEquiv'.symm

@[simp]
/-
**LinearMap.toMatrixAlgEquiv'_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   LinearMap.toMatrixAlgEquiv'.symm = Matrix.toLinAl
gEquiv'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem LinearMap.toMatrixAlgEquiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl

@[simp]
/-
**Matrix.toLinAlgEquiv'_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   Matrix.toLinAlgEquiv'.symm = LinearMap.toMatrixAl
gEquiv'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem Matrix.toLinAlgEquiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n → R) →ₗ[R] n → R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl

@[simp]
/-
**LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   (M : Matrix n n R), LinearMap.toMatrixAlgEquiv' (M
atrix.toLinAlgEquiv' M) = M
参数：M : Matrix n n R；Matrix.toLinAlgEquiv' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]
/-
**Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   (f : (n → R) →ₗ[R] n → R), Matrix.toLinAlgEquiv' (
LinearMap.toMatrixAlgEquiv' f) = f
参数：f : (n → R) →ₗ[R] n → R；LinearMap.toMatrixAlgEquiv' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (f : (n → R) →ₗ[R] n → R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]
/-
**LinearMap.toMatrixAlgEquiv'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   (f : (n → R) →ₗ[R] n → R) (i j : n), LinearMap.toM
atrixAlgEquiv' f i j = f (Pi.single j 1) i
参数：f : (n → R) →ₗ[R] n → R；i j : n；Pi.single j 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem LinearMap.toMatrixAlgEquiv'_apply (f : (n → R) →ₗ[R] n → R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (Pi.single j 1) i :=
  rfl

@[simp]
/-
**Matrix.toLinAlgEquiv'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n] (M : Matrix n n R)   (v : n → R), (Matrix.toLinAlgEq
uiv' M) v = M.mulVec v
参数：M : Matrix n n R；v : n → R；Matrix.toLinAlgEquiv' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem Matrix.toLinAlgEquiv'_apply (M : Matrix n n R) (v : n → R) :
    Matrix.toLinAlgEquiv' M v = M *ᵥ v :=
  rfl
/-
**Matrix.toLinAlgEquiv'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   Matrix.toLinAlgEquiv' 1 = LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLin'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_
5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   Matrix.toLin' 1 = LinearMap.
id
-/
theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.toLin'_one

@[simp]
/-
**LinearMap.toMatrixAlgEquiv'_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n],   LinearMap.toMatrixAlgEquiv' LinearMap.id = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'_id`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Ty
pe u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LinearMap.toMatrix' Lin
earMap.id = …
-/
theorem LinearMap.toMatrixAlgEquiv'_id :
    LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n → R) →ₗ[R] n → R) = 1 :=
  LinearMap.toMatrix'_id
/-
**LinearMap.toMatrixAlgEquiv'_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   (f g : (n → R) →ₗ[R] n → R),   LinearMap.toMatrixA
lgEquiv' (f ∘ₗ g) = LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' 
g
参数：f g : (n → R) →ₗ[R] n → R；f ∘ₗ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'_comp`：∀ {R : Type u_1} [inst : CommSemiring R] {l : 
Type u_3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fin
type n] [inst_…
-/
theorem LinearMap.toMatrixAlgEquiv'_comp (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f.comp g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrix'_comp _ _
/-
**LinearMap.toMatrixAlgEquiv'_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   (f g : (n → R) →ₗ[R] n → R),   LinearMap.toMatrixA
lgEquiv' (f * g) = LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g
参数：f g : (n → R) →ₗ[R] n → R；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrixAlgEquiv'_comp`：∀ {R : Type u_1} [inst : CommSemiring 
R] {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f g : (n → R)
 →ₗ[R] n → R),   Linea…
-/
theorem LinearMap.toMatrixAlgEquiv'_mul (f g : (n → R) →ₗ[R] n → R) :
    LinearMap.toMatrixAlgEquiv' (f * g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrixAlgEquiv'_comp f g

@[simp]
/-
**LinearMap.isUnit_toMatrix'_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   {f : (n → R) →ₗ[R] n → R}, IsUnit (LinearMap.toMat
rix' f) ↔ IsUnit f
参数：n → R；LinearMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem LinearMap.isUnit_toMatrix'_iff {f : (n → R) →ₗ[R] n → R} : IsUnit f.toMatrix' ↔ IsUnit f :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

@[simp]
/-
**Matrix.isUnit_toLin'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_5} [inst_1 : Decidabl
eEq n] [inst_2 : Fintype n]   {M : Matrix n n R}, IsUnit (Matrix.toLin' M) ↔ IsU
nit M
参数：Matrix.toLin' M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem Matrix.isUnit_toLin'_iff {M : Matrix n n R} : IsUnit M.toLin' ↔ IsUnit M :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

end ToMatrix'

section ToMatrix

section Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
/-
**LinearMap.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix : (M₁ ->ₗ[R] M₂) ≃ₗ[R] Matrix m n R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star

--- 原说明 ---
Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a l
inear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the 
bases.
-/
def LinearMap.toMatrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

/-- `LinearMap.toMatrix'` is a particular case of `LinearMap.toMatrix`, for the standard basis
`Pi.basisFun R n`. -/
/-
**LinearMap.toMatrix_eq_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_4} [inst_1 : Fintype 
n] [inst_2 : DecidableEq n],   LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun
 R n) = LinearMap.toMatrix'
参数：Pi.basisFun R n；Pi.basisFun R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`LinearMap.toMatrix'` is a particular case of `LinearMap.toMatrix`, for the stan
dard basis
`Pi.basisFun R n`.
-/
@[simp] theorem LinearMap.toMatrix_eq_toMatrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
/-
**Matrix.toLin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ ->ₗ[R] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a l
inear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →
ₗ M₂`.
-/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ →ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm

/-- `Matrix.toLin'` is a particular case of `Matrix.toLin`, for the standard basis
`Pi.basisFun R n`. -/
/-
**Matrix.toLin_eq_toLin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) 
= Matrix.toLin'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`Matrix.toLin'` is a particular case of `Matrix.toLin`, for the standard basis
`Pi.basisFun R n`.
-/
theorem Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl

@[simp]
/-
**LinearMap.toMatrix_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v
₁ v₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl

@[simp]
/-
**Matrix.toLin_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl

@[simp]
/-
**Matrix.toLin_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix.toLin v₁ v₂ (LinearMap.t
oMatrix v₁ v₂ f) = f
参数：f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin_symm`：Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = Linea
rMap.toMatrix v₁ v₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem Matrix.toLin_toMatrix (f : M₁ →ₗ[R] M₂) :
    Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.toLin_symm, LinearEquiv.apply_symm_apply]

@[simp]
/-
**LinearMap.toMatrix_toLin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_toLin (M : Matrix m n R) : LinearMap.toMatrix v₁ v₂ (Ma
trix.toLin v₁ v₂ M) = M
参数：M : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin_symm`：Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = Linea
rMap.toMatrix v₁ v₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem LinearMap.toMatrix_toLin (M : Matrix m n R) :
    LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.toLin_symm, LinearEquiv.symm_apply_apply]
/-
**LinearMap.toMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i : m) (j : n) : LinearMap.to
Matrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
参数：f : M₁ ->ₗ[R] M₂；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by
  simp [toMatrix]
/-
**LinearMap.toMatrix_transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_transpose_apply (f : M₁ ->ₗ[R] M₂) (j : n) : (LinearMap
.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j))
参数：f : M₁ ->ₗ[R] M₂；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
-/
theorem LinearMap.toMatrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i ↦ f.toMatrix_apply _ _ i j
/-
**LinearMap.toMatrix_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_apply' (f : M₁ ->ₗ[R] M₂) (i : m) (j : n) : LinearMap.t
oMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
参数：f : M₁ ->ₗ[R] M₂；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
-/
theorem LinearMap.toMatrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.toMatrix_apply v₁ v₂ f i j
/-
**LinearMap.toMatrix_transpose_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_transpose_apply' (f : M₁ ->ₗ[R] M₂) (j : n) : (LinearMa
p.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j))
参数：f : M₁ ->ₗ[R] M₂；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix_transpose_apply`：LinearMap.toMatrix_transpose_apply (
f : M₁ ->ₗ[R] M₂) (j : n) : (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j))
-/
theorem LinearMap.toMatrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.toMatrix_transpose_apply v₁ v₂ f j

/-- This will be a special case of `LinearMap.toMatrix_id_eq_basis_toMatrix`. -/
/-
**LinearMap.toMatrix_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This will be a special case of `LinearMap.toMatrix_id_eq_basis_toMatrix`.
-/
theorem LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]
/-
**LinearMap.toMatrix_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
-/
theorem LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.toMatrix_id v₁

@[simp]
/-
**LinearMap.toMatrix_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_singleton {ι : Type*} [Unique ι] (f : R ->ₗ[R] R) (i j 
: ι) : f.toMatrix (.singleton ι R) (.singleton ι R) i j = f 1
参数：f : R ->ₗ[R] R；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Module.Basis.singleton_apply`：singleton_apply (ι R : Type*) [Unique ι] [
Semiring R] (i) : Basis.singleton ι R i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
-/
lemma LinearMap.toMatrix_singleton {ι : Type*} [Unique ι] (f : R →ₗ[R] R) (i j : ι) :
    f.toMatrix (.singleton ι R) (.singleton ι R) i j = f 1 := by
  simp [toMatrix, Subsingleton.elim j default]

@[simp]
/-
**Matrix.toLin_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
-/
theorem Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrix_id v₁, Matrix.toLin_toMatrix]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.toLin_scalar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_scalar (r : R) : Matrix.toLin v₁ v₁ (scalar n r) = r • Linear
Map.id
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `Matrix.smul_one_eq_diagonal`：smul_one_eq_diagonal [DecidableEq m] (a : α
) : a • (1 : Matrix m m α) = diagonal fun _ => a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toLin_scalar (r : R) : Matrix.toLin v₁ v₁ (scalar n r) = r • LinearMap.id :=
  (LinearMap.toMatrix v₁ v₁).injective (by simp [toMatrix_id, smul_one_eq_diagonal])
/-
**LinearMap.toMatrix_reindexRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_reindexRange [DecidableEq M₁] (f : M₁ ->ₗ[R] M₂) (k : m
) (i : n) : LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, Set.mem_
range_self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ = LinearMap.toMatrix v₁ v₂ f k i
参数：f : M₁ ->ₗ[R] M₂；k : m；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.reindexRange_self`：reindexRange_self (i : ι) (h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.reindexRange_repr`：reindexRange_repr (x : M) (i : ι) (h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, Set.mem_range_self k⟩
        ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i := by
  simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearMap.toMatrix_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_algebraMap (x : R) : LinearMap.toMatrix v₁ v₁ (algebraM
ap R (Module.End R M₁) x) = scalar n x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `Matrix.smul_eq_diagonal_mul`：smul_eq_diagonal_mul [Fintype m] [Decidable
Eq m] (M : Matrix m n α) (a : α) : a • M = (diagonal fun _ => a) * M
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix_algebraMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id, smul_eq_diagonal_mul]
/-
**LinearMap.toMatrix_mulVec_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_mulVec_repr (f : M₁ ->ₗ[R] M₂) (x : M₁) : LinearMap.toM
atrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)
参数：f : M₁ ->ₗ[R] M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearMap.toMatrix.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_3} {n : Type u_4} [inst_1 : Fintype n] [inst_2 : Finite m]   [inst_3 : Dec
idableEq n] {…
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
· 使用定理 `LinearEquiv.arrowCongr_apply`：arrowCongr_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂
 : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ ->ₛₗ[σ₁₁'] M₁') (x : M₂) : arrowCongr e₁ e₂ f x =
 e₂ (f (e₁.symm x)…
· 使用定理 `Module.Basis.equivFun_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem LinearMap.toMatrix_mulVec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
    LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x) := by
  ext i
  rw [← Matrix.toLin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix',
    LinearEquiv.arrowCongr_apply, v₂.equivFun_apply]
  congr
  exact v₁.equivFun.symm_apply_apply x
/-
**Matrix.repr_toLin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.repr_toLin (M : Matrix m n R) (x : M₁) : v₂.repr (M.toLin v₁ v₂ x) 
= M.mulVec (v₁.repr x)
参数：M : Matrix m n R；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_mulVec_repr`：LinearMap.toMatrix_mulVec_repr (f : M₁ -
>ₗ[R] M₂) (x : M₁) : LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
-/
theorem Matrix.repr_toLin (M : Matrix m n R) (x : M₁) :
    v₂.repr (M.toLin v₁ v₂ x) = M.mulVec (v₁.repr x) := by
  rw [← toMatrix_mulVec_repr v₁, toMatrix_toLin]

@[simp]
/-
**LinearMap.toMatrix_basis_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R 
M₁) (b' : Basis l R M₂) : LinearMap.toMatrix b' b (b'.equiv b (Equiv.refl l) : M
₂ ->ₗ[R] M₁) = 1
参数：b : Basis l R M₁；b' : Basis l R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R M₁)
    (b' : Basis l R M₂) :
    LinearMap.toMatrix b' b (b'.equiv b (Equiv.refl l) : M₂ →ₗ[R] M₁) = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
/-
**LinearMap.toMatrix_smulBasis_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_smulBasis_left {G} [Group G] [DistribMulAction G M₁] [S
MulCommClass G R M₁] (g : G) (f : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix (g • v₁) v₂
 f = LinearMap.toMatrix v₁ v₂ (f ∘ₗ DistribSMul.toLinearMap _ _ g)
参数：g : G；f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrix_smulBasis_left {G} [Group G] [DistribMulAction G M₁]
    [SMulCommClass G R M₁] (g : G) (f : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix (g • v₁) v₂ f =
      LinearMap.toMatrix v₁ v₂ (f ∘ₗ DistribSMul.toLinearMap _ _ g) := by
  rfl
/-
**LinearMap.toMatrix_smulBasis_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_smulBasis_right {G} [Group G] [DistribMulAction G M₂] [
SMulCommClass G R M₂] (g : G) (f : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ (g • v₂
) f = LinearMap.toMatrix v₁ v₂ (DistribSMul.toLinearMap _ _ g⁻¹ ∘ₗ f)
参数：g : G；f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrix_smulBasis_right {G} [Group G] [DistribMulAction G M₂]
    [SMulCommClass G R M₂] (g : G) (f : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ (g • v₂) f =
      LinearMap.toMatrix v₁ v₂ (DistribSMul.toLinearMap _ _ g⁻¹ ∘ₗ f) := by
  rfl

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)
/-
**LinearMap.toMatrix_map_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_map_left (f : M₃ ->ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃) : f.toMat
rix (v₁.map g) v₂ = (f ∘ₗ g.toLinearMap).toMatrix v₁ v₂
参数：f : M₃ ->ₗ[R] M₂；g : M₁ ≃ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrix_map_left (f : M₃ →ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃) :
    f.toMatrix (v₁.map g) v₂ = (f ∘ₗ g.toLinearMap).toMatrix v₁ v₂ := by
  rfl
/-
**LinearMap.toMatrix_map_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_map_right (f : M₁ ->ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃) : f.toMa
trix v₁ (v₂.map g) = (g.symm.toLinearMap ∘ₗ f).toMatrix v₁ v₂
参数：f : M₁ ->ₗ[R] M₃；g : M₂ ≃ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrix_map_right (f : M₁ →ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃) :
    f.toMatrix v₁ (v₂.map g) = (g.symm.toLinearMap ∘ₗ f).toMatrix v₁ v₂ := by
  rfl

end Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

set_option backward.isDefEq.respectTransparency false in
/-- The matrix of `toSpanSingleton R M₂ x` given by bases `v₁` and `v₂` is equal to
`vecMulVec (v₂.repr x) v₁`. When `v₁ = Module.Basis.singleton`
then this is the column matrix of `v₂.repr x`. -/
/-
**LinearMap.toMatrix_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_toSpanSingleton [Finite m] (v₁ : Basis n R R) (v₂ : Bas
is m R M₂) (x : M₂) : (toSpanSingleton R M₂ x).toMatrix v₁ v₂ = vecMulVec (v₂.re
pr x) v₁
参数：v₁ : Basis n R R；v₂ : Basis m R M₂；x : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The matrix of `toSpanSingleton R M₂ x` given by bases `v₁` and `v₂` is equal to
`vecMulVec (v₂.repr x) v₁`. When `v₁ = Module.Basis.singleton`
then this is the column matrix of `v₂.repr x`.
-/
theorem LinearMap.toMatrix_toSpanSingleton [Finite m] (v₁ : Basis n R R) (v₂ : Basis m R M₂)
    (x : M₂) : (toSpanSingleton R M₂ x).toMatrix v₁ v₂ = vecMulVec (v₂.repr x) v₁ := by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearMap.toMatrix_smulRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_smulRight [Finite m] (f : M₁ ->ₗ[R] R) (x : M₂) : toMat
rix v₁ v₂ (f.smulRight x) = vecMulVec (v₂.repr x) (f ∘ v₁)
参数：f : M₁ ->ₗ[R] R；x : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma LinearMap.toMatrix_smulRight [Finite m] (f : M₁ →ₗ[R] R) (x : M₂) :
    toMatrix v₁ v₂ (f.smulRight x) = vecMulVec (v₂.repr x) (f ∘ v₁) := by
  ext i j
  simpa [toMatrix_apply, vecMulVec_apply] using mul_comm _ _
/-
**Matrix.toLin_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v : M₁) : Matrix.toLin 
v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j
参数：M : Matrix m n R；v : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {m : Type 
u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : Matrix 
m n R) (v…
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
-/
theorem Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v : M₁) :
    Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply, v₂.equivFun_symm_apply]

@[simp]
/-
**Matrix.toLin_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i : n) : Matrix.toLin v₁
 v₂ M (v₁ i) = ∑ j, M j i • v₂ j
参数：M : Matrix m n R；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_apply`：Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v
 : M₁) : Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Matrix.mulVec.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst :
 NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n α) (v : n →
 α) (x :…
· 使用定理 `dotProduct.eq_1`：∀ {m : Type u_2} {α : Type v} [inst : Fintype m] [inst_
1 : Mul α] [inst_2 : AddCommMonoid α] (v w : m → α),   v ⬝ᵥ w = ∑ i, v i * w i
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i : n) :
    Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j := by
  rw [Matrix.toLin_apply, Finset.sum_congr rfl fun j _hj ↦ ?_]
  rw [Basis.repr_self, Matrix.mulVec, dotProduct, Finset.sum_eq_single i, Finsupp.single_eq_same,
    mul_one]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne, mul_zero]
  · intros
    have := Finset.mem_univ i
    contradiction
/-
**Matrix.toLin_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_apply_eq_zero_iff {R M₁ M₂ : Type*} [Finite m] [CommRing R] [
AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] {v₁ : Basis n R M
₁} {v₂ : Basis m R M₂} {A : Matrix m n R} {x : M₁} : A.toLin v₁ v₂ x = 0 ↔ foral
l j, (A *ᵥ v₁.repr x) j = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.toLin_apply`：Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v
 : M₁) : Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toLin_apply_eq_zero_iff {R M₁ M₂ : Type*} [Finite m] [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    {v₁ : Basis n R M₁} {v₂ : Basis m R M₂} {A : Matrix m n R} {x : M₁} :
    A.toLin v₁ v₂ x = 0 ↔ ∀ j, (A *ᵥ v₁.repr x) j = 0 := by
  have := Fintype.ofFinite m
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h ↦ by simp [h]⟩

variable [Fintype m]

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)
/-
**LinearMap.toMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_comp [Finite l] [DecidableEq m] (f : M₂ ->ₗ[R] M₃) (g :
 M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) = LinearMap.toMatrix v₂ v₃ 
f * LinearMap.toMatrix v₁ v₂ g
参数：f : M₂ ->ₗ[R] M₃；g : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.arrowCongr_comp`：arrowCongr_comp (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ :
 M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂'') (f : M₁ ->ₛₗ[σ₁₁'] M₁') (g : 
M₁' ->ₛₗ[σ₁'₁''] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'_comp`：∀ {R : Type u_1} [inst : CommSemiring R] {l : 
Type u_3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fin
type n] [inst_…
-/
theorem LinearMap.toMatrix_comp [Finite l] [DecidableEq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) =
    LinearMap.toMatrix v₂ v₃ f * LinearMap.toMatrix v₁ v₂ g := by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply]
  rw [LinearEquiv.arrowCongr_comp _ v₂.equivFun, LinearMap.toMatrix'_comp]
/-
**LinearMap.toMatrix_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : LinearMap.toMatrix v₁ v₁ (f 
* g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix v₁ v₁ g
参数：f g : M₁ ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
-/
theorem LinearMap.toMatrix_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix v₁ v₁ g := by
  rw [Module.End.mul_eq_comp, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
/-
**LinearMap.toMatrix_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_pow (f : M₁ ->ₗ[R] M₁) (k : Nat) : (toMatrix v₁ v₁ f) ^
 k = toMatrix v₁ v₁ (f ^ k)
参数：f : M₁ ->ₗ[R] M₁；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g
-/
lemma LinearMap.toMatrix_pow (f : M₁ →ₗ[R] M₁) (k : ℕ) :
    (toMatrix v₁ v₁ f) ^ k = toMatrix v₁ v₁ (f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, ← toMatrix_mul]
/-
**Matrix.toLin_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix
 m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin
 v₁ v₂ B)
参数：A : Matrix l m R；B : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
-/
theorem Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) := by
  apply (LinearMap.toMatrix v₁ v₃).injective
  have : DecidableEq l := fun _ _ ↦ Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]

@[simp]
/-
**Matrix.toLin_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_pow (A : Matrix n n R) (k : Nat) : (A ^ k).toLin v₁ v₁ = (A.t
oLin v₁ v₁) ^ k
参数：A : Matrix n n R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.toLin_one`：Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
-/
theorem Matrix.toLin_pow (A : Matrix n n R) (k : ℕ) :
    (A ^ k).toLin v₁ v₁ = (A.toLin v₁ v₁) ^ k := by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

/-- Shortcut lemma for `Matrix.toLin_mul` and `LinearMap.comp_apply`. -/
/-
**Matrix.toLin_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_mul_apply [Finite l] [DecidableEq m] (A : Matrix l m R) (B : 
Matrix m n R) (x) : Matrix.toLin v₁ v₃ (A * B) x = (Matrix.toLin v₂ v₃ A) (Matri
x.toLin v₁ v₂ B x)
参数：A : Matrix l m R；B : Matrix m n R；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)

--- 原说明 ---
Shortcut lemma for `Matrix.toLin_mul` and `LinearMap.comp_apply`.
-/
theorem Matrix.toLin_mul_apply [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
    (x) : Matrix.toLin v₁ v₃ (A * B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.toLin_mul v₁ v₂, LinearMap.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `Matrix.toLin M` and `Matrix.toLin M'`
form a linear equivalence. -/
@[simps]
/-
**Matrix.toLinOfInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (
hMM' : M * M' = 1) (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂
参数：hMM' : M * M' = 1；hM'M : M' * M = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `M` and `M` are each other's inverse matrices, `Matrix.toLin M` and `Matrix.t
oLin M'`
form a linear equivalence.
-/
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
    (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x ↦ by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x ↦ by
      rw [← Matrix.toLin_mul_apply, hMM', Matrix.toLin_one, id_apply] }

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
/-
**LinearMap.toMatrixAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv : (M₁ ->ₗ[R] M₁) ≃ₐ[R] Matrix n n R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g

--- 原说明 ---
Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed 
by the basis.
-/
def LinearMap.toMatrixAlgEquiv : (M₁ →ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
/-
**Matrix.toLinAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ ->ₗ[R] M₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear map
s `M₁ →ₗ M₁`.
-/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ →ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]
/-
**LinearMap.toMatrixAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_symm : (LinearMap.toMatrixAlgEquiv v₁).symm = M
atrix.toLinAlgEquiv v₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.toMatrixAlgEquiv_symm :
    (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl

@[simp]
/-
**Matrix.toLinAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_symm : (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toM
atrixAlgEquiv v₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Matrix.toLinAlgEquiv_symm :
    (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl

@[simp]
/-
**Matrix.toLinAlgEquiv_toMatrixAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ ->ₗ[R] M₁) : Matrix.toLinAlg
Equiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f
参数：f : M₁ ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLinAlgEquiv_symm`：Matrix.toLinAlgEquiv_symm : (Matrix.toLinAlgE
quiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ →ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.apply_symm_apply]

@[simp]
/-
**LinearMap.toMatrixAlgEquiv_toLinAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) : LinearMap.to
MatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLinAlgEquiv_symm`：Matrix.toLinAlgEquiv_symm : (Matrix.toLinAlgE
quiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
-/
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.toLinAlgEquiv_symm, AlgEquiv.symm_apply_apply]
/-
**LinearMap.toMatrixAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_apply (f : M₁ ->ₗ[R] M₁) (i j : n) : LinearMap.
toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i
参数：f : M₁ ->ₗ[R] M₁；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrixAlgEquiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]
/-
**LinearMap.toMatrixAlgEquiv_transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ ->ₗ[R] M₁) (j : n) : (L
inearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j))
参数：f : M₁ ->ₗ[R] M₁；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i ↦ f.toMatrix_apply _ _ i j
/-
**LinearMap.toMatrixAlgEquiv_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_apply' (f : M₁ ->ₗ[R] M₁) (i j : n) : LinearMap
.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i
参数：f : M₁ ->ₗ[R] M₁；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrixAlgEquiv_apply`：LinearMap.toMatrixAlgEquiv_apply (f : 
M₁ ->ₗ[R] M₁) (i j : n) : LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j
)) i
-/
theorem LinearMap.toMatrixAlgEquiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.toMatrixAlgEquiv_apply v₁ f i j
/-
**LinearMap.toMatrixAlgEquiv_transpose_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ ->ₗ[R] M₁) (j : n) : (
LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j))
参数：f : M₁ ->ₗ[R] M₁；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrixAlgEquiv_transpose_apply`：LinearMap.toMatrixAlgEquiv_t
ranspose_apply (f : M₁ ->ₗ[R] M₁) (j : n) : (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j
 = v₁.repr (f (v₁ j))
-/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j
/-
**Matrix.toLinAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) : Matrix.toLinAlgEq
uiv v₁ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₁ j
参数：M : Matrix n n R；v : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLinAlgEquiv'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {n
 : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R)   
(v : n → R), (Mat…
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
-/
theorem Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply, v₁.equivFun_symm_apply]

@[simp]
/-
**Matrix.toLinAlgEquiv_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) : Matrix.toLinAlgEqui
v v₁ M (v₁ i) = ∑ j, M j i • v₁ j
参数：M : Matrix n n R；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
-/
theorem Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.toLin_self _ _ _ _
/-
**LinearMap.toMatrixAlgEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]
/-
**Matrix.toLinAlgEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrixAlgEquiv_id`：LinearMap.toMatrixAlgEquiv_id : LinearMap
.toMatrixAlgEquiv v₁ id = 1
· 使用定理 `Matrix.toLinAlgEquiv_toMatrixAlgEquiv`：Matrix.toLinAlgEquiv_toMatrixAlgE
quiv (f : M₁ ->ₗ[R] M₁) : Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁
 f) = f
-/
theorem Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
/-
**LinearMap.toMatrixAlgEquiv_reindexRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ ->ₗ[R] M₁
) (k i : n) : LinearMap.toMatrixAlgEquiv v₁.reindexRange f ⟨v₁ k, Set.mem_range_
self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ = LinearMap.toMatrixAlgEquiv v₁ f k i
参数：f : M₁ ->ₗ[R] M₁；k i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrixAlgEquiv_apply`：LinearMap.toMatrixAlgEquiv_apply (f : 
M₁ ->ₗ[R] M₁) (i j : n) : LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j
)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.reindexRange_self`：reindexRange_self (i : ι) (h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.reindexRange_repr`：reindexRange_repr (x : M) (i : ι) (h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ →ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f
        ⟨v₁ k, Set.mem_range_self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i := by
  simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]
/-
**LinearMap.toMatrixAlgEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_comp (f g : M₁ ->ₗ[R] M₁) : LinearMap.toMatrixA
lgEquiv v₁ (f.comp g) = LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgE
quiv v₁ g
参数：f g : M₁ ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_one`：LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v
₁ 1 = 1
· 使用定理 `LinearMap.toMatrix_mul`：LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) : Li
nearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix
 v₁ v₁ g
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrixAlgEquiv_comp (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]
/-
**LinearMap.toMatrixAlgEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixAlgEquiv_mul (f g : M₁ ->ₗ[R] M₁) : LinearMap.toMatrixAl
gEquiv v₁ (f * g) = LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv
 v₁ g
参数：f g : M₁ ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.toMatrixAlgEquiv_comp`：LinearMap.toMatrixAlgEquiv_comp (f g : 
M₁ ->ₗ[R] M₁) : LinearMap.toMatrixAlgEquiv v₁ (f.comp g) = LinearMap.toMatrixAlg
Equiv v₁ f * LinearMa…
-/
theorem LinearMap.toMatrixAlgEquiv_mul (f g : M₁ →ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  rw [Module.End.mul_eq_comp, LinearMap.toMatrixAlgEquiv_comp v₁ f g]
/-
**Matrix.toLinAlgEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) : Matrix.toLinAlgEquiv v₁ (A
 * B) = (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B)
参数：A B : Matrix n n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
-/
theorem Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A * B) =
      (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) := by
  convert! Matrix.toLin_mul v₁ v₁ v₁ A B

@[simp]
/-
**LinearMap.isUnit_toMatrix_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isUnit_toMatrix_iff {f : M₁ ->ₗ[R] M₁} : IsUnit (f.toMatrix v₁ v
₁) ↔ IsUnit f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem LinearMap.isUnit_toMatrix_iff {f : M₁ →ₗ[R] M₁} : IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

@[simp]
/-
**Matrix.isUnit_toLin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isUnit_toLin_iff {M : Matrix n n R} : IsUnit (M.toLin v₁ v₁) ↔ IsUn
it M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
-/
theorem Matrix.isUnit_toLin_iff {M : Matrix n n R} : IsUnit (M.toLin v₁ v₁) ↔ IsUnit M :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _).symm M

@[simp]
/-
**Matrix.toLin_finTwoProd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) : Matrix.toLin (Ba
sis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x = (a * x.fst + b * x.snd
, c * x.fst + d * x.snd)
参数：a b c d : R；x : R × R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_apply`：Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v
 : M₁) : Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.finTwoProd_zero`：finTwoProd_zero (R : Type*) [Semiring R] :
 Basis.finTwoProd R 0 = (1, 0)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Module.Basis.finTwoProd_one`：finTwoProd_one (R : Type*) [Semiring R] : B
asis.finTwoProd R 1 = (0, 1)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) := by
  simp [Matrix.toLin_apply, Matrix.mulVec, dotProduct]
/-
**Matrix.toLin_finTwoProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_finTwoProd (a b c d : R) : Matrix.toLin (Basis.finTwoProd R) 
(Basis.finTwoProd R) !![a, b; c, d] = (a • LinearMap.fst R R R + b • LinearMap.s
nd R R R).prod (c • LinearMap.fst R R R + d • LinearMap.snd R R R)
参数：a b c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.toLin_finTwoProd_apply`：Matrix.toLin_finTwoProd_apply (a b c d : 
R) (x : R × R) : Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b;
 c, d] x = (a * x.f…
-/
theorem Matrix.toLin_finTwoProd (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).prod
        (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
  LinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _

@[simp]
/-
**toMatrix_distrib_mul_action_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMatrix_distrib_mul_action_toLinearMap (x : R) : LinearMap.toMatrix v₁ v₁
 (DistribSMul.toLinearMap R M₁ x) = Matrix.diagonal fun _ => x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single_one`：smul_single_one [MulZeroOneClass R] (a : α) (b 
: R) : b • single a (1 : R) = single a b
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `Matrix.diagonal_apply`：diagonal_apply [Zero α] (d : n -> α) (i j) : diag
onal d i j = if i = j then d i else 0
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
theorem toMatrix_distrib_mul_action_toLinearMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (DistribSMul.toLinearMap R M₁ x) =
    Matrix.diagonal fun _ ↦ x := by
  ext
  rw [LinearMap.toMatrix_apply, DistribSMul.toLinearMap_apply, map_smul,
    Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_pi_single, Matrix.diagonal_apply,
    Pi.single_apply]
/-
**LinearMap.toMatrix_prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_prodMap [DecidableEq m] [DecidableEq (n oplus m)] (φ₁ :
 Module.End R M₁) (φ₂ : Module.End R M₂) : toMatrix (v₁.prod v₂) (v₁.prod v₂) (φ
₁.prodMap φ₂) = Matrix.fromBlocks (toMatrix v₁ v₁ φ₁) 0 0 (toMatrix v₂ v₂ φ₂)
参数：n oplus m；φ₁ : Module.End R M₁；φ₂ : Module.End R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.prod_apply`：prod_apply (i) : b.prod b' i = Sum.elim (Linear
Map.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma LinearMap.toMatrix_prodMap [DecidableEq m] [DecidableEq (n ⊕ m)]
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) :
    toMatrix (v₁.prod v₂) (v₁.prod v₂) (φ₁.prodMap φ₂) =
      Matrix.fromBlocks (toMatrix v₁ v₁ φ₁) 0 0 (toMatrix v₂ v₂ φ₂) := by
  ext (i | i) (j | j) <;> simp [toMatrix]

end ToMatrix

namespace Algebra

section Lmul

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

/-
**Algebra.toMatrix_lmul'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toMatrix_lmul' (x : S) (i j) : LinearMap.toMatrix b b (lmul R S x) i j = b
.repr (x * b j) i
参数：x : S；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply'`：LinearMap.toMatrix_apply' (f : M₁ ->ₗ[R] M₂) 
(i : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_lmul' (x : S) (i j) :
    LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']

@[simp]
/-
**Algebra.toMatrix_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toMatrix_lsmul (x : R) : LinearMap.toMatrix b b (Algebra.lsmul R R S x) = 
Matrix.diagonal fun _ => x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toMatrix_distrib_mul_action_toLinearMap`：toMatrix_distrib_mul_action_toL
inearMap (x : R) : LinearMap.toMatrix v₁ v₁ (DistribSMul.toLinearMap R M₁ x) = M
atrix.diagonal fun _ => x
-/
theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R R S x) = Matrix.diagonal fun _ ↦ x :=
  toMatrix_distrib_mul_action_toLinearMap b x

/-- `leftMulMatrix b x` is the matrix corresponding to the linear map `fun y ↦ x * y`.

`leftMulMatrix_eq_repr_mul` gives a formula for the entries of `leftMulMatrix`.

This definition is useful for doing (more) explicit computations with `LinearMap.mulLeft`,
such as the trace form or norm map for algebras.
-/
/-
**Algebra.leftMulMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：leftMulMatrix : S ->ₐ[R] Matrix m m R where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
`leftMulMatrix b x` is the matrix corresponding to the linear map `fun y ↦ x * y
`.

`leftMulMatrix_eq_repr_mul` gives a formula for the entries of `leftMulMatrix`.

This definition is useful for doing (more) explicit computations with `LinearMap
.mulLeft`,
such as the trace form or norm map for algebras.
-/
noncomputable def leftMulMatrix : S →ₐ[R] Matrix m m R where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [map_zero, map_zero]
  map_one' := by
    rw [map_one, LinearMap.toMatrix_one]
  map_add' x y := by
    rw [map_add, map_add]
  map_mul' x y := by
    rw [map_mul, LinearMap.toMatrix_mul]
  commutes' r := by
    ext
    rw [lmul_algebraMap, toMatrix_lsmul, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self_apply]
/-
**Algebra.leftMulMatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (
lmul R S x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl
/-
**Algebra.leftMulMatrix_eq_repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (
x * b j) i
参数：x : S；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.leftMulMatrix_apply`：leftMulMatrix_apply (x : S) : leftMulMatrix
 b x = LinearMap.toMatrix b b (lmul R S x)
· 使用定理 `Algebra.toMatrix_lmul'`：toMatrix_lmul' (x : S) (i j) : LinearMap.toMatri
x b b (lmul R S x) i j = b.repr (x * b j) i
-/
theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply, toMatrix_lmul' b x i j]
/-
**Algebra.leftMulMatrix_mulVec_repr** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：leftMulMatrix_mulVec_repr (x y : S) : leftMulMatrix b x *ᵥ b.repr y = b.re
pr (x * y)
参数：x y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix_mulVec_repr`：LinearMap.toMatrix_mulVec_repr (f : M₁ -
>ₗ[R] M₂) (x : M₁) : LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem leftMulMatrix_mulVec_repr (x y : S) :
    leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y) :=
  (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

@[simp]
/-
**Algebra.toMatrix_lmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toMatrix_lmul_eq (x : S) : LinearMap.toMatrix b b (LinearMap.mulLeft R x) 
= leftMulMatrix b x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toMatrix_lmul_eq (x : S) :
    LinearMap.toMatrix b b (LinearMap.mulLeft R x) = leftMulMatrix b x :=
  rfl
/-
**Algebra.leftMulMatrix_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：leftMulMatrix_injective : Function.Injective (leftMulMatrix b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem leftMulMatrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h ↦
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

@[simp]
/-
**Algebra.smul_leftMulMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：smul_leftMulMatrix {G} [Group G] [DistribMulAction G S] [SMulCommClass G R
 S] [SMulCommClass G S S] (g : G) (x) : leftMulMatrix (g • b) x = leftMulMatrix 
b x
参数：g : G；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribMulAction.toLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
4} (M : Type u_5) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _ro
ot_.Module R M] [inst_3 : Group…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_leftMulMatrix {G} [Group G] [DistribMulAction G S]
    [SMulCommClass G R S] [SMulCommClass G S S] (g : G) (x) :
    leftMulMatrix (g • b) x = leftMulMatrix b x := by
  ext
  simp_rw [leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Basis.repr_smul, Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

variable {A M n : Type*} [Fintype n] [DecidableEq n]
  [CommSemiring A] [AddCommMonoid M] [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M]
  (bA : Basis m R A) (bM : Basis n A M)

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra._root_.LinearMap.restrictScalars_toMatrix** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.restrictScalars_toMatrix (f : M →ₗ[A] M) :
    (f.restrictScalars R).toMatrix (bA.smulTower' bM) (bA.smulTower' bM) =
      ((f.toMatrix bM bM).map (leftMulMatrix bA)).comp _ _ _ _ _ := by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply, mul_comm]

end Lmul

section LmulTower

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (b : Basis m R S) (c : Basis n S T)

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.smulTower_leftMulMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：smulTower_leftMulMatrix (x) (ik jk) : leftMulMatrix (b.smulTower c) x ik j
k = leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1
参数：x；ik jk。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.smulTower_apply`：smulTower_apply (ij) : (b.smulTower c) ij 
= b ij.1 • c ij.2
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Module.Basis.smulTower_repr`：smulTower_repr (x ij) : (b.smulTower c).rep
r x ij = b.repr (c.repr x ij.2) ij.1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulTower_leftMulMatrix (x) (ik jk) :
    leftMulMatrix (b.smulTower c) x ik jk =
      leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smulTower_apply,
    Basis.smulTower_repr, Finsupp.smul_apply, smul_eq_mul, map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']
/-
**Algebra.smulTower_leftMulMatrix_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`
。
形式化陈述：smulTower_leftMulMatrix_algebraMap (x : S) : leftMulMatrix (b.smulTower c)
 (algebraMap _ _ x) = blockDiagonal fun _ => leftMulMatrix b x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smulTower_leftMulMatrix`：smulTower_leftMulMatrix (x) (ik jk) : l
eftMulMatrix (b.smulTower c) x ik jk = leftMulMatrix b (leftMulMatrix c x ik.2 j
k.2) ik.1 jk.1
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Matrix.blockDiagonal_apply`：blockDiagonal_apply (M : o -> Matrix m n α) 
(ik jk) : blockDiagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0
· 使用定理 `Matrix.algebraMap_matrix_apply`：algebraMap_matrix_apply {r : R} {i j : n
} : algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
-/
theorem smulTower_leftMulMatrix_algebraMap (x : S) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagonal fun _ ↦ leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smulTower_leftMulMatrix, AlgHom.commutes, blockDiagonal_apply, algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp
/-
**Algebra.smulTower_leftMulMatrix_algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra`。
形式化陈述：smulTower_leftMulMatrix_algebraMap_eq (x : S) (i j k) : leftMulMatrix (b.s
mulTower c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j
参数：x : S；i j k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smulTower_leftMulMatrix_algebraMap`：smulTower_leftMulMatrix_alge
braMap (x : S) : leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagona
l fun _ => leftMulMatrix b x
· 使用定理 `Matrix.blockDiagonal_apply_eq`：blockDiagonal_apply_eq (M : o -> Matrix m
 n α) (i j k) : blockDiagonal M (i, k) (j, k) = M k i j
-/
theorem smulTower_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply_eq]
/-
**Algebra.smulTower_leftMulMatrix_algebraMap_ne** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra`。
形式化陈述：smulTower_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k != k') :
 leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k') = 0
参数：x : S；i j；h : k != k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smulTower_leftMulMatrix_algebraMap`：smulTower_leftMulMatrix_alge
braMap (x : S) : leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagona
l fun _ => leftMulMatrix b x
· 使用定理 `Matrix.blockDiagonal_apply_ne`：blockDiagonal_apply_ne (M : o -> Matrix m
 n α) (i j) {k k'} (h : k != k') : blockDiagonal M (i, k) (j, k') = 0
-/
theorem smulTower_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k ≠ k') :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply_ne _ _ _ h]

end LmulTower

end Algebra

section

variable {R S : Type*} [CommSemiring R] {n : Type*} [DecidableEq n]
variable {M M₁ M₂ : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [Semiring S] [Module S M₁] [Module S M₂] [SMulCommClass S R M₁] [SMulCommClass S R M₂]
variable [SMul R S] [IsScalarTower R S M₁] [IsScalarTower R S M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
/-
**algEquivMatrix'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algEquivMatrix' [Fintype n] : Module.End R (n -> R) ≃ₐ[R] Matrix n n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between linear endomorphisms of finite free modules and 
square matrices
is compatible with the algebra structures.
-/
def algEquivMatrix' [Fintype n] : Module.End R (n → R) ≃ₐ[R] Matrix n n R :=
  LinearMap.toMatrixAlgEquiv'

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
/-
**algEquivMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix
 n n R
参数：h : Basis n R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A basis of a module induces an equivalence of algebras from the endomorphisms of
 the module to
square matrices.
-/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  (h.equivFun.conjAlgEquiv R).trans algEquivMatrix'

end

namespace Module.Basis

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module R M₁] [Module R M₂]
variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]
variable [DecidableEq ι] [DecidableEq ι₁]
variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- The standard basis of the space linear maps between two modules
induced by a basis of the domain and codomain.

If `M₁` and `M₂` are modules with basis `b₁` and `b₂` respectively indexed
by finite types `ι₁` and `ι₂`,
then `Basis.linearMap b₁ b₂` is the basis of `M₁ →ₗ[R] M₂` indexed by `ι₂ × ι₁`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
/-
**Module.Basis.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：linearMap (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) : Basis (ι₂ × ι₁) R (M
₁ ->ₗ[R] M₂)
参数：b₁ : Basis ι₁ R M₁；b₂ : Basis ι₂ R M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
def linearMap (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) :
    Basis (ι₂ × ι₁) R (M₁ →ₗ[R] M₂) :=
  (Matrix.stdBasis R ι₂ ι₁).map (LinearMap.toMatrix b₁ b₂).symm

attribute [simp] linearMap_repr_apply
/-
**Module.Basis.linearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：linearMap_apply (ij : ι₂ × ι₁) : (b₁.linearMap b₂ ij) = (Matrix.toLin b₁ b
₂) (Matrix.stdBasis R ι₂ ι₁ ij)
参数：ij : ι₂ × ι₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearMap_apply (ij : ι₂ × ι₁) :
    (b₁.linearMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij) := by
  simp [linearMap]
/-
**Module.Basis.linearMap_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：linearMap_apply_apply (ij : ι₂ × ι₁) (k : ι₁) : (b₁.linearMap b₂ ij) (b₁ k
) = if ij.2 = k then b₂ ij.1 else 0
参数：ij : ι₂ × ι₁；k : ι₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Basis.linearMap_apply`：linearMap_apply (ij : ι₂ × ι₁) : (b₁.linea
rMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij)
· 使用定理 `Matrix.stdBasis_eq_single`：stdBasis_eq_single (i : m) (j : n) [Decidable
Eq m] [DecidableEq n] : stdBasis R m n (i, j) = single i j (1 : R)
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearMap_apply_apply (ij : ι₂ × ι₁) (k : ι₁) :
    (b₁.linearMap b₂ ij) (b₁ k) = if ij.2 = k then b₂ ij.1 else 0 := by
  have := Classical.decEq ι₂
  rw [linearMap_apply, Matrix.stdBasis_eq_single, Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The standard basis of the endomorphism algebra of a module
induced by a basis of the module.

If `M` is a module with basis `b` indexed by a finite type `ι`,
then `Basis.end b` is the basis of `Module.End R M` indexed by `ι × ι`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
/-
**Module.Basis.** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev «end» (b : Basis ι R M) : Basis (ι × ι) R (Module.End R M) :=
  b.linearMap b
/-
**Module.Basis.end_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：end_apply (ij : ι × ι) : (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis 
R ι ι ij)
参数：ij : ι × ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Basis.linearMap_apply`：linearMap_apply (ij : ι₂ × ι₁) : (b₁.linea
rMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij)
-/
lemma end_apply (ij : ι × ι) : (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij) :=
  linearMap_apply b b ij
/-
**Module.Basis.end_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`。
形式化陈述：end_apply_apply (ij : ι × ι) (k : ι) : (b.end ij) (b k) = if ij.2 = k then
 b ij.1 else 0
参数：ij : ι × ι；k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Basis.linearMap_apply_apply`：linearMap_apply_apply (ij : ι₂ × ι₁)
 (k : ι₁) : (b₁.linearMap b₂ ij) (b₁ k) = if ij.2 = k then b₂ ij.1 else 0
-/
lemma end_apply_apply (ij : ι × ι) (k : ι) : (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0 :=
  linearMap_apply_apply b b ij k
/-
**Module.Basis.lie_end_of_apply_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis`
。
形式化陈述：lie_end_of_apply_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Modu
le R M] (b : Basis ι R M) (a : ι -> R) (s : Module.End R M) (hs : forall k, s (b
 k) = a k • b k) (i j : ι) : ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j)
参数：b : Basis ι R M；a : ι -> R；s : Module.End R M；hs : forall k, s (b k) = a k • 
b k；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Module.Basis.end_apply_apply`：end_apply_apply (ij : ι × ι) (k : ι) : (b.
end ij) (b k) = if ij.2 = k then b ij.1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma lie_end_of_apply_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) (a : ι → R) (s : Module.End R M)
    (hs : ∀ k, s (b k) = a k • b k) (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  refine b.ext fun k ↦ ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, End.mul_apply, LinearMap.smul_apply,
    Basis.end_apply_apply, smul_ite, smul_zero, sub_smul]
  rcases eq_or_ne j k with rfl | hjk
  · simp [hs, Basis.end_apply_apply]
  · simp [hs, Basis.end_apply_apply, hjk]

end Module.Basis

section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

set_option backward.isDefEq.respectTransparency false in
/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `A`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simp]
/-
**endVecRingEquivMatrixEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：endVecRingEquivMatrixEnd : Module.End A (ι -> M) ≃+* Matrix ι ι (Module.En
d A M) where toFun f i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-
matrix whose entries
are `A`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))`
 defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
def endVecRingEquivMatrixEnd :
    Module.End A (ι → M) ≃+* Matrix ι ι (Module.End A M) where
  toFun f i j :=
  { toFun := fun x ↦ f (Pi.single j x) i
    map_add' := fun x y ↦ by simp [Pi.single_add]
    map_smul' := fun x y ↦ by simp [Pi.single_smul] }
  invFun m :=
  { toFun := fun x i ↦ ∑ j, m i j (x j)
    map_add' := by intros; ext; simp [Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp [Finset.smul_sum] }
  left_inv f := by
    ext i x j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coe_comp, coe_single, Function.comp_apply]
    rw [← Fintype.sum_apply, ← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  right_inv m := by ext; simp [Pi.single_apply, apply_ite]
  map_mul' f g := by
    ext
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
      LinearMap.coe_sum, Finset.sum_apply]
    rw [← Fintype.sum_apply, ← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  map_add' f g := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `R`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simps!]
/-
**endVecAlgEquivMatrixEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：endVecAlgEquivMatrixEnd : Module.End A (ι -> M) ≃ₐ[R] Matrix ι ι (Module.E
nd A M) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-
matrix whose entries
are `R`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))`
 defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
def endVecAlgEquivMatrixEnd :
    Module.End A (ι → M) ≃ₐ[R] Matrix ι ι (Module.End A M) where
  __ := endVecRingEquivMatrixEnd ι A M
  commutes' r := by
    ext
    simp only [endVecRingEquivMatrixEnd, RingEquiv.toEquiv_eq_coe, Module.algebraMap_end_eq_smul_id,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      LinearMap.smul_apply, id_coe, id_eq, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      LinearMap.coe_mk, AddHom.coe_mk, algebraMap_matrix_apply]
    split_ifs <;> rfl

variable {A ι}

/-- A matrix algebra is isomorphic to the opposite of an endomorphism algebra. -/
/-
**matrixAlgEquivEndVecMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：matrixAlgEquivEndVecMulOpposite : Matrix ι ι A ≃ₐ[R] (Module.End A (ι -> A
))ᵐᵒᵖ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
A matrix algebra is isomorphic to the opposite of an endomorphism algebra.
-/
def matrixAlgEquivEndVecMulOpposite : Matrix ι ι A ≃ₐ[R] (Module.End A (ι → A))ᵐᵒᵖ :=
  .trans (.opOp R _) <| .op <| .trans (.symm .mopMatrix) <| .trans
    (.mapMatrix <| .moduleEndSelf _) <| .symm <| endVecAlgEquivMatrixEnd ..

/-- A matrix ring is isomorphic to the opposite of an endomorphism ring. -/
/-
**matrixRingEquivEndVecMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：matrixRingEquivEndVecMulOpposite : Matrix ι ι A ≃+* (Module.End A (ι -> A)
)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix ring is isomorphic to the opposite of an endomorphism ring.
-/
def matrixRingEquivEndVecMulOpposite : Matrix ι ι A ≃+* (Module.End A (ι → A))ᵐᵒᵖ :=
  (matrixAlgEquivEndVecMulOpposite ℕ).toRingEquiv
/-
**isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd : IsStablyFiniteRi
ng A ↔ forall n, IsDedekindFiniteMonoid (Module.End A (Fin n -> A))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulEquivClass.isDedekindFiniteMonoid_iff`：∀ {F : Type u_1} {α : Type u_2
} {β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulOne α] [inst_2 : MulOne β
]   [MulEquivClass F α β] [One…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd :
    IsStablyFiniteRing A ↔ ∀ n, IsDedekindFiniteMonoid (Module.End A (Fin n → A)) := by
  simp_rw [isStablyFiniteRing_iff, MulEquivClass.isDedekindFiniteMonoid_iff
    (matrixRingEquivEndVecMulOpposite (ι := Fin _) (A := A)),
    MulOpposite.isDedekindFiniteMonoid_iff]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ι) [Finite ι] [IsStablyFiniteRing A] : IsStablyFiniteRing (Module.End A (ι → A)) := by
  have := Fintype.ofFinite ι
  classical rw [← MulOpposite.isStablyFiniteRing_iff,
    ← RingEquiv.isStablyFiniteRing_iff (matrixRingEquivEndVecMulOpposite (ι := ι) (A := A))]
  infer_instance

open Function
/-
**isStablyFiniteRing_iff_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStablyFiniteRing_iff_injective_of_surjective : IsStablyFiniteRing A ↔ fo
rall n (f : Module.End A (Fin n -> A)), Surjective f -> Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `LinearEquiv.symm_comp`：symm_comp : e.symm.toLinearMap ∘ₛₗ e.toLinearMap 
= LinearMap.id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
-/
theorem isStablyFiniteRing_iff_injective_of_surjective :
    IsStablyFiniteRing A ↔ ∀ n (f : Module.End A (Fin n → A)), Surjective f → Injective f := by
  simp_rw [isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isDedekindFiniteMonoid_iff]
  refine ⟨fun h n f surj ↦ ?_, fun h n f g eq ↦ ?_⟩
  · have ⟨g, eq⟩ := Module.projective_lifting_property _ .id surj
    exact injective_of_comp_eq_id _ _ (h _ eq)
  · have surj := surjective_of_comp_eq_id _ _ eq
    have := (LinearEquiv.ofBijective f ⟨h _ _ surj, surj⟩).symm_comp
    rwa [← left_inv_eq_right_inv this eq]

/-- `Module.End.injective_of_surjective` is the more general version for finite free `A`-modules
not necessarily of the form `Fin n → A`, but this version requires less imports. -/
/-
**Module.End.injective_of_surjective_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.injective_of_surjective_fin [IsStablyFiniteRing A] {n} {f : Mod
ule.End A (Fin n -> A)} (hf : Surjective f) : Injective f
参数：Fin n -> A；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStablyFiniteRing_iff_injective_of_surjective`：isStablyFiniteRing_iff_i
njective_of_surjective : IsStablyFiniteRing A ↔ forall n (f : Module.End A (Fin 
n -> A)), Surjective f -> Injective …

--- 原说明 ---
`Module.End.injective_of_surjective` is the more general version for finite free
 `A`-modules
not necessarily of the form `Fin n → A`, but this version requires less imports.
-/
theorem Module.End.injective_of_surjective_fin [IsStablyFiniteRing A] {n}
    {f : Module.End A (Fin n → A)} (hf : Surjective f) : Injective f :=
  isStablyFiniteRing_iff_injective_of_surjective.mp ‹_› n f hf

end

