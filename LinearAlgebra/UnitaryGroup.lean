/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Unitary Group

This file defines elements of the unitary group `Matrix.unitaryGroup n α`, where `α` is a
`StarRing`. This consists of all `n` by `n` matrices with entries in `α` such that the
star-transpose is its inverse. In addition, we define the group structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n R`, where `R` is a `CommRing`.

## Main Definitions

* `Matrix.unitaryGroup` is the submonoid of matrices where the star-transpose is the inverse; the
  group structure (under multiplication) is inherited from a more general `unitary` construction.
* `Matrix.UnitaryGroup.embeddingGL` is the embedding `Matrix.unitaryGroup n α → GLₙ(α)`, where
  `GLₙ(α)` is `LinearMap.GeneralLinearGroup α (n → α)`.
* `Matrix.orthogonalGroup` is the submonoid of matrices where the transpose is the inverse.

## References

* https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/

@[expose] public section


universe u v

namespace Matrix

open LinearMap Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]
variable (α : Type v) [CommRing α] [StarRing α]

/-- `Matrix.unitaryGroup n` is the group of `n` by `n` matrices where the star-transpose is the
inverse.
-/
/-
**Matrix.unitaryGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：unitaryGroup : Submonoid (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.unitaryGroup n` is the group of `n` by `n` matrices where the star-trans
pose is the
inverse.
-/
abbrev unitaryGroup : Submonoid (Matrix n n α) :=
  unitary (Matrix n n α)

-- the group and star structure is already defined in another file
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Group (unitaryGroup n α) := inferInstance
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : StarMul (unitaryGroup n α) := inferInstance

end

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

/-
**Matrix.mem_unitaryGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_unitaryGroup_iff : A in Matrix.unitaryGroup n α ↔ A * star A = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
-/
theorem mem_unitaryGroup_iff : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA
/-
**Matrix.mem_unitaryGroup_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_unitaryGroup_iff' : A in Matrix.unitaryGroup n α ↔ star A * A = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_comm`：∀ {M : Type u_2} [inst : MulOne M] [IsDedekindFiniteMon
oid M] {a b : M}, a * b = 1 ↔ b * a = 1
· 使用定理 `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing`：∀ (n : Type u_11)
 (R : Type u_12) [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : MulOne R]
   [inst_3 : AddCommMonoid R] [IsStablyFini…
· 使用定理 `Matrix.instIsStablyFiniteRingOfCommSemiring`：∀ {R : Type u_3} [inst : Co
mmSemiring R], IsStablyFiniteRing R
-/
theorem mem_unitaryGroup_iff' : A ∈ Matrix.unitaryGroup n α ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA
/-
**Matrix.det_of_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_of_mem_unitary {A : Matrix n n α} (hA : A in Matrix.unitaryGroup n α) 
: A.det in unitary α
参数：hA : A in Matrix.unitaryGroup n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem det_of_mem_unitary {A : Matrix n n α} (hA : A ∈ Matrix.unitaryGroup n α) :
    A.det ∈ unitary α := by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

open scoped Kronecker in
/-- The kronecker product of two unitary matrices is unitary.

This is stated for `unitary` instead of `unitaryGroup` as it holds even for
non-commutative coefficients. -/
/-
**Matrix.kronecker_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kronecker_mem_unitary {R m : Type*} [Semiring R] [StarRing R] [Fintype m] 
[DecidableEq m] {U₁ : Matrix n n R} {U₂ : Matrix m m R} (hU₁ : U₁ in unitary (Ma
trix n n R)) (hU₂ : U₂ in unitary (Matrix m m R)) : U₁ otimesₖ U₂ in unitary (Ma
trix (n × m) (n × m) R)
参数：hU₁ : U₁ in unitary (Matrix n n R)；hU₂ : U₂ in unitary (Matrix m m R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_kronecker'`：conjTranspose_kronecker' [Mul R] [StarM
ul R] (x : Matrix l m R) (y : Matrix n p R) : (x otimesₖ y)ᴴ = (yᴴ otimesₖ xᴴ).s
ubmatrix Prod.swap Pr…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι) (f g : ι → M),   (∑ x ∈ 
s, if p th…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The kronecker product of two unitary matrices is unitary.

This is stated for `unitary` instead of `unitaryGroup` as it holds even for
non-commutative coefficients.
-/
theorem kronecker_mem_unitary {R m : Type*} [Semiring R] [StarRing R] [Fintype m]
    [DecidableEq m] {U₁ : Matrix n n R} {U₂ : Matrix m m R}
    (hU₁ : U₁ ∈ unitary (Matrix n n R)) (hU₂ : U₂ ∈ unitary (Matrix m m R)) :
    U₁ ⊗ₖ U₂ ∈ unitary (Matrix (n × m) (n × m) R) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₁.1, Matrix.one_apply,
      mul_boole, ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₂.1,
      Matrix.one_apply, Finset.sum_const_zero, ← ite_and, Prod.eq_iff_fst_eq_snd_eq]
  · simp_rw [mul_assoc _ _ (star U₂ _ _), ← Finset.univ_product_univ, Finset.sum_product,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₂.2, Matrix.one_apply, mul_boole,
      ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₁.2, Matrix.one_apply,
      Finset.sum_const_zero, ← ite_and, and_comm, Prod.eq_iff_fst_eq_snd_eq]

section TensorProduct
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [StarRing A] [StarRing B] [StarRing R] [StarModule R A] [StarModule R B]

open scoped TensorProduct Kronecker

/-
**Matrix._root_.Unitary.tmul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Unitary.tmul_mem {U : A} {V : B} (hU : U ∈ unitary A) (hV : V ∈ unitary B) :
    U ⊗ₜ[R] V ∈ unitary (A ⊗[R] B) := by
  simp [Unitary.mem_iff, hU, hV, Algebra.TensorProduct.one_def]
/-
**Matrix.kroneckerTMul_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：kroneckerTMul_mem_unitary {m : Type*} [Fintype m] [DecidableEq m] {U : Mat
rix m m A} {V : Matrix n n B} (hU : U in unitary (Matrix m m A)) (hV : V in unit
ary (Matrix n n B)) : U otimesₖₜ[R] V in unitary (Matrix (m × n) (m × n) (A otim
es[R] B))
参数：hU : U in unitary (Matrix m m A)；hV : V in unitary (Matrix n n B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_kroneckerTMul`：conjTranspose_kroneckerTMul [StarRin
g R] [StarAddMonoid α] [StarAddMonoid β] [StarModule R α] [StarModule R β] (x : 
Matrix l m α) (y : Matri…
· 使用定理 `Matrix.one_kroneckerTMul_one`：one_kroneckerTMul_one [AddCommMonoidWithOn
e α] [AddCommMonoidWithOne β] [Module R α] [Module R β] [DecidableEq m] [Decidab
leEq n] : (1 : Mat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem kroneckerTMul_mem_unitary {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m A}
    {V : Matrix n n B} (hU : U ∈ unitary (Matrix m m A)) (hV : V ∈ unitary (Matrix n n B)) :
    U ⊗ₖₜ[R] V ∈ unitary (Matrix (m × n) (m × n) (A ⊗[R] B)) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose] at hU hV ⊢
  simp [conjTranspose_kroneckerTMul, ← mul_kroneckerTMul_mul, hU, hV]

end TensorProduct

namespace UnitaryGroup

/-
**Matrix.UnitaryGroup.coeMatrix** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：coeMatrix : Coe (unitaryGroup n α) (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeMatrix : Coe (unitaryGroup n α) (Matrix n n α) :=
  ⟨Subtype.val⟩
/-
**Matrix.UnitaryGroup.coeFun** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：coeFun : CoeFun (unitaryGroup n α) fun _ => n -> n -> α where coe A
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeFun : CoeFun (unitaryGroup n α) fun _ => n → n → α where coe A := A.val

/-- `Matrix.UnitaryGroup.toLin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `Matrix.unitaryGroup n` is defined, we show in
`Matrix.UnitaryGroup.toLinearEquiv` that this gives a linear equivalence.
-/
/-
**Matrix.UnitaryGroup.toLin'** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：toLin' (A : unitaryGroup n α)
参数：A : unitaryGroup n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.UnitaryGroup.toLin' A` is matrix multiplication of vectors by `A`, as a 
linear map.

After the group structure on `Matrix.unitaryGroup n` is defined, we show in
`Matrix.UnitaryGroup.toLinearEquiv` that this gives a linear equivalence.
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1
/-
**Matrix.UnitaryGroup.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：ext_iff (A B : unitaryGroup n α) : A = B ↔ forall i j, A i j = B i j
参数：A B : unitaryGroup n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]
/-
**Matrix.UnitaryGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：ext (A B : unitaryGroup n α) : (forall i j, A i j = B i j) -> A = B
参数：A B : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.UnitaryGroup.ext_iff`：ext_iff (A B : unitaryGroup n α) : A = B ↔ 
forall i j, A i j = B i j
-/
theorem ext (A B : unitaryGroup n α) : (∀ i j, A i j = B i j) → A = B :=
  (UnitaryGroup.ext_iff A B).mpr
/-
**Matrix.UnitaryGroup.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGro
up`。
形式化陈述：star_mul_self (A : unitaryGroup n α) : star A.1 * A.1 = 1
参数：A : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem star_mul_self (A : unitaryGroup n α) : star A.1 * A.1 = 1 :=
  A.2.1

@[simp]
/-
**Matrix.UnitaryGroup.det_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`
。
形式化陈述：det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det
参数：A : unitaryGroup n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp <| (Unitary.toUnits A).isUnit

section CoeLemmas

variable (A B : unitaryGroup n α)

/-
**Matrix.UnitaryGroup.inv_val** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A : ↥(Matrix.unitaryGroup n α)), ↑A
⁻¹ = star ↑A
参数：A : ↥(Matrix.unitaryGroup n α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) := rfl
/-
**Matrix.UnitaryGroup.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A : ↥(Matrix.unitaryGroup n α)), ↑A
⁻¹ = star ↑A
参数：A : ↥(Matrix.unitaryGroup n α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) := rfl
/-
**Matrix.UnitaryGroup.mul_val** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A B : ↥(Matrix.unitaryGroup n α)), 
↑(A * B) = ↑A * ↑B
参数：A B : ↥(Matrix.unitaryGroup n α)；A * B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mul_val : ↑(A * B) = A.1 * B.1 := rfl
/-
**Matrix.UnitaryGroup.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A B : ↥(Matrix.unitaryGroup n α)), 
↑(A * B) = ↑A * ↑B
参数：A B : ↥(Matrix.unitaryGroup n α)；A * B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mul_apply : ⇑(A * B) = A.1 * B.1 := rfl
/-
**Matrix.UnitaryGroup.one_val** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α],   ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem one_val : ↑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl
/-
**Matrix.UnitaryGroup.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α],   ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl

@[simp]
/-
**Matrix.UnitaryGroup.toLin'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`
。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A B : ↥(Matrix.unitaryGroup n α)), 
  Matrix.UnitaryGroup.toLin' (A * B) = Matrix.UnitaryGroup.toLin' A ∘ₗ Matrix.Un
itaryGroup.toLin' B
参数：A B : ↥(Matrix.unitaryGroup n α)；A * B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
-/
theorem toLin'_mul : toLin' (A * B) = (toLin' A).comp (toLin' B) :=
  Matrix.toLin'_mul A.1 B.1

@[simp]
/-
**Matrix.UnitaryGroup.toLin'_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`
。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α],   Matrix.UnitaryGroup.toLin' 1 = Line
arMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.toLin'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {n : Type u_
5} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   Matrix.toLin' 1 = LinearMap.
id
-/
theorem toLin'_one : toLin' (1 : unitaryGroup n α) = LinearMap.id :=
  Matrix.toLin'_one

end CoeLemmas

-- TODO: redefine `toGL`/`embeddingGL` as in the following example,
-- so that we can get `toLinearEquiv` from `GeneralLinearGroup.toLinearEquiv`
/-
**Matrix.UnitaryGroup.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix.UnitaryGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  .toHomUnits ⟨⟨toLin', toLin'_one⟩, toLin'_mul⟩

/-- `Matrix.unitaryGroup.toLinearEquiv A` is matrix multiplication of vectors by `A`, as a linear
equivalence. -/
/-
**Matrix.UnitaryGroup.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGro
up`。
形式化陈述：toLinearEquiv (A : unitaryGroup n α) : (n -> α) ≃ₗ[α] n -> α
参数：A : unitaryGroup n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.unitaryGroup.toLinearEquiv A` is matrix multiplication of vectors by `A`
, as a linear
equivalence.
-/
def toLinearEquiv (A : unitaryGroup n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [inv_mul_cancel, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_inv_cancel, toLin'_one, id_apply] }

/-- `Matrix.unitaryGroup.toGL` is the map from the unitary group to the general linear group -/
/-
**Matrix.UnitaryGroup.toGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n -> α)
参数：A : unitaryGroup n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.unitaryGroup.toGL` is the map from the unitary group to the general line
ar group
-/
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n → α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)
/-
**Matrix.UnitaryGroup.coe_toGL** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A
参数：A : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A := rfl

@[simp]
/-
**Matrix.UnitaryGroup.toGL_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：toGL_one : toGL (1 : unitaryGroup n α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.UnitaryGroup.toLin'_one`：∀ {n : Type u} [inst : DecidableEq n] [i
nst_1 : Fintype n] {α : Type v} [inst_2 : CommRing α] [inst_3 : StarRing α],   M
atrix.UnitaryGroup.t…
-/
theorem toGL_one : toGL (1 : unitaryGroup n α) = 1 := Units.ext <| by
  simp only [coe_toGL, toLin'_one]
  rfl

@[simp]
/-
**Matrix.UnitaryGroup.toGL_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：toGL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B
参数：A B : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.UnitaryGroup.toLin'_mul`：∀ {n : Type u} [inst : DecidableEq n] [i
nst_1 : Fintype n] {α : Type v} [inst_2 : CommRing α] [inst_3 : StarRing α]   (A
 B : ↥(Matrix.unitar…
-/
theorem toGL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B := Units.ext <| by
  simp only [coe_toGL, toLin'_mul]
  rfl

/-- `Matrix.unitaryGroup.embeddingGL` is the embedding from `Matrix.unitaryGroup n α` to
`LinearMap.GeneralLinearGroup n α`. -/
/-
**Matrix.UnitaryGroup.embeddingGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGroup
`。
形式化陈述：embeddingGL : unitaryGroup n α ->* GeneralLinearGroup α (n -> α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.UnitaryGroup.toGL_one`：toGL_one : toGL (1 : unitaryGroup n α) = 1
· 使用定理 `Matrix.UnitaryGroup.toGL_mul`：toGL_mul (A B : unitaryGroup n α) : toGL (
A * B) = toGL A * toGL B

--- 原说明 ---
`Matrix.unitaryGroup.embeddingGL` is the embedding from `Matrix.unitaryGroup n α
` to
`LinearMap.GeneralLinearGroup n α`.
-/
def embeddingGL : unitaryGroup n α →* GeneralLinearGroup α (n → α) :=
  ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩
/-
**Matrix.UnitaryGroup._root_.Matrix.transpose_mem_unitaryGroup_iff** 是 Mathlib 中
的一个定理，位于命名空间 `Matrix.UnitaryGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.transpose_mem_unitaryGroup_iff {U : Matrix n n α} :
    Uᵀ ∈ unitaryGroup n α ↔ U ∈ unitaryGroup n α := by
  conv_rhs => rw [mem_unitaryGroup_iff']
  rw [mem_unitaryGroup_iff, show star Uᵀ = (star U)ᵀ by rfl, ← transpose_mul, ← transpose_inj]
  simp
/-
**Matrix.UnitaryGroup._root_.Matrix.map_star_mem_unitaryGroup_iff** 是 Mathlib 中的
一个定理，位于命名空间 `Matrix.UnitaryGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.map_star_mem_unitaryGroup_iff {U : Matrix n n α} :
    U.map star ∈ unitaryGroup n α ↔ U ∈ unitaryGroup n α := by
  simp [← conjTranspose_transpose, transpose_mem_unitaryGroup_iff, ← star_eq_conjTranspose]

/-- The transpose of a unitary matrix as a unitary matrix. -/
/-
**Matrix.UnitaryGroup.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：{n : Type u} →   [inst : DecidableEq n] →     [inst_1 : Fintype n] →      
 {α : Type v} →         [inst_2 : CommRing α] → [inst_3 : StarRing α] → ↥(Matrix
.unitaryGroup n α) → ↥(Matrix.unitaryGroup n α)
参数：Matrix.unitaryGroup n α；Matrix.unitaryGroup n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of a unitary matrix as a unitary matrix.
-/
@[simps] def transpose (U : unitaryGroup n α) : unitaryGroup n α :=
  ⟨Uᵀ, transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩

/-- The `Matrix.map star` of a unitary matrix (i.e., taking the `star` of
each element in the matrix) as a unitary matrix. -/
/-
**Matrix.UnitaryGroup.map_star** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.UnitaryGroup`。
形式化陈述：{n : Type u} →   [inst : DecidableEq n] →     [inst_1 : Fintype n] →      
 {α : Type v} →         [inst_2 : CommRing α] → [inst_3 : StarRing α] → ↥(Matrix
.unitaryGroup n α) → ↥(Matrix.unitaryGroup n α)
参数：Matrix.unitaryGroup n α；Matrix.unitaryGroup n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Matrix.map star` of a unitary matrix (i.e., taking the `star` of
each element in the matrix) as a unitary matrix.
-/
@[simps] def map_star (U : unitaryGroup n α) : unitaryGroup n α :=
  ⟨(U : Matrix n n α).map star, map_star_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩
/-
**Matrix.UnitaryGroup.map_star_inv_eq_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.UnitaryGroup`。
形式化陈述：map_star_inv_eq_transpose (U : unitaryGroup n α) : (map_star U)⁻¹ = Unitar
yGroup.transpose U
参数：U : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.UnitaryGroup.ext`：ext (A B : unitaryGroup n α) : (forall i j, A i
 j = B i j) -> A = B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.UnitaryGroup.map_star_coe`：∀ {n : Type u} [inst : DecidableEq n] 
[inst_1 : Fintype n] {α : Type v} [inst_2 : CommRing α] [inst_3 : StarRing α]   
(U : ↥(Matrix.unitaryG…
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.UnitaryGroup.transpose_coe`：∀ {n : Type u} [inst : DecidableEq n]
 [inst_1 : Fintype n] {α : Type v} [inst_2 : CommRing α] [inst_3 : StarRing α]  
 (U : ↥(Matrix.unitaryG…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_star_inv_eq_transpose (U : unitaryGroup n α) :
    (map_star U)⁻¹ = UnitaryGroup.transpose U := by ext; simp
/-
**Matrix.UnitaryGroup.transpose_inv_eq_map_star** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.UnitaryGroup`。
形式化陈述：transpose_inv_eq_map_star (U : unitaryGroup n α) : (UnitaryGroup.transpose
 U)⁻¹ = map_star U
参数：U : unitaryGroup n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_inv_eq_map_star (U : unitaryGroup n α) :
    (UnitaryGroup.transpose U)⁻¹ = map_star U := by
  simp [← map_star_inv_eq_transpose]

end UnitaryGroup

section specialUnitaryGroup

variable (n) (α)

/-- `Matrix.specialUnitaryGroup` is the group of unitary `n` by `n` matrices where the determinant
is 1. (This definition is only correct if 2 is invertible.) -/
/-
**Matrix.specialUnitaryGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：specialUnitaryGroup : Submonoid (Matrix n n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.specialUnitaryGroup` is the group of unitary `n` by `n` matrices where t
he determinant
is 1. (This definition is only correct if 2 is invertible.)
-/
def specialUnitaryGroup : Submonoid (Matrix n n α) := unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

variable {n} {α}
/-
**Matrix.specialUnitaryGroup_le_unitaryGroup** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：specialUnitaryGroup_le_unitaryGroup : specialUnitaryGroup n α <= unitaryGr
oup n α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem specialUnitaryGroup_le_unitaryGroup : specialUnitaryGroup n α ≤ unitaryGroup n α :=
  inf_le_left
/-
**Matrix.mem_specialUnitaryGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_specialUnitaryGroup_iff : A in specialUnitaryGroup n α ↔ A in unitaryG
roup n α ∧ A.det = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_specialUnitaryGroup_iff :
    A ∈ specialUnitaryGroup n α ↔ A ∈ unitaryGroup n α ∧ A.det = 1 :=
  Iff.rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (specialUnitaryGroup n α) where
  star A := ⟨star A, by simpa using A.prop.1, by have := A.prop.2; simp_all [star_eq_conjTranspose]⟩
  star_mul A B := Subtype.ext <| star_mul A.1 B.1
  star_involutive A := Subtype.ext <| star_involutive A.1

@[simp, norm_cast]
/-
**Matrix.specialUnitaryGroup.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.specialU
nitaryGroup`。
形式化陈述：∀ {n : Type u} [inst : DecidableEq n] [inst_1 : Fintype n] {α : Type v} [i
nst_2 : CommRing α] [inst_3 : StarRing α]   (A : ↥(Matrix.specialUnitaryGroup n 
α)), ↑(star A) = star ↑A
参数：A : ↥(Matrix.specialUnitaryGroup n α)；star A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem specialUnitaryGroup.coe_star (A : specialUnitaryGroup n α) : (star A).1 = star A.1 := rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (specialUnitaryGroup n α) where inv := star
/-
**Matrix.star_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：star_eq_inv (A : specialUnitaryGroup n α) : star A = A⁻¹
参数：A : specialUnitaryGroup n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv (A : specialUnitaryGroup n α) : star A = A⁻¹ :=
  rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (specialUnitaryGroup n α) where
  inv_mul_cancel A := Subtype.ext A.prop.1.1

end specialUnitaryGroup

section OrthogonalGroup

variable (n) (R : Type v) [CommRing R]

-- TODO: will lemmas about `Matrix.orthogonalGroup` work without making
-- `starRingOfComm` a local instance? E.g., can we talk about unitary group and orthogonal group
-- at the same time?
attribute [local instance] starRingOfComm

/-- `Matrix.orthogonalGroup n` is the group of `n` by `n` matrices where the transpose is the
inverse. -/
/-
**Matrix.orthogonalGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：orthogonalGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.orthogonalGroup n` is the group of `n` by `n` matrices where the transpo
se is the
inverse.
-/
abbrev orthogonalGroup := unitaryGroup n R
/-
**Matrix.mem_orthogonalGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_orthogonalGroup_iff {A : Matrix n n R} : A in Matrix.orthogonalGroup n
 R ↔ A * Aᵀ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mem_unitaryGroup_iff`：mem_unitaryGroup_iff : A in Matrix.unitaryG
roup n α ↔ A * star A = 1
-/
theorem mem_orthogonalGroup_iff {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ A * Aᵀ = 1 :=
  mem_unitaryGroup_iff
/-
**Matrix.mem_orthogonalGroup_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_orthogonalGroup_iff' {A : Matrix n n R} : A in Matrix.orthogonalGroup 
n R ↔ Aᵀ * A = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mem_unitaryGroup_iff'`：mem_unitaryGroup_iff' : A in Matrix.unitar
yGroup n α ↔ star A * A = 1
-/
theorem mem_orthogonalGroup_iff' {A : Matrix n n R} :
    A ∈ Matrix.orthogonalGroup n R ↔ Aᵀ * A = 1 :=
  mem_unitaryGroup_iff'

end OrthogonalGroup

section specialOrthogonalGroup

variable (n) (R : Type v) [CommRing R]

attribute [local instance] starRingOfComm

/-- `Matrix.specialOrthogonalGroup n` is the group of orthogonal `n` by `n` where the determinant
is one. (This definition is only correct if 2 is invertible.) -/
/-
**Matrix.specialOrthogonalGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：specialOrthogonalGroup : Submonoid (Matrix n n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.specialOrthogonalGroup n` is the group of orthogonal `n` by `n` where th
e determinant
is one. (This definition is only correct if 2 is invertible.)
-/
abbrev specialOrthogonalGroup : Submonoid (Matrix n n R) := specialUnitaryGroup n R

variable {n} {R} {A : Matrix n n R}

-- the group and star structure is automatic from `specialUnitaryGroup`
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Group (specialOrthogonalGroup n R) := inferInstance
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : StarMul (specialOrthogonalGroup n R) := inferInstance
/-
**Matrix.mem_specialOrthogonalGroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mem_specialOrthogonalGroup_iff : A in specialOrthogonalGroup n R ↔ A in or
thogonalGroup n R ∧ A.det = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_specialOrthogonalGroup_iff :
    A ∈ specialOrthogonalGroup n R ↔ A ∈ orthogonalGroup n R ∧ A.det = 1 :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Matrix.of_mem_specialOrthogonalGroup_fin_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix`。
形式化陈述：of_mem_specialOrthogonalGroup_fin_two_iff {a b c d : R} : !![a, b; c, d] i
n Matrix.specialOrthogonalGroup (Fin 2) R ↔ a = d ∧ b = -c ∧ a ^ 2 + b ^ 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.cons_transpose`：cons_transpose (v : n' -> α) (A : Matrix (Fin m) 
n' α) : (of (vecCons v A))ᵀ = of fun i => vecCons (v i) (Aᵀ i)
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.cons_vecMul`：cons_vecMul (x : α) (v : Fin n -> α) (B : Fin n.succ
 -> o' -> α) : vecCons x v ᵥ* of B = x • vecHead B + v ᵥ* of (vecTail B)
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Matrix.add_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma of_mem_specialOrthogonalGroup_fin_two_iff {a b c d : R} :
    !![a, b; c, d] ∈ Matrix.specialOrthogonalGroup (Fin 2) R ↔
      a = d ∧ b = -c ∧ a ^ 2 + b ^ 2 = 1 := by
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  grind
/-
**Matrix.mem_specialOrthogonalGroup_fin_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x`。
形式化陈述：mem_specialOrthogonalGroup_fin_two_iff {M : Matrix (Fin 2) (Fin 2) R} : M 
in Matrix.specialOrthogonalGroup (Fin 2) R ↔ M 0 0 = M 1 1 ∧ M 0 1 = - M 1 0 ∧ M
 0 0 ^ 2 + M 0 1 ^ 2 = 1
参数：Fin 2；Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.etaExpand_eq`：etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) :
 etaExpand A = A
· 使用引理 `Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`：of_mem_specialOrthogon
alGroup_fin_two_iff {a b c d : R} : !![a, b; c, d] in Matrix.specialOrthogonalGr
oup (Fin 2) R ↔ a = d ∧ b = -c ∧ a ^ 2…
-/
lemma mem_specialOrthogonalGroup_fin_two_iff {M : Matrix (Fin 2) (Fin 2) R} :
    M ∈ Matrix.specialOrthogonalGroup (Fin 2) R ↔
      M 0 0 = M 1 1 ∧ M 0 1 = - M 1 0 ∧ M 0 0 ^ 2 + M 0 1 ^ 2 = 1 := by
  rw [← M.etaExpand_eq]
  exact of_mem_specialOrthogonalGroup_fin_two_iff

end specialOrthogonalGroup

end Matrix

